| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Coq Automation

이번 장에서는 Coq의 증명 노가다를 도와줄 tactic들을 소개합니다. 이번에 소개할 tactic들은 tactic에 쓰는 tactic입니다. 책의 표현을 빌리자면 higher-order tactic이죠.

## try

[[anchor, id = keyword try]][[/anchor]]

원래 Coq에서 tactic이 실패를 하면 (ex. 똑같지 않은데 `reflexivity`를 쓰면) 증명 전체가 실패합니다. 하지만 `try` 뒤에 있는 tactic은 실패를 하더라도 아무 영향이 없습니다. 즉,

- `try` 뒤의 tactic이 성공하면
  - 그 tactic이 context에 반영됩니다.
- `try`뒤의 tactic이 실패하면
  - 그 tactic을 통째로 무시하고 다음으로 넘어갑니다.

얼핏 보면 저런게 왜 필요한가 싶습니다. 실패하는 tactic은 애초에 안 쓸텐데 말이죠... 손으로 증명을 할 때는 그렇습니다. 하지만 증명 자체를 자동화하는 경우에는 다릅니다. 증명을 위한 스크립트를 쓰면 실패하는 tactic이 섞여 있을 수도 있습니다. 이따가 예시와 함께 설명하겠습니다.

## ; tactical

[[anchor, id = keyword semi colon]][[/anchor]]

`destruct`나 `induction` 등등을 사용하면 여러 subgoal이 생깁니다. subgoal의 개수가 많은데 각 subgoal에 동일한 tactic을 적용하고 싶으면 어떻게 할까요? 아래의 예시를 보겠습니다.

```haskell, line_num
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    - (*{- n = 0 -}*)
      simpl.
      reflexivity.
    - (*{- n = S n' -}*)
      simpl.
      reflexivity.
Qed.
```

`simpl`과 `reflexivity`가 2번씩 반복되는게 거슬리죠? `;`를 이용해서 간략하게 해보겠습니다. 아래를 봅시다.

```haskell, line_num
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n;
  simpl;
  reflexivity.
  Qed.
```

`destruct` 뒤에 `;`가 붙어있기 때문에 그 뒤에 오는 `simpl`이 두 subgoal에 각각 적용되고, `simpl` 뒤에 `;`가 있기 때문에 `reflexivity`도 2번 적용됩니다.

```haskell, line_num
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
  try (
    simpl;
    rewrite IHa1;
    rewrite IHa2;
    reflexivity
  ).
  - (*{- ANum -}*)
    reflexivity.
  - (*{- APlus -}*)
    destruct a1 eqn:Ea1;
    try (
      simpl;
      simpl in IHa1;
      rewrite IHa1;
      rewrite IHa2;
      reflexivity
    ).
    + (*{- a1 = ANum n -}*)
      destruct n eqn:En;
      simpl;
      rewrite IHa2;
      reflexivity.
  Qed.
```

[이전 단원](Chap12-1.html#optimizations)에서 봤던 `optimize_0plus`의 증명을 `try`와 `;`를 이용해서 해봤습니다. 6번 줄의 `try`가 `AMinus`와 `AMult`의 경우를 자동으로 처리해 주고 나머지 경우들은 수동으로 처리했습니다.

## repeat

[[anchor, id = keyword repeat]][[/anchor]]

`repeat`은 뒤에 오는 tactic을 계속 반복해서 실행합니다. 실행하다가 tactic이 아무런 효과도 없거나 실패하면 반복을 멈추고 넘어갑니다.

```haskell, line_num
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.
```

위의 예시를 뜯어보겠습니다. `In 10 [1;2;3;...]`을 `unfold` 해보면 `1 = 10 \/ 2 = 10 \/ 3 = 10 \/ ... \/ 10 = 10`이 나옵니다. 저 상태에서 `left`를 하면 `1 = 10`만 남겠죠? 거기에 `reflexivity`를 하면 당연히 실패합니다. 그럼 다음으로 넘어갑니다. 그런 식으로 계속 `repeat`을 해서 `10 = 10`까지 간 뒤, 거기에 `reflexivity`를 해서 증명을 끝냅니다.

## lia

[[anchor, id = keyword lia]][[/anchor]]

`lia`는 아주 유용한 tactic입니다. 먼저 `From Coq Require Import Lia.`를 이용해서 `lia`를 가져옵시다. `lia`의 기능은 아래와 같습니다.

> 상수, 덧셈 (`+`, `S`), 뺄셈 (`-`, `pred`), 상수 곱셈, 등호 (`=`, `!=`), 대소 (`<=`, `>`), 논리 연산자 (`\/`, `/\`, `~`, `->`)로만 이뤄진 정리를 한번에 풉니다.

정리 자체가 거짓이거나 `lia`가 다룰 수 없는 기호가 있을 경우 `lia`는 실패합니다. 예시를 보겠습니다.

```haskell, line_num
Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros.
  lia.
Qed.
```

간단하죠?

## subst

[[anchor, id = keyword subst]][[/anchor]]

`subst`도 아주 유용한 tactic입니다. Coq으로 증명을 하다보면 context에 불필요한 이름들이 많이 들어가서 더러워집니다. 예를 들어서 `c1 = c`,  `c2 = c1` 등등의 의미없는 등식들이 context에 가득 차 있으면 증명을 따라가기 버겁습니다. 저런 의미없는 등식들을 날려주는게 `subst`입니다. 예를 들어서 context에 `x = e`나 `e = x`가 있을 때 `subst x`를 하면 증명의 모든 부분에 있는 `x`를 전부 찾아서 `e`로 바꿔준 후, context의 `x = e`를 날려버립니다.

더 간편하게 쓰려면 `subst`라고만 해도 됩니다. 그러면 교체가 가능한 모든 이름들을 교체한 후 context에서 필요없는 등식들을 날려버립니다. 아래의 예시를 보겠습니다.

```
1 goal
c : com
st, st' : state
H : st =[ skip; c ]=> st'
c1, c2 : com
st0, st'0, st'' : state
H2 : st =[ skip ]=> st'0
H5 : st'0 =[ c ]=> st'
H0 : c1 = <{ skip }>
H1 : c2 = c
H3 : st0 = st
H4 : st'' = st'
______________________________________(1/1)
st =[ c ]=> st'
```

위는 진행 중인 어떤 증명의 context와 goal입니다. 한 눈에 봐도 더럽죠? 저 상태에서 `subst`를 하면 아래와 같이 변합니다.

```
1 goal
c : com
st, st' : state
H : st =[ skip; c ]=> st'
st'0 : state
H2 : st =[ skip ]=> st'0
H5 : st'0 =[ c ]=> st'
______________________________________(1/1)
st =[ c ]=> st'
```

`st0`와 `st''`, `c1`, `c2`는 날려버려도 상관이 없으니 날려버렸습니다. 이렇게 하면 필요한 이름들만 남게 돼서 훨씬 보기 좋습니다.

## assumption

[[anchor, id = keyword assumption]][[/anchor]]

아주 간단합니다. context에 `H: a = b`가 있고 goal도 `a = b`이다? 둘이 모양이 완전 동일하죠? 그럼 그 즉시 증명을 끝냅니다.

즉, context를 뒤져서 goal과 동일하게 생긴 가정을 찾고, 그런 가정이 있으면 즉시 증명을 끝냅니다. Coq이 자동으로 `apply`를 해준다고 생각해도 됩니다.

## auto

[[anchor, id = keyword auto]][[/anchor]]

아주 강력한 tactic입니다. 이름부터 세 보이죠? 아래의 두 증명을 봅시다.

```haskell, line_num
Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  apply H1.
  assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.
```

위의 두 증명은 동일합니다. `intros`와 `apply`로만 이뤄진 증명은, `auto`로 즉시 끝낼 수 있습니다. 만약 `auto`가 적용 가능할 경우 증명이 즉시 끝나고 적용 불가능할 경우 증명에 손을 대지 않기 때문에 아무때나 써도 안전합니다.

`auto`가 내부적으로 무슨 일을 하는지 궁금할 경우 `auto` 대신 `debug auto` 혹은 `info_auto` 라고[^sp] 입력하면 됩니다.

실제로 실행하기 전까지 `auto`는 증명의 길이가 얼마나 길지 예측할 수 없습니다. 그렇다고 증명이 끝날 때까지 계속 탐색을 하면 `auto`가 무한루프에 빠질 수도 있습니다. 그래서 `auto`는 증명의 깊이가 일정 수준 이상 되면 (기본값은 5입니다) 증명을 포기합니다. 깊이를 임의로 주고 싶으면 `auto 6`과 같은 방식으로 `auto` 뒤에 숫자를 붙여서 주면 됩니다.

[^sp]: 전자는 띄어쓰기가 있고 후자는 `_`가 있습니다. 주의하세요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 12-1. Arithmetic and Boolean Expressions](Chap12-1.html)

[[/left]]

[[right]]

[Chapter 12-3. States and Commands](Chap12-3.html) >>

[[/right]]