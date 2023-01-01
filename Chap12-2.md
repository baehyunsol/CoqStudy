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