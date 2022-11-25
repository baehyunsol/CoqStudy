| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# More tactics

## Tactics on Hypothesis

[[anchor, id = keyword in]][[/anchor]]

Context 안에 있는 가정들을 대상으로 tactic을 사용하려면 어떻게 해야할까요? Context 안에 `H: m = n`가 있는데 저걸 `H: n = m`으로 바꾸려면 어떻게 해야할까요? `in`이라는 키워드를 쓰면 됩니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem ridiculous : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.
  apply EQ in H.
  symmetry in H.
  apply H.
  Qed.
```

7번 줄의 `symmetry in H`는 `H: m = n`을 `H: n = m`으로 바꿉니다.

## Varying the Induction Hypothesis

```haskell, line_num
Theorem double_injective : forall n m,
  double n = double m -> n = m.
```

위의 식을 증명해보겠습니다. 얼핏 보기엔 `intros n m`을 하고 `n`과 `m`에 대해 각각 `induction`을 쓰면 될 것 같지만 그렇지 않습니다. `n`과 `m` 중 `forall`이 하나라도 있어야하는데 그렇지 않아서 의미가 없는 귀납법이 나옵니다. 그걸 해결하기 위해선 둘 중 하나만 `intros`를 한 뒤, 따로 귀납법을 써야합니다. 아래처럼 말이죠.

```haskell, line_num
Proof.
  intros n m.
  generalize dependent n.
  induction m as [ | m' IHm'].
  - (*{- m = 0 -}*)
    intros n eq.
    induction n as [ | n' IHn'].
    + (*{- n = 0 -}*)
      reflexivity.
    + (*{- n = S n' -}*)
      discriminate eq.
  - (*{- m = S m' -}*)
    intros n eq.
    induction n as [ | n' IHn'].
    + (*{- n = 0 -}*)
      discriminate eq.
    + (*{- n = S n' -}*)
      injection eq.
      intros H.
      apply IHm' in H.
      rewrite H.
      reflexivity.
  Qed.
```

[[anchor, id = keyword generalize]][[/anchor]]

`generalize dependent n`은 context에 있는 `n`을 다시 `forall n`으로 바꿔줍니다. 그 다음 `induction m`을 한 뒤 그 안에서 각각 `intros n`을 했습니다. 이러면 증명이 성공적으로 끝납니다.

그럼 애초에 `intros n`만 한 다음에 `n`을 가지고 귀납법을 쓰면 되는 거 아니냐고 생각하시는 분들도 계실 겁니다. 사실 저도 그렇게 생각합니다. 이 예시에서는 `generalize dependent`라는 tactic을 소개하기 위해서 굳이 저렇게 한 거 같습니다.

## unfold

[[anchor, id = keyword unfold]][[/anchor]]

간단한 예시로 시작하겠습니다.

```haskell, line_num
Definition square (n : nat) := n * n.

Theorem square_mult : forall (n m : nat), square (n * m) = square n * square m.
```

눈으로 보기에는 당연해 보이는 위 예제를 Coq로 증명하려면 생각보다 쉽지 않습니다. `simpl`을 쓰더라도 `square` 함수의 내부를 건드리지 않기 때문에 아무 일도 일어나지 않습니다. 이럴 때 사용하는게 `unfold`입니다. 함수 inlining이라고 생각하면 비슷합니다.[^jgu]

`unfold square`는 `square n`을 `n * n`으로 바꿔줍니다. 즉, 위의 식이 `n * m * (n * m) = n * n * (m * m)`가 됩니다. 이러면 적용할 수 있는 tactic이 아주 많아집니다.

물론 `simpl`이나 `reflexivity`, `apply` 등도 어느정도의 unfolding을 합니다. 하지만 적용이 될 때도 있고 안 될 때도 있습니다. 그에반해 `unfold`는 모든 상황에서 단순무식하게 식을 unfolding합니다.

[^jgu]: 제 개인적인 의견입니다.

## destruct on compound expressions

[[anchor, id = keyword destruct]][[/anchor]]

[이전](Chap1-3.html#keyworddestruct)에 봤던 `destruct`는 특정 값을 쪼갰습니다. 예를 들어 어떤 boolean `b`를 `destruct b`하면 `b`가 `true`인 경우와 `false`인 경우로 나눠집니다. 값을 쪼개는게 아니라 식을 쪼갤 수도 있을까요? 아래의 예시를 보겠습니다.

```haskell, line_num
Definition compound_false (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem compound_false_false : forall (n : nat), compound_false n = false.
```

위에서 정의한 `compound_false`는 항상 `false`입니다. 사람 눈으로 보기엔 그게 자명하지만 Coq가 봐도 그럴까요? 아쉽게도 그렇지 않습니다. Coq에게는 `destruct`를 이용해서 `n`이 3, 5, 나머지인 경우로 나눠줘야합니다. 아래처럼 말이죠.

```haskell, line_num
Proof.
  intros n.
  unfold compound_false.
  destruct (n =? 3).
  - (*{- n =? 3 = true -}*)
    reflexivity.
  - (*{- n =? 3 = false -}*)
    destruct (n =? 5).
    + (*{- n =? 5 = true -}*)
      reflexivity.
    + (*{- n =? 5 = false -}*)
      reflexivity.
  Qed.
```

위의 식은 `n`에다가 3을 대입하는게 아니고 `n =? 3`에다가 `true`를 대입합니다. 그러면 if문이 통째로 날아가서 `false`와 `if n =? 5 then ...`으로 쪼개집니다. 그렇게되면 저희가 증명하려는 식도 `false = false`의 형태가 되어서 `reflexivity`만으로 증명이 가능해집니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap5-2. Injective and Disjoint](Chap5-2.html)

[[/left]]

[[right]]

[Chap6-1. Conjunction and Disjunction](Chap6-1.html) >>

[[/right]]