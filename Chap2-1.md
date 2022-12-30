| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proofs by Induction

```haskell, line_num
Theorem add_0_r_firsttry : forall n: nat,
  n + 0 = n.
```

위와 같은 theorem을 증명하려면 어떻게 해야할까요? 덧셈의 왼쪽 인자가 상수가 아니라서 `simpl`이나 `reflexivity`등의 tactic이 통하지 않습니다. `destruct`를 이용하면 `n`을 `S n'`으로 바꿀 수 있지만 여전히 부족합니다.

이럴 때 필요한 것이 귀납법입니다. 고등학교 때 수학시간에 수학적 귀납법을 배운 기억이 나시나요? 바로 그 귀납법입니다.

[[anchor, id = keyword induction]][[/anchor]]

```haskell, line_num
Theorem add_0_r : forall n: nat, n + 0 = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - (*{- n = 0 -}*)
    reflexivity.
  - (*{- n = S n' -}*)
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.
```

귀납법에는 `induction` 키워드를 사용합니다. `induction`은 `destruct`와 비슷하게, 상황을 `n = 0`과 `n = S n'`으로 나눕니다. 하지만 귀납법을 쓰기 위해서는 한가지가 더 필요합니다. `n = S n'`와 `n' + 0 = n'`이 둘 다 있어야지만 귀납법이 사용가능한데요, 대괄호 안의 `IHn'`[^ihn]이 바로 `n' + 0 = n'`입니다.

즉, 첫번째 bullet에서는 `n = 0`일 때 `n + 0 = n`을 증명하고, 두번째 bullet에서는 `n = S n'`이고 `n' + 0 = n'`일 때 `n + 0 = n`을 증명합니다.

두번째 bullet을 좀 더 자세히 들여다보면 `simpl`을 이용해서 `S n' + 0 = S n'`을 `S(n' + 0) = S n'`으로 바꾸고, `rewrite`를 이용해서 `n' + 0`을 `n'`으로 바꿉니다. 그럼 남은 식은 `S n' = S n'`이 되죠? 증명이 끝났습니다.

[^ihn]: 책에서는 *Induction Hypothesis for n'*의 줄임말로 IHn'이라고 명명했습니다.

## Examples

귀납법은 아주 중요합니다. 귀납법을 좀 더 잘 이해하기 위해서 예시들을 추가했습니다. 몇몇 예시는 책의 풀이이고 나머지는 제가 푼 것들입니다. Coq가 어떻게 동작하는지 잘 이해하기 위해서는 아래의 예시들을 CoqIDE 혹은 다른 Coq 구현체에 넣어서 직접 실행해보시는 걸 추천드립니다. 각 tactic을 실행할 때마다 goal과 context를 확인함으로써 Coq의 작동원리를 더 자세하게 알 수 있습니다.

### mul_0_r

```haskell, line_num
Theorem mul_0_r : forall n: nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - (*{- n = 0 -}*)
    reflexivity.
  - (*{- n = S n' -}*)
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.
```

### plus_n_Sm

```haskell, line_num
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - (*{- n = 0 -}*)
    rewrite -> add_0.
    rewrite -> add_0.
    reflexivity.
  - (*{- n = S n' -}*)
    simpl.
    rewrite IHn'.
    reflexivity.
  Qed.
```

참고로 `add_0`은 `0 + n = n`입니다.

6번 줄에서 `S (0 + m) = 0 + S m`이 나오는데, 거기서 `rewrite -> add_0`를 2번 하면 `S m = S m`이 됩니다. 11번 줄에서 `simpl`을 하면 `S (S (n' + m)) = S (n' + S m)`이 되는데, `IHn': S (n' + m) = n' + S m`이므로, `rewrite IHn'`을 하면 식이 `S (n' + S m) = S (n' + S m)`로 깔끔해집니다.

### add_comm

[[anchor, id=theorem add comm]][[/anchor]]

이제 교환법칙을 증명해보겠습니다.

```haskell, line_num
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [ |n' IHn'].
  - (*{- n = 0 -}*)
    rewrite -> add_0.
    rewrite -> add_0_r.
    reflexivity.
  - (*{- n = S n' -}*)
    simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
  Qed.
```

참고로 `add_0_r`은 `n + 0 = n`입니다.

6번 줄의 `0 + m = m + 0`은 `add_0`와 `add_0_r`만으로 깔끔하게 `m = m` 꼴로 만들 수 있습니다. 11번 줄에서 `simpl`을 하면 `S (n' + m) = m + S n'`이 되는데, `IHn': n' + m = m + n'`이므로, `rewrite IHn'`으로 `n'`과 `m`의 순서를 바꾸고 아까 증명한 `plus_n_Sm`을 이용하면 깔끔하게 증명할 수 있습니다.

### add_assoc

```haskell, line_num
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  rewrite add_comm.
  induction n as [ |n' IHn'].
  - (*{- n = 0 -}*)
    rewrite add_0.
    rewrite add_0_r.
    reflexivity.
  - (*{- n = S n' -}*)
    rewrite <- plus_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.
```

아까 증명한 `add_comm`을 이용하면 식이 `m + p + n = n + m + p`의 형태로 바뀝니다. `m + p`를 하나의 항으로 생각하면 `add_comm`과 동일한 형태의 식으로 생각할 수 있습니다. 그래서 아까와 비슷하게 증명이 가능합니다.

### eqb_refl

```haskell, line_num
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [ |n' IHn'].
  - (*{- n = 0 -}*)
    simpl.
    reflexivity.
  - (*{- n = S n' -}*)
    rewrite <- IHn'.
    simpl.
    reflexivity.
  Qed.
```

위의 증명에서 `simpl`을 전부 제거해도 증명이 됩니다. `simpl`하고 `reflexivity`가 정확히 어떻게 동작하는지 잘 모르겠네요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap1-3. Proofs](Chap1-3.html)

[[/left]]

[[right]]

[Chap2-2. Proofs within proofs](Chap2-2.html) >>

[[/right]]