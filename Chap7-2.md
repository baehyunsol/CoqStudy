| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Using Evidence in Proofs

`Inductive`를 이용해서 `ev`를 정의하고 시작하겠습니다.

[[anchor, id = definition ev]][[/anchor]]

```haskell, line_num
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

`ev`는 주어진 자연수가 짝수인지 아닌지 `Prop`으로 알려주는 `Inductive`입니다. 0은 짝수고, `n + 2`가 짝수면 `n`도 짝수라고 재귀적으로 정의했습니다.

저기서 `ev_0`와 `ev_SS`는 evidence라고 부르고, 다른 증명을 할 때 이미 증명된 명제처럼 사용할 수 있습니다. 이전 챕터에서 `Inductive`를 이용한 증명을 조금 살펴 보았으니 이번에는 제대로 살펴보겠습니다.

```haskell, line_num
Theorem ev_4 : ev 4.

(*{- Proof 1 -}*)
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
  Qed.

(*{- Proof 2 -}*)
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
  Qed.
```

4가 짝수임을 2가지 방식으로 증명했습니다. 첫번째 증명에선 `ev_SS`를 그 자체로 사용했고, 두번째에선 `ev_SS`에게 인수를 직접 제공했습니다.

```haskell, line_num
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n.
  simpl.
  intros Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
  Qed.
```

이번에는 context에 `Hn: ev n`이 들어있는 경우를 증명해보았습니다. `apply`를 이용해서 goal과 context가 동일한 모양이 되도록 한 후에 `apply Hn`을 했습니다.

## Inversion on Evidence

만약 `E`가 `ev n`의 evidence라면 `E`는 반드시 `ev_0` 혹은 `ev_SS` 중 하나입니다. 이는 `Induction`이라는 이름에서도 잘 알 수 있죠. 이 사실을 inversion이라고 부르며 증명에 다양한 방법으로 활용할 수 있습니다. Inversion을 활용한 증명을 보기 전에 inversion 자체를 먼저 증명해보겠습니다.

```haskell, line_num
Theorem ev_inversion : forall (n : nat),
    ev n ->
      (n = 0)
      \/
      (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (*{- E = ev_0 : ev 0 -}*)
    left.
    reflexivity.
  - (*{- E = ev_SS n' E' : ev (S (S n')) -}*)
    right.
    exists n'.
    split.
    reflexivity.
    apply E'.
  Qed.
```

`ev`에 대해서 inversion을 풀어 쓴 증명입니다. 한국말로 풀어쓰면 ~_n이 짝수면 n = 0이거나 n + 2는 짝수다_~ 정도가 됩니다. 증명에선 `destruct`를 이용해서 `ev n`를 `ev_0`과 `ev_SS`로 쪼갰습니다. 주석을 보면 `E`의 모습이 복잡해보일 수 있지만 자세히 보면 [위](#definitionev)에서 한 `ev`의 정의와 같은 모양입니다.

방금 만든 `ev_inversion`을 이용해서 다른 걸 증명해보겠습니다. 아래를 봅시다.

```haskell, line_num
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0 | H1].
  - (*{- H0: S (S n) = 0 -}*)
    discriminate H0.
  - (*{- H1: exists n' : nat, S (S n) = S (S n') /\ ev n' -}*)
    destruct H1 as [n' [Hnm Hev]].
    injection Hnm as Heq.
    rewrite Heq.
    apply Hev.
  Qed.
```

4번 줄의 `ev_inversion`은 `H: ev (S (S n))`을 2개로 쪼갭니다. 첫번째 경우는 `H`가 `ev 0`인 경우로, `S (S n)`은 절대 0이 될 수 없으므로 `discriminate` tactic으로 간단하게 처리했습니다. 두번째 경우도 `ev_SS`의 정의를 잘 지지고볶아서 쉽게 결론에 도달할 수 있습니다.

방금의 증명은 `inversion` tactic을 이용하면 더 짧게 만들 수 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [ | n' E' Heq].
  apply E'.
  Qed.
```

[[anchor, id = keyword inversion]][[/anchor]]

4번 줄에서 `inversion`을 하면 Coq는 `E`를 `ev_0`인 경우와 `ev_SS`인 경우로 나눕니다. 또한, `E`가 `ev_0`일 수 없다는 건 자명하므로 Coq가 알아서 그 경우는 제외해버리고 `ev_SS`만 남겨버립니다. 즉, 방금 전에는 `discriminate`를 이용해서 일일이 처리해야했던 경우들을 `inversion` tactic이 알아서 처리해줍니다.

`inversion` tactic이 알아서 `discriminate`해주는 더 극단적인 경우를 보겠습니다.

```haskell, line_num
Theorem not_ev_1 : ~ ev 1.
Proof.
  intros H.
  inversion H.
  Qed.
```

1은 0도 될 수 없고 `S (S n)`도 될 수 없습니다. 따라서 `ev 1`에 `inversion`을 쓰면 모든 경우가 알아서 `discriminate`되고 증명이 끝납니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap7-1. Inductively defined Propositions](Chap7-1.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]