| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Using Evidence in Proofs

`Inductive`를 이용해서 `ev`를 정의하고 시작하겠습니다.

[[anchor, id = definition ev]][[/anchor]]

```coq, line_num
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

`ev`는 주어진 자연수가 짝수인지 아닌지 `Prop`으로 알려주는 `Inductive`입니다. 0은 짝수고, `n + 2`가 짝수면 `n`도 짝수라고 재귀적으로 정의했습니다.

[[anchor, id = ref evidence]][[/anchor]]

저기서 `ev_0`와 `ev_SS`는 증거[^ev]라고 부르고, 다른 증명을 할 때 이미 증명된 명제처럼 사용할 수 있습니다. 이전 챕터에서 `Inductive`를 이용한 증명을 조금 살펴 보았으니 이번에는 제대로 살펴보겠습니다.

[^ev]: 책에서는 *evidence*라는 용어를 사용합니다. 앞으로 이 문서에선 전부 *증거*라고 번역하겠습니다.

```coq, line_num
Theorem ev_4 : ev 4.

(* Proof 1 *)
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
  Qed.

(* Proof 2 *)
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
  Qed.
```

4가 짝수임을 2가지 방식으로 증명했습니다. 첫번째 증명에선 `ev_SS`를 그 자체로 사용했고, 두번째에선 `ev_SS`에게 인수를 직접 제공했습니다.

```coq, line_num
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

만약 `E`가 `ev n`의 증거라면 `E`는 반드시 `ev_0` 혹은 `ev_SS` 중 하나입니다. 이는 `Induction`이라는 이름에서도 잘 알 수 있죠. 이 사실을 inversion이라고 부르며 증명에 다양한 방법으로 활용할 수 있습니다. Inversion을 활용한 증명을 보기 전에 inversion 자체를 먼저 증명해보겠습니다.

```coq, line_num
Theorem ev_inversion : forall (n : nat),
    ev n ->
      (n = 0)
      \/
      (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left.
    reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right.
    exists n'.
    split.
    reflexivity.
    apply E'.
  Qed.
```

`ev`에 대해서 inversion을 풀어 쓴 증명입니다. 한국말로 풀어쓰면 ~_n이 짝수면 n = 0이거나 n + 2는 짝수다_~ 정도가 됩니다. 증명에선 `destruct`를 이용해서 `ev n`를 `ev_0`과 `ev_SS`로 쪼갰습니다. 주석을 보면 `E`의 모습이 복잡해보일 수 있지만 자세히 보면 [위](#definitionev)에서 한 `ev`의 정의와 같은 모양입니다.

방금 만든 `ev_inversion`을 이용해서 다른 걸 증명해보겠습니다. 아래를 봅시다.

```coq, line_num
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0 | H1].
  - (* H0: S (S n) = 0 *)
    discriminate H0.
  - (* H1: exists n' : nat, S (S n) = S (S n') /\ ev n' *)
    destruct H1 as [n' [Hnm Hev]].
    injection Hnm as Heq.
    rewrite Heq.
    apply Hev.
  Qed.
```

4번 줄의 `ev_inversion`은 `H: ev (S (S n))`을 2개로 쪼갭니다. 첫번째 경우는 `H`가 `ev 0`인 경우로, `S (S n)`은 절대 0이 될 수 없으므로 `discriminate` tactic으로 간단하게 처리했습니다. 두번째 경우도 `ev_SS`의 정의를 잘 지지고볶아서 쉽게 결론에 도달할 수 있습니다.

방금의 증명은 `inversion` tactic을 이용하면 더 짧게 만들 수 있습니다. 아래의 예시를 보겠습니다.

```coq, line_num
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

```coq, line_num
Theorem not_ev_1 : ~ ev 1.
Proof.
  intros H.
  inversion H.
  Qed.
```

1은 0도 될 수 없고 `S (S n)`도 될 수 없습니다. 따라서 `ev 1`에 `inversion`을 쓰면 모든 경우가 알아서 `discriminate`되고 증명이 끝납니다.

## Induction on Evidence

이번에는 귀납법을 해보겠습니다. [이전](Chap2-1.html#keywordinduction)에 `nat`에 귀납법을 사용했을 때와 비슷합니다. 아래의 예시를 보면서 설명하겠습니다.

[[anchor, id=keyword induction]][[/anchor]]

```coq, line_num
Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [ | n' E' IH].
  - (* E = ev_0 *)
    unfold Even.
    exists 0.
    reflexivity.
  - (* E = ev_SS n' E' with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even.
    exists (S k).
    simpl.
    reflexivity.
Qed.
```

5번 줄을 보면, goal이 `Even 0`이고 context에 `E: ev n`이 있는 상황에서 `induction E`를 했습니다. 그럼 goal이 `Even 0`와 `Even (S (S n'))`으로 나눠집니다. 또한 두번째 subgoal에서는 context에 `E: ev n'`과 `IH: Even n'`이 추가됐습니다.

```coq, line_num
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1 E2.
  induction E1 as [ | n' E1' IH1].
  - (* ev (0 + m) *)
    simpl.
    apply E2.
  - (* ev (S (S n') + m) *)
    simpl.
    apply ev_SS.
    apply IH1.
  Qed.
```

`induction` tactic을 이용해서 또다른 재밌는 증명을 해봤습니다. `simpl` tactic이 생각보다 강력해서 신기하네요.

## Inductive Relations

`ev`는 `nat`을 하나 받아서 `Prop`을 내놓습니다. 즉, `ev`는 자연수의 *성질* (*property*)이라고 생각할 수 있죠. 비슷하게 생각을 하면, `le`는 `nat` 2개를 받아서 `Prop`을 내놓으므로 `le`는 자연수들의 *관계* (*relation*)이라고 생각할 수 있습니다.

```coq, line_num
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).
```

`le`의 정의를 다시 써 보았습니다. 이전에는 `<=` 기호를 Fixpoint를 이용해서 정의했지만 이제는 Inductive로 정의했습니다. 이렇게하면 `inversion` tactic을 사용할 수 있기 때문에 더 강력한 증명들을 할 수 있습니다.

```coq, line_num
Theorem silly1 : 5 <= 2 -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H as [ | n' m' H' H2].
  inversion H' as [ | n'' m'' H'' H3].
  inversion H''.
  Qed.
```

`inversion`을 다시 연습할 겸 예제를 만들어보았습니다. 4번 줄의 `inversion`은 `H: 5 <= 2`를 `le_n`과 `le_S`로 나눕니다. 5와 2는 다르므로 `le_n`은 자동으로 버려지고 `le_S`에 의해 `H': 5 <= 1`이 생깁니다. `H'`에 `inversion`을 다시 쓰면 `H'': 5 <= 0`이 나오고 거기에 다시 `inversion`을 하면 가정이 거짓이 되므로 증명이 끝납니다.

[[box]]

[[giant]] Type 표기법 [[/giant]]

아래의 세 표기법은 전부 동일합니다.

```coq, line_num
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
```

- `bin`의 type은 항상 `bin`이므로 생략했습니다.
- `le` 혹은 `ev`처럼 `Prop`을 반환하는 경우 이런 표기법을 쓸 수 없습니다.

[[br]]

```coq, line_num
Inductive bin : Type :=
  | Z : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
```

- `bin`의 type이 `bin`이라는 것을 ':' 뒤에 표시했습니다.

[[br]]

```coq, line_num
Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
```

- `bin`의 인수들의 type도 ':' 뒤에 표시했습니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap7-1. Inductively defined Propositions](Chap7-1.html)

[[/left]]

[[right]]

[Chap7-3. Regular Expressions](Chap7-3.html) >>

[[/right]]