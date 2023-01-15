| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Small-Step Operational Semantics

지금까지 봤던 모든 프로그램 검증은 big-step으로 진행됐습니다. 프로그램을 통째로 던져주고, 시작과 끝 조건만 알려주면 Coq이 한번에 검증을 해주었습니다. 간단한 프로그램에선 아주 좋은 방법이지만, 세상은 그렇게 간단하지 않습니다. 예를 들어서, 명령어 10개로 이뤄진 병렬 프로그램을 생각해봅시다. 만약 이 프로그램이 병렬로 돌아가지 않는다면 명령어 10개가 동시에 실행된다고 생각해도 문제가 없습니다. 중간에 누가 끼어들지 않을테니까요. (끼어들더라도 이 프로그램에 영향을 주지 않을테니까요) 하지만 병렬로, 서로 협력하면서 돌아간다면요? 첫번째 프로그램의 명령어가 3개 실행됐을 때, 두번째 프로그램의 7번째 명령어가 실행되면요? 이런 상황에서도 검증이 유효하려면 big-step말고 다른 전략을 취해야합니다. 그래서 이번 장에서는 small-step을 소개합니다.

TODO: typechecker도 big-step/small-step과 관련된 문제라는데 왜 그런지 모르겠습니다...

## tm

본격적으로 small-step operational semantics를 다루기 전에 간단한 언어를 정의하겠습니다. 이번에 정의할 tm이라는 언어는 이전에 봤던 Imp보다 훨씬 간단합니다. 상수와 덧셈밖에 없어요.

```coq, line_num
Inductive tm : Type :=
  | C : nat -> tm         (* 상수 *)
  | P : tm -> tm -> tm.   (* 덧셈 *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.
```

아주 간단하죠? `C 3`은 3이고 `P (C 3) (P (C 2) (C 4))`는 `3 + (2 + 4)`라서 9입니다. 그다음으로 `Notation`도 정의해보겠습니다.

```line_num
Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)

where " t '==>' n " := (eval t n).
```

아까 `Fixpoint`로 정의한 `evalF`를 `Inductive`로 정의해보았습니다. 이 정의는 지금까지 봐왔던 big-step operational semantics를 따르는 정의입니다. small-step으로도 정의해보겠습니다. 아래를 봅시다.

```line_num
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').
```

big-step에서는 `tm`이 아무리 복잡하더라도 한번에 계산을 끝냈는데, 이번에는 한번에 한 단계씩 원자적으로(atomic) 계산합니다. 예를 들어서, `P (C 3) (P (C 2) (C 4))`를 big-step으로 계산하면 9가 되지만 small-step으로 계산하면 `P (C 3) (C 6)`이 됩니다.

`step`의 정의를 좀 더 자세하게 뜯어보면 아래와 같습니다.

- 덧셈의 양변이 상수 (`C`)일 경우 덧셈을 계산합니다.
- 덧셈의 인수 중 다른 덧셈이 포함돼 있을 경우 그 덧셈부터 계산합니다. 이때는 왼쪽 인수부터 확인합니다.

## Relations

이번에는 single-step의 관계(relation)에 대해서 얘기를 해보겠습니다. [11장](Chap11-1.html)에서 봤던 내용들이 다시 나오니 기억이 안 나시면 잠깐 복습을 하고 와주세요.

```coq
Definition relation (X : Type) := X -> X -> Prop.
```

Coq에서 관계(relation)는 위와 같이 정의합니다. 어떤 type `X`의 원소 2개가 갖는 `Prop`을 관계라고 하죠. 저희는 `X`가 tm인 관계를 살펴보는게 아니고 `X`가 single-step인 관계를 살펴볼 예정입니다. 먼저 `deterministic`이라는 관계부터 살펴보겠습니다.

### Determinism

```coq, line_num
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem step_deterministic:
  deterministic step.
```

tm의 single-step이 deterministic하다는 정의입니다. 쉽게 말하면, 어떤 tm이 주어졌을 때, 거기서 single-step을 거치면 그 다음 tm의 모양은 최대 1개입니다. 즉, 다음 상태가 유일하게 정해지거나 더 이상 step을 진행할 수 없습니다. 이전에 정의했던 Imp도 deterministic한 언어라 동일한 성질을 갖습니다.

```coq, line_num
Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1;
  intros y2 Hy2.
  - (* ST_PlusConstConst *)
    inversion Hy2;
    subst.
    + (* ST_PlusConstConst *)
      reflexivity.
    + (* ST_Plus1 *)
      inversion H2.
    + (* ST_Plus2 *)
      inversion H2.
  - (* ST_Plus1 *)
    inversion Hy2;
    subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      apply IHHy1 in H2.
      rewrite H2.
      reflexivity.
    + (* ST_Plus2 *)
      inversion Hy1.
  - (* ST_Plus2 *)
    inversion Hy2;
    subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      inversion H2.
    + (* ST_Plus2 *)
      apply IHHy1 in H2.
      rewrite H2.
      reflexivity.
  Qed.
```

`step_deterministic`의 증명입니다. single-step으로 가능한 모든 경우의 수를 `inversion`을 통해서 풀어헤친 뒤 `reflexivity`로 증명했습니다. 증명 과정에서 동일한 tactic이 반복되는게 귀찮았는지 책에선 `Ltac`을 사용해서 축약을 했습니다.

```line_num
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.
```

저 tactic이 어떤 원리로 동작하는지는 중요하지 않습니다. 다만 tactic을 재귀적으로 쓴다는게 신기하네요. `solve_by_inverts`를 이용해서 다시 증명을 해보면 아래와 같습니다.

```coq, line_num
Theorem step_deterministic_alt:
  deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2;
    subst;
    try solve_by_invert.
  - (* ST_PlusConstConst *)
    reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2.
    rewrite H2.
    reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2.
    rewrite H2.
    reflexivity.
  Qed.
```

아까보다 훨씬 간단하군요.

### Strong Progress

방금 전에는 step이 유일하다는 걸 증명했죠? 이번엔 step이 가능하다는 걸 증명하겠습니다. 즉, 모든 tm에 대해서 더 이상 계산이 불가능한 상태거나 (이미 계산이 끝나서 상수밖에 안 남은 경우), single-step을 밟을 수 있음을 증명하겠습니다.

```coq, line_num
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).
```

그 전에, `value`라는 `Inductive`를 정의했습니다. `value`는 `tm`이 상수인지를 `Prop`으로 나타냅니다.

```coq, line_num
Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *)
    left.
    apply v_const.
  - (* P *)
    right.
    destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* left *)
      destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* left *)
        inversion IHt1.
        inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* right *)
        exists (P t1 t2').
        apply ST_Plus2.
        apply IHt1.
        apply Ht2.
    + (* right *)
      exists (P t1' t2).
      apply ST_Plus1.
      apply Ht1.
  Qed.
```

이번 증명도 간단합니다. `t`가 덧셈인지 상수인지를 경우를 나눠서 증명했습니다.

### Normal Form

Strong Progress를 증명하면서 `value`의 중요한 성질을 하나 발견했습니다. `value`는 더 이상 step을 밟을 수 없고, 더 이상 step을 밟을 수 없으면 `value`입니다. 이처럼 더 이상 step을 밟을 수 없는 상태를 *normal form*이라고 합니다. Normal form을 Coq으로 정의해보면 아래와 같습니다.

```coq, line_num
Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.
```

한가지 특기할 사항은 `normal_form`이 `step`에 대해서 정의된게 아니고 모든 `relation`에 대해서 정의됐다는 점입니다. 어떤 관계 `-->`이든지 `t --> t'`인 관계가 존재하지 않으면 `t`는 normal form이라고 부릅니다. tm에서 `C`가 normal form인 걸 증명해보겠습니다.

```coq, line_num
Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form.
  intros v H.
  destruct H.
  intros contra.
  destruct contra.
  inversion H.
  Qed.
```

증명은 아주 간단합니다. 계속 쪼개다보면 7번 줄에서 `contra: exists t', C n --> t'`가 남습니다. `C n --> t'`가 되는 경우는 없죠? 그래서 `inversion`을 쓰면 증명이 끝납니다.

`value`와 `normal_form`이 동치인 걸 보여야하니 반대방향들도 증명하겠습니다. 아래를 봅시다.

```coq, line_num
Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  unfold normal_form.
  intros t H.
  assert (G : value t \/ exists t', t --> t').
    { apply strong_progress. }
  destruct G as [G | G].
  - (* l *)
    apply G.
  - (* r *)
    contradiction.
  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  apply nf_is_value.
  apply value_is_nf.
  Qed.
```

이 사실이 흥미로운 이유 중 하나는 `value`는 문법적(syntactic)인 요소고 normal form은 의미적(semantic)인 요소인데 둘이 정확히 대응된다는 겁니다.

모든 언어가 다 이런 성질을 갖는 건 아닙니다. 아직 상수가 아니지만 step을 진행하는게 불가능한 언어들도 정의할 수 있는데, 저런 상태를 막혔다(stuck)고 합니다. Stuck에 대해서는 15단원에서 다루겠습니다.

## Multi-step Reduction

지금까지는 single-step 위주로 봤습니다. 그래서 small-step은 항상 single-step인가 궁금해하셨을 수도 있는데, 그렇지 않습니다. small-step은 0번 이상의 모든 단계를 허용합니다. 이번엔 그런 식으로 단계를 확장하는 방법을 살펴보겠습니다. 먼저, `multi`의 정의를 봅시다.

```coq, line_num
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
```

`x`에서 `x`로 가는 관계는 0 단계를 거치면 되죠? 그걸 `multi_refl`에서 정의했습니다. `multi_step`은 단계를 거치는 과정을 귀납적으로 정의했습니다. `x`에서 `y`로 가는 과정은 딱 1단계를 거치고 (`multi`가 안 붙었으니까), `y`에서 `z`로 가는 과정은 0단계 이상을 거칩니다. 그렇게 되면 `x`에서 `z`로 가는 관계도 있다고 정의함으로써 0 이상의 임의의 단계를 거치는 `multi`라는 관계를 정의했습니다.

Multi-step을 위한 `Notation`도 정의하겠습니다. 아래를 봅시다.

```line_num
Notation " t '-->*' t' " := (multi step t t') (at level 40).
```

TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-5. Hoare Logic as a Logic](Chap14-5.html)

[[/left]]

[[right]]

[Chapter 15-1. Basics](Chap15-1.html) >>

[[/right]]