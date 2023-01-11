제가 쓰려고 만든 부록 페이지입니다. 아직 CoqIDE에도 익숙하지 않고 stdlib이 있는지도 모르겠어서 그때그때 코드를 복사 붙여넣기해서 쓰는 중입니다. 복사 붙여넣기를 쉽게 하기 위해서 모든 걸 모아둔 페이지입니다.

[[toc]]

## Imp

12장 이후에 쓰이는 예제들은 아래의 코드를 무식하게 복붙하고 시작합시다!

### total map

```haskell, line_num
Require Export Coq.Strings.String.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).
```

### 언어 문법

```haskell, line_num
From Coq Require Import Lia.
From Coq Require Import Init.Nat.
Definition state := total_map nat.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
```

### Equivalence

```haskell, line_num
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 H st st'.
  split;
  intros H2.
  - (*{- if -> c1 -}*)
    inversion H2;
    subst.
    + (*{- H7: st =[c1]=> st' -}*)
      assumption.
    + (*{- H7: st =[c2]=> st' -}*)
      rewrite H in H6.
      unfold beval in H6.
      discriminate.
  - (*{- c1 -> if -}*)
    apply E_IfTrue.
    + (*{- b = true -}*)
      apply H.
    + (*{- st =[c1]=> st' -}*)
      assumption.
  Qed.

Theorem if_false: forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 H st st'.
  split;
  intros H2.
  - (*{- if -> c2 -}*)
    inversion H2;
    subst.
    + (*{- H7: st =[ c1 ]=> st' -}*)
      rewrite H in H6.
      unfold beval in H6.
      discriminate.
    + (*{- H7: st =[c2]=> st' -}*)
      assumption.
  - (*{- c2 -> if -}*)
    apply E_IfFalse.
    + (*{- b = false -}*)
      apply H.
    + (*{- st =[c2]=> st' -}*)
      assumption.
  Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb.
  split;
  intros H.
  - (*{- while -> skip -}*)
    inversion H. subst.
    + (*{- E_WhileFalse -}*)
      apply E_Skip.
    + (*{- E_WhileTrue -}*)
      rewrite Hb in H2.
      discriminate.
  - (*{- skip -> while -}*)
    inversion H.
    subst.
    apply E_WhileFalse.
    apply Hb.
  Qed.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  intros b c st st' Hb H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  inversion Heqcw;
  subst;
  clear Heqcw.
  (*{- The two interesting cases are the ones for while loops: -}*)
  - (*{- E_WhileFalse -}*)
    unfold bequiv in Hb.
    (*{- rewrite is able to instantiate the quantifier in st -}*)
    rewrite Hb in H.
    discriminate.
  - (*{- E_WhileTrue -}*)
    apply IHceval2.
    reflexivity.
  Qed.

Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c H st st'.
  split;
  intros H2.
  - (*{- true -> nonterm -}*)
    apply (while_true_nonterm b c st st') in H.
    apply H in H2.
    destruct H2. (*{- H2: False -}*)
  - (*{- nonterm -> true -}*)
    destruct b;
    remember <{while true do skip end}> as cw eqn: H2eqcw.
    induction H2;
    inversion H2eqcw;
    subst;
    clear H2eqcw.
    +
      unfold beval in H0.
      discriminate H0.
    +
      clear H.
      clear H0.
      assert (H3: st' =[ while true do c end ]=> st'').
      { apply IHceval2. reflexivity. }
      assert (H4: st =[ while true do c end ]=> st').
      Admitted. (*{- TODO -}*)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st.
  reflexivity.
  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H st.
  symmetry.
  apply H.
  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv.
  intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st).
  rewrite (H23 st).
  reflexivity.
  Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  intros b st.
  reflexivity.
  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  intros b1 b2 H st.
  symmetry.
  apply H.
  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st).
  rewrite (H23 st).
  reflexivity.
  Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  intros c st st'.
  reflexivity.
  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv.
  intros c1 c2 H st st'.
  rewrite H.
  reflexivity.
  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv.
  intros c1 c2 c3 H12 H23 st st'.
  rewrite H12.
  apply H23.
  Qed.

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' H st st'.
  split;
  intros H2;
  inversion H2;
  subst;
  apply E_Asgn;
  rewrite H;
  reflexivity.
  Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2 st st'.
  split;
  intros H3;
  inversion H3;
  subst.
  - (*{- c1 -> c1' -}*)
    assert (H5: st =[ c1' ]=> st'0).
      { apply H1. apply H4. }
    assert (H6: st'0 =[ c2' ]=> st').
      { apply H2. apply H7. }
    apply (E_Seq c1' c2' st st'0 st' H5 H6).
  - (*{- c1' -> c1 -}*)
    assert (H5: st =[ c1 ]=> st'0).
      { apply H1. apply H4. }
    assert (H6: st'0 =[ c2 ]=> st').
      { apply H2. apply H7. }
    apply (E_Seq c1 c2 st st'0 st' H5 H6).
  Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  intros b b' c1 c1' c2 c2' H1 H2 H3 st st'.
  split;
  intros H4;
  inversion H4;
  subst.
  - (*{- b -> b', b = true -}*)
    assert (H5: beval st b' = true).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c1' ]=> st').
    { apply H2. apply H9. }
    apply (E_IfTrue st st' b' c1' c2' H5 H6).
  - (*{- b -> b', b = false -}*)
    assert (H5: beval st b' = false).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c2' ]=> st').
    { apply H3. apply H9. }
    apply (E_IfFalse st st' b' c1' c2' H5 H6).
  - (*{- b' -> b, b' = true -}*)
    assert (H5: beval st b = true).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c1 ]=> st').
    { apply H2. apply H9. }
    apply (E_IfTrue st st' b c1 c2 H5 H6).
  - (*{- b' -> b, b' = false -}*)
    assert (H5: beval st b = false).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c2 ]=> st').
    { apply H3. apply H9. }
    apply (E_IfFalse st st' b c1 c2 H5 H6).
  Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { 
    unfold bequiv, cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile eqn:Heqcwhile.
    induction Hce;
    inversion Heqcwhile;
    subst.
    + (*{- E_WhileFalse -}*)
      apply E_WhileFalse.
      rewrite <- Hbe.
      apply H.
    + (*{- E_WhileTrue -}*)
      apply E_WhileTrue with (st' := st').
      * (*{- show loop runs -}*)
        rewrite <- Hbe.
        apply H.
      * (*{- body execution -}*)
        apply (Hc1e st st').
        apply Hce1.
      * (*{- subsequent loop execution -}*)
        apply IHHce2.
        reflexivity.
  }
  intros.
  split.
  - (*{- b -> b' -}*)
    apply A;
    assumption.
  - (*{- b' -> b -}*)
    apply A;
    try apply sym_bequiv;
    try apply sym_cequiv;
    assumption.
  Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).
```

### Hoare Logic

```haskell, line_num
Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).
Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP.
  inversion H;
  subst.
  assumption.
  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12;
  subst.
  eauto.
  Qed.

Theorem hoare_asgn: forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE.
  subst.
  unfold assn_sub in HQ.
  assumption.
  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros p p' q c H0 H1 st st' H2 H3.
  apply H0 with st. (*{- H0: {p'} c {q} -}*)
  - (*{- st =[ c ]=> st' -}*)
    apply H2. (*{- H2: st =[ c ]=> st' -}*)
  - (*{- p' st -}*)
    apply H1. (*{- H1: p ->> p' -}*)
    apply H3. (*{- H3: p st -}*)
  Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros p q q' c H0 H1 st st' H2 H3.
  apply H1. (*{- H1: q' ->> q -}*)
  apply H0 with st. (*{- H0: {p} c {q'} -}*)
  - (*{- st =[ c ]=> st' -}*)
    apply H2. (*{- H2: st =[ c ]=> st' -}*)
  - (*{- p st -}*)
    apply H3. (*{- H3: p st -}*)
  Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - (*{- {P'} c {Q} -}*)
    apply hoare_consequence_post with (Q' := Q').
    + (*{- {P'} c {Q'} -}*)
      assumption.
    + (*{- Q' ->> Q -}*)
      assumption.
  - (*{- P ->> P' -}*)
    assumption.
  Qed.

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.
Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  congruence.
  Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 H1 H2 st st' H3 H4.
  inversion H3;
  eauto.
  Qed.

From Coq Require Import Arith.PeanoNat. Import Nat.

Ltac assn_auto :=
  unfold assert_implies, assn_sub, t_update, bassn;
  intros st;
  simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;
  auto;
  try lia.
```

## Functional Programming

### Map, Filter, Fold

```haskell, line_num
Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t => if test h
    then h :: (filter test t)
    else filter test t
  end.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.
```

### Currying

pair와 prod의 정의도 포함시켰습니다.

```haskell, line_num
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (x : X * Y) : Z := f (fst x) (snd x).
```

## Natural Numbers

```haskell, line_num
Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Even x := exists n : nat, x = double n.

Fixpoint even (n : nat) :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => even n
  end.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [ | n' IHn'].
  - (*{- n = 0 -}*)
    reflexivity.
  - (*{- n = S n' -}*)
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [ | n'].
  - (*{- n = O -}*)
    intros m.
    rewrite -> add_0_r.
    reflexivity.
  - (*{- n = S n' -}*)
    intros m. simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
  Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
    | O => true
    | _ => false
    end
  | S n' => match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.

Fixpoint leb (m n : nat) : bool :=
  match m with
  | O => true
  | S m' => match n with
    | O => false
    | S n' => leb m' n'
    end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
```

## List

```haskell, line_num
Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint append {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | h :: t => h :: (append t l2)
  end.

Notation "x ++ y" := (append x y)
                     (right associativity, at level 60).
```