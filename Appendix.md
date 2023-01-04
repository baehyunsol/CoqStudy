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
From Coq Require Import Init.Nat.
Definition state := total_map nat.

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