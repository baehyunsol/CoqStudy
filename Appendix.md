제가 쓰려고 만든 부록 페이지입니다. 아직 CoqIDE에도 익숙하지 않고 stdlib이 있는지도 모르겠어서 그때그때 코드를 복사 붙여넣기해서 쓰는 중입니다. 복사 붙여넣기를 쉽게 하기 위해서 모든 걸 모아둔 페이지입니다.

[[toc]]

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