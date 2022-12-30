| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Induction Principles

지금까지 보았듯 Coq는 아주 작고 간단한 언어로 이뤄져 있고 그 언어를 이용해서 `\/`, `exists`, `True`, `False`,... 등등 수많은 걸 정의했습니다. `induction` tactic도 마찬가지입니다. `induction` tactic을 위한 특별한 기능이 Coq에 내장돼 있는 것이 ***아니고***, `apply`만을 이용해서 정의돼 있습니다. 그 정의를 살펴보겠습니다.

`nat` type을 이용해서 설명하겠습니다. `Inductive`를 이용해서 `nat`을 정의하면 `nat_rect`, `nat_ind`, `nat_rec`, `nat_sind`가 자동으로 같이 정의됩니다. 이 중 `induction`에 쓰이는 것은 `nat_ind`입니다. `nat_ind`의 모양은 아래와 같습니다.

```haskell, line_num
(*{-
nat_ind = 
fun (P : nat -> Prop) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

Arguments nat_ind P%function_scope f f0%function_scope n
-}*)
Print nat_ind.


(*{-
nat_ind
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
-}*)
Check nat_ind.
```

생긴 건 무섭지만 type을 보면 이해가 쉽습니다. 어떤 `P`에 대해서 `P O`가 성립하고, `P n -> P (S n)`이면 `P n`이 항상 성립한다고 돼 있습니다. 즉, 수학적 귀납법을 그대로 정의해놨습니다. 즉, 우리가 증명을 하면서 `induction`을 쓰는게 결국은 `apply nat_ind`를 쓰는 것과 거의 동일합니다.

그렇다면 `list`처럼 polymorphic한 자료구조는 어떻게 될까요? `list nat`을 위한 `list_ind`와 `list bool`을 위한 `list_ind`가 별개로 정의될까요? 확인해보겠습니다.

```haskell, line_num
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.


(*{-
list_ind = 
fun (X : Type) (P : list X -> Prop) (f : P (nil X))
  (f0 : forall (x : X) (l : list X), P l -> P (cons X x l)) =>
fix F (l : list X) : P l :=
  match l as l0 return (P l0) with
  | nil _ => f
  | cons _ y l0 => f0 y l0 (F l0)
  end
     : forall (X : Type) (P : list X -> Prop),
       P (nil X) ->
       (forall (x : X) (l : list X), P l -> P (cons X x l)) -> forall l : list X, P l

Arguments list_ind X%type_scope P%function_scope f f0%function_scope l
-}*)
Print list_ind.


(*{-
list_ind
     : forall (X : Type) (P : list X -> Prop),
       P (nil X) ->
       (forall (x : X) (l : list X), P l -> P (cons X x l)) -> forall l : list X, P l
-}*)
Check list_ind.
```

위에서 확인했듯이 각 type마다 `list_ind`가 따로 정의되는 것이 아니고 그 자체로 polymorphic하게 정의됩니다.

한번만 더 연습을 해보겠습니다.

```haskell, line_num
Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

(*{-
tree_ind
     : forall (X : Type) (P : tree X -> Prop),
       (forall x : X, P (leaf X x)) ->
       (forall t1 : tree X, P t1 -> forall t2 : tree X, P t2 -> P (node X t1 t2)) ->
       forall t : tree X, P t
-}*)
Check tree_ind.
```

이진트리 구조를 만든 뒤 `tree_ind`가 어떻게 생겼는지 확인해보았습니다.

1. 모든 `leaf`에 대해 `P`가 성립한다.
2. `t1`과 `t2`에 대해 `P`가 성립하면 `t1`, `t2`로 이뤄진 `tree`에 대해서도 `P`가 성립한다.

1과 2를 만족하면 모든 `tree`에 대해서 `P`가 성립한다는게 `tree_ind`의 내용입니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap9-3. ??](Chap9-3.html)

[[/left]]

[[right]]

[Chap10-2. ??](Chap10-2.html) >>

[[/right]]