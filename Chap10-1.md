| Table of Contents |
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