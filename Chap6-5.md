| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Axioms

[[anchor, id = keyword axiom]][[/anchor]]

공리는 증명 없이 참이라고 받아들여지는 명제를 말합니다. 어떤 체계의 공리가 잘못되면 그 체계 전체의 기반이 무너지므로 공리를 다룰 때는 항상 매우 조심해야합니다. Coq에서는 공리를 어떻게 다룰까요? 아래의 예시를 보겠습니다.

```haskell, line_num
Example function_equality :
  (fun x => plus x 1) = (fun x => plus 1 x).
```

`x => x + 1`과 `x => 1 + x`는 동일한 함수입니다! 하지만 Coq의 논리 체계 안에선 저 둘이 동일한 함수란 걸 증명할 방법이 없습니다. 이런 경우엔 `Axiom`이란 명령어를 사용해서 새로운 공리를 만들면 됩니다.

```haskell, line_num
Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.
```

모든 input에 대해서 동일한 output을 반환하는 두 함수는 동일합니다. 앞으론 그 사실을 증명없이 참이라 받아들이고 사용하겠습니다. 공리는 참인 명제이므로 다른 명제들과 동일한 방식으로 `rewrite`나 `apply`등을 이용해서 사용할 수 있습니다. 아까 증명하던 명제를 다시 증명해보겠습니다.

```haskell, line_num
Example function_equality :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply add_comm.
```

참 쉽죠?

## Excluded Middle

Coq에서는 아래의 명제도 증명불가능합니다.

```haskell, line_num
Theorem excluded_middle :
  forall P : Prop, P \/ ~P.
```

모든 명제는 참 혹은 거짓이니까 당연히 저것도 성립하지 않겠냐 싶겠지만 Coq에선 저걸 증명할 수 없습니다. 책에선 ~_Coq가 classical logic이 아닌 constructive logic을 사용하기 때문에 의도적으로 빼놓았다_~고 했는데 필요하시면 Axiom으로 추가해서 사용해도 됩니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-4. Programming with Propositions](Chap6-4.html)

[[/left]]

[[right]]

[Chap7-1. Inductively defined Propositions](Chap7-1.html) >>

[[/right]]