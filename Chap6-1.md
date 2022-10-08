| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# 가제

지금까지 저희는 아주 간단한 논리들 (`p -> q`, `x = y` 등)만 봤습니다. Coq가 다룰 수 있는 논리는 이것들보다 훨씬 많은데, 이번 장에서는 그 논리들을 살펴보겠습니다.

그 전에, `Prop`이라는 type에 대해서 먼저 알아보겠습니다.

## Prop

[이전](Chap4-2.html#higher-order-functions)에 Coq에서 함수가 일급시민이라고 언급했습니다. 그것과 마찬가지로, 모든 명제들도 일급시민입니다. 모든 명제들은 `Prop`이라는 type을 가지며, 함수의 인자로 쓰거나 반환값으로 쓰는 등 다양한 연산[^fc]을 할 수 있습니다.

[^fc]: `nat`, `bool`등이 할 수 있는 걸 `Prop`도 전부 할 수 있습니다.

```haskell, line_num
Check 2 = 2.     (*{- : Prop -}*)
Check 3 = 2.     (*{- : Prop -}*)
Check (forall n: nat, n + 0 = 0 + n).  (*{- : Prop -}*)
Compute 3 = 3.   (*{- 3 = 3 : Prop -}*)
Compute 3 = 2.   (*{- 3 = 2 : Prop -}*)
```

위에서처럼 `Check`나 `Compute`를 할 수도 있고, 아래처럼 함수와 조합하여 더 놀라운 것들도 할 수 있습니다.

```haskell, line_num
Definition is_injective {A B} (f : A -> B) :=
  forall x y : A,
  f x = f y -> x = y.
```

`is_injective`는 함수를 받아서 `Prop`을 내놓는 함수입니다. `is_injective`가 받는 함수가 injective하면 반환된 `Prop`이 참이고 아니면 반환된 `Prop`이 거짓입니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem S_injective : is_injective S.

Proof.
  intros n m H.
  injection H as H1.
  apply H1.
  Qed.
```

자연수를 정의할 때 쓰는 `S`가 injective하단 걸 증명하기 위해 `is_injective S`라는 아주 간단한 표현을 썼습니다. 쉽죠?

[[box]]

#### eq

참고로 `x = y` 할 때의 `=`도 내장특수 문법이 아닌 일반 함수입니다. `=`는 Coq 표준 라이브러리에 정의돼 있으며 이름은 `eq`입니다. Type을 확인해보면 아래와 같습니다.

```haskell
Check @eq : forall A : Type, A -> A -> Prop.
```

즉, `eq`는 `A`라는 type의 instance 2개를 받아서 그 둘이 같은지 다른지의 `Prop`을 반환하는 함수입니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap5-3. More tactics](Chap5-2.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]