| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Higher Order Fuctions

함수형 언어들의 가장 큰 특징 중 하나는 함수들이 일급시민[^igsm]이라는 겁니다. 즉, 함수를 다른 함수에게 인자로 주거나, 함수가 함수를 반환하는 등 함수를 다른 모든 type들과 동일하게 취급합니다. 이 개념은 function pointer와는 조금 다릅니다. Function pointer도 함수를 다른 함수의 인자로 넘길 수 있게 해주지만 C언어에서 함수와 정수가 동일하게 다뤄지나요? 잘 모르겠네요.

고차 함수[^gchs]는 아주 다양한 기술들을 구사할 수 있게 해줍니다. Python 혹은 Rust에서 map/reduce/filter를 사용해보셨을 겁니다. 또한 저 함수들을 쓰면서 람다함수를 정의한 적도 있으실 겁니다. Coq에서는 해당 함수들을 어떻게 정의하는지 살펴보겠습니다.

[^igsm]: 보통 first-class citizen을 일급시민이라고 번역하더군요. 썩 마음에 들진 않습니다.
[^gchs]: 보통 higher-order function을 고차함수라고 번역하더군요. 그럭저럭 마음에 듭니다.

## Function as argument

```haskell, line_num
Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).
```

함수 `f`와 값 `n`을 받아서 `f(f(f(n)))`을 반환하는 함수입니다. Type은 아래와 같습니다.

```haskell, line_num
Check doit3times : (?X -> ?X) -> ?X -> nat -> ?X where ?X : [ |- Type]

Check @doit3times : forall X : Type, (X -> X) -> X -> nat -> X
```

Haskell에서 higher order function의 type 표현과 거의 비슷합니다.

## filter

```haskell, line_num
Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t => if test h
    then h :: (filter test t)
    else filter test t
  end.
```

`filter` 구현입니다. 제대로 구현했는지 검사해보겠습니다.

```haskell, line_num
Fixpoint is_len1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Compute filter is_len1 [[]; [1]; [2; 3]; [4]; [5; 6; 7]].
```

결과가 `[[1]; [4]]`이 나옵니다. 제대로 구현이 됐군요. filter에만 단한번 쓰기 위해서 `is_len1`을 정의하는 건 불필요해보입니다. 다행히도 Coq는 익명함수를 지원합니다. 아래의 예시를 보겠습니다.

```haskell
Compute filter (fun l => (length l) =? 1) [[]; [1]; [2; 3]; [4]; [5; 6; 7]].
```

[[anchor, id = keyword fun]][[/anchor]]

번거롭게 함수를 정의할 필요없이 `fun` 키워드를 통해서 익명함수를 정의하는 걸 볼 수 있습니다.

## map

함수형 언어의 꽃인 `map`입니다.

```haskell, line_num
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
```

## fold

## Functions that return other functions

## Currying

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap4-1. Polymorphism](Chap4-1.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]