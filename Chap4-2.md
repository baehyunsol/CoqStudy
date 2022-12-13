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
Check doit3times. (*{- (?X -> ?X) -> ?X -> ?X where ?X : [ |- Type] -}*)

Check @doit3times. (*{- forall X : Type, (X -> X) -> X -> X -}*)
```

Haskell에서 고차함수의 type 표현과 거의 비슷합니다.

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

아래는 심심해서 구현해본 `flat_map`입니다.

```haskell, line_num
Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
```

아래는 심심해서 증명해본 `map_rev`입니다. `map rev`와 `rev map`은 동일하다는 걸 증명했습니다. 증명에 쓰기 위해서 도움정리를 먼저 증명했습니다.

```haskell, line_num
Lemma map_single : forall (X Y : Type) (f : X -> Y) (l : list X) (e : X),
  map f (l ++ [e]) = (map f l) ++ [f e].
Proof.
  intros X Y f l e.
  induction l as [ | h' t' IHl'].
  - (*{- l = [] -}*)
    reflexivity.
  - (*{- l = h' :: t' -}*)
    simpl.
    rewrite IHl'.
    reflexivity.
  Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [ | h' t' IHht'].
  - (*{- l = [] -}*)
    reflexivity.
  - (*{- l = h' :: t' -}*)
    simpl.
    rewrite <- IHht'.
    rewrite map_single.
    reflexivity.
  Qed.
```

## fold

Haskell이나 Rust의 fold, 혹은 Python의 reduce입니다.

```haskell, line_num
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.
```

마지막 인수로 `b`가 있는 것을 유의하시기 바랍니다. 빈 list를 넘길 경우 `b`를 기본값으로 사용합니다.

## Functions that return other functions

함수형 언어답게 함수를 반환하는 함수를 만들 수도 있습니다.

```haskell, line_num
Definition adder (n : nat) : nat -> nat :=
  plus n.

Definition add3 : nat -> nat := adder 3.
```

`adder` 함수는 `n`을 더하는 함수를 반환합니다. 즉, `adder 3`은 자연수 값이 아니고 3을 더하는 함수입니다. 위의 코드에서 정의된 `add3`을 이용해서 `add3 4`를 하면 7이 나옵니다.

함수형 언어에서는 이를 partial application이라고 부릅니다. `plus`는 인수를 2개 받는 함수인데 `adder` 안에서는 인수를 하나만 줬죠? 나머지 한 인수는 `adder`의 인수로 들어옵니다. 이런 식으로 인수를 따로 주기 때문에 partial application이라고 부릅니다.

## Currying

함수형 언어를 배우면 항상 만나게되는 Curry 선생님입니다. Curry는 간단하게 말하면 `f(x, y)`를 `f(x)(y)`로 바꿔주는 함수입니다. 무슨 말인지 알듯말듯 하죠? 아래의 예시를 보면서 더 설명드리겠습니다.

먼저, Curry 함수의 정의는 아래와 같습니다.

```haskell, line_num
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
```

참고로 `(x, y)`는 pair의 notation이고 `X * Y`는 prod type의 notation입니다. 정의는 [부록](Appendix.html#currying)에 있습니다. 위의 정의만 보고는 감이 잘 안 오실텐데 아래에서 실제 함수와 함께 용례를 보겠습니다.

```haskell, line_num
Definition add (x : nat * nat) : nat :=
  match x with
  | (x, y) => x + y
  end.

Definition curry_add := prod_curry add.
```

먼저 두 숫자를 더하는 `add`라는 함수를 만들었습니다. 그리고 `add`를 curry하여 `curry_add`라는 함수도 만들었습니다. 두 함수의 모양이 어떻게 다른지 아래를 보겠습니다.

```haskell, line_num
Check add.                (*{- nat * nat -> nat -}*)
Check curry_add.          (*{- nat -> nat -> nat -}*)

Compute add(3, 4).        (*{- 7 -}*)
Compute curry_add(3)(4).  (*{- 7 -}*)
```

위를 보시면 감이 오실 겁니다. `add`는 `add(3, 4)` 꼴의 모양으로 썼지만 `curry_add`는 `curry_add(3)(4)` 꼴로 씁니다. 그래서 둘의 type도 다릅니다. 이것만 보시면 이런 함수가 왜 필요한지 의문이 들 겁니다.

Curry는 함수형 프로그래밍에서 아주 중요한 개념 중 하나인데[^hskl], 너무 자세히 다루는 건 이 문서의 취지에 어긋나므로 대표적인 예시 몇개만 보겠습니다. 아래는 curry를 이용해서 partial application을 구현한 예시입니다.

[^hskl]: 실제로 하스켈 언어에서 모든 다변수함수는 curry돼 있습니다.

```haskell, line_num
Definition add3 := prod_curry add 3.

Check add3.     (*{- nat -> nat -}*)
Compute add3 4. (*{- 7 -}*)
```

[위](#functions-that-return-other-functions)에서 구현했던 `add3`를 더 간단하게 구현했습니다.

Curry가 있으면 당연히 uncurry도 있겠죠? 구현해보겠습니다.

```haskell, line_num
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (x : X * Y) : Z := f (fst x) (snd x).

Check @prod_curry.    (*{- forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z -}*)
Check @prod_uncurry.  (*{- forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z -}*)
```

curry의 정의와 아주 비슷하게 생겼습니다. 이번에는 `f(x)(y)`를 `f(x, y)`로 바꿔줍니다. 즉, `prod_uncurry (prod_curry add)`는 `add`와 동일합니다. 저 둘이 동일하다는 걸 아래에서 일반화된 형태로 증명해보겠습니다.

### uncurry curry curry uncurry

```haskell, line_num
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.
```

먼저 curry uncurry가 identity라는 걸 증명했습니다. 증명이 간단해서 먼저 적었습니다.

```haskell, line_num
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  induction p as [x y].
  - (*{- x : X, y : Y -}*)
    assert (H: (prod_curry f) (x) (y) = f (x, y)).
      { reflexivity. }
    rewrite <- H.
    assert (H2: forall f2 : X -> Y -> Z, (prod_uncurry f2) (x, y) = f2 x y).
      { reflexivity. }
    rewrite H2.
    reflexivity.
  Qed.
```

그 다음은 uncurry curry가 identity라는 걸 증명했습니다. 증명이 아까보다 긴데 더 짧은게 있을지 모르겠습니다. 6번 줄에서 `induction p`를 이용해서 `f p` 꼴의 형태들을 전부 `f (x, y)`의 꼴로 바꿨습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap4-1. Polymorphism](Chap4-1.html)

[[/left]]

[[right]]

[Chap 5-1. Apply tactics](Chap5-1.html) >>

[[/right]]