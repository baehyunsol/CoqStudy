| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Coq

Coq는 Gallina라는 함수형 언어로 이루어져 있습니다.[^Gal] Coq에 대해서 본격적으로 공부하기 전에, 함수형 언어로서의 Coq의 특징에 대해서 알아보겠습니다.

[^Gal]: 막상 책에서는 *Coq 언어*라고 지칭을 할 때가 많아서 어디까지가 무슨 언어인지 사실 저도 잘 모르겠어요. 이 문서에는 Gallina는 더 이상 언급하지 않고, 전부 Coq라는 표현만 썼습니다.

## `Inductive`

[[anchor, id=keyword inductive]][[/anchor]]

Rust의 `enum`에 대응되는 개념으로 Coq에는 `Inductive`가 있습니다. Coq의 primitive type들은 대부분 `Inductive`를 통해서 구현돼 있습니다. 즉, 정수형이나 Boolean등도 Coq 내부에 구현된 특별한 자료형이 아닌, 다른 모든 자료형과 동일하다는 뜻입니다.

Boolean이 어떻게 구현돼 있는지 살펴보겠습니다.

```haskell, line_num
Inductive bool : Type :=
  | true
  | false.
```

Rust에 익숙하신 분이라면 위의 코드를 이해하는 것이 어렵지 않을 것입니다. `bool`이란 type을 정의하고, `bool`에는 `true`와 `false`라는 variant가 있음을 정의합니다. 함수를 정의하는 것도 어렵지 않습니다.

## `Definition`

[[anchor, id=keyword definition]][[/anchor]]

```haskell, line_num
Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
```

[[box]]

`Definition`은 Rust의 함수 정의보다는 Haskell의 함수 정의에 좀 더 가까운 것 같습니다. 위의 코드에서 `negb`는 `negb`라는 함수를 정의한 것이 아니고 단지 `bool` 값을 정의한 것에 불과합니다. 다만 그 값이 `b`라는 다른 인수에 의해 결정될 뿐입니다. 상수 정의도 이것과 동일한 syntax로 할 수 있습니다.

*이 박스 안의 내용은 제 추측입니다. 아직 공부 중이라, 틀린 내용이 있을 수 있습니다.*

[[/box]]

`match`문은 Rust의 `match`문과 대응됩니다.

함수를 호출하는 방식은 Lisp 혹은 Haskell과 비슷합니다. `orb false false`는 `false`와 `false`란 값을 인수로 넘겨서 `orb` 함수를 호출합니다. `orb false (orb false false)`와 같은 형식으로 괄호를 이용해 중의성을 해소할 수 있습니다.

## `Notation`

[[anchor, id=keyword notation]][[/anchor]]

바로 [위](#keyworddefinition)에서 정의했던 것 같은 Lisp 스타일의 함수 호출도 좋지만 C나 수학 스타일의 중위 연산자가 그리울 때가 있습니다. Coq의 `Notation` 키워드는 중위 연산자를 정의할 수 있게 해줍니다.

```haskell, line_num
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```

이제 우리는 `andb x y`라는 Lisp스러운 표현대신 `x && y`라는 일반적인 표현을 사용할 수 있습니다.

## `if`

[[anchor, id=keyword if]][[/anchor]]

함수형 패러다임을 지원하는 최신 언어들이 대부분 그러하듯, Coq의 `if` 또한 식(expression)으로 취급됩니다. 위에서 방금 정의했던 함수들은 아래와 같이 다시 정의할 수 있습니다.

```haskell, line_num
Definition negb (b:bool) : bool :=
  if b then false
  else true.
Definition andb (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.
```

`if` 문 뒤에 조건이 오고, 그 뒤에 `then`과 `else`가 오는 구조입니다. 위에서도 말했듯, Coq에서 `bool`은 special primitive가 아니기에 `if` 문의 조건에 `bool`만 쓸 수 있게 하는 것은 이치에 맞지 않습니다. 따라서, `if`문의 조건에는 모든 type을 다 사용할 수 있습니다(단, 그 type의 variant가 2개이어야 합니다). 그럼 뭐가 참이고 뭐가 거짓인지 어떻게 구분할지 혼란스러울텐데, `Inductive` 문의 정의 안에서 먼저 정의된 variant를 참으로 간주합니다. [위](#keywordinductive)에서 `true`가 `false`보다 먼저 정의됐으니, 이 코드에서는 `true`가 참으로 간주됩니다.

## `Check`

[[anchor, id=keyword check]][[/anchor]]

`Check`는 값을 받아서 그 값의 type을 반환하는 명령어[^f]입니다.

[^f]: `Check`는 일반적인 함수가 아닙니다. 아래에서 자세히 설명하겠습니다. [[br]]*function*이라는 용어는 전부 *함수*로 번역했고, *command*는 전부 *명령어*로 번역했습니다. 문서에서 두 용어를 완전히 구분해서 사용할테니 읽는데 혼동이 없으시길 바라겠습니다.

```haskell, line_num
(*{-
Coq의 주석은
(* .. 주석 .. *)
와 같은 형태로 씁니다. 하지만 Coq의 문법을 지원하는 syntax highlighter를 찾지 못하여 부득이하게
Haskell 스타일로 주석을 썼습니다.
-}*)

Check true.   (*{- true : bool -}*)
Check (andb true true).   (*{- true : bool -}*)

(*{- Coq에서는 함수도 first class object입니다. -}*)
Check andb.   (*{- andb : bool -> bool -}*)

(*{- `Check`는 일반적인 함수가 아니기에 type이 없습니다. -}*)
Check Check.  (*{- error -}*)
```

혹은 `Check value : Type.`의 형태로 theorem prover에게 type이 맞는지 질의할 수도 있습니다.

```haskell, line_num, copy_button(false)
Check true : bool.
```

위와 같이 쓸 경우, `true`가 `bool` type이 맞으면 넘어가고 그렇지 않을 경우 틀렸다고 알려줍니다.

문득 Coq의 type이 어떤 식으로 작동하는지 궁금해져서 몇가지 질의를 더 해보았습니다.

```haskell, line_num
Check true.  (*{- true : bool -}*)
Check bool.  (*{- bool : Set  -}*)
Check Set.   (*{- Set : Type  -}*)
Check Type.  (*{- Type : Type -}*)
```

사용자가 `Inductive` 키워드를 이용해서 정의한 type들은 `Set`이란 type을 가지고 `Set`은 `Type`이란 type을 가집니다.

## `Compute`

[[anchor, id=keyword compute]][[/anchor]]

```haskell, line_num, copy_button(false)
Compute negb true.  (*{- = false : bool -}*)
```

`Compute`는 주어진 식을 계산합니다. `Check`와 마찬가지로 함수가 아니고 명령어입니다.

## Enums

Rust 혹은 Haskell을 할 줄 아시는 분은 enum을 만들면서 variant 안에 다양한 값을 넣어본 기억이 있으실 겁니다. Coq에서도 비슷한 방식의 type 정의를 지원합니다.

```haskell, line_num
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
```

Rust에서 enum을 정의하는 방법과 동일합니다. `color`라는 enum은 `primary`라는 variant를 가지고, `primary`는 `rgb`의 instance 하나를 멤버로 가집니다. `color`를 패턴매칭으로 뜯어내는 방식은 Haskell과 비슷합니다.

```haskell, line_num
Definition is_red_or_black(c: color) : bool :=
  match c with
  | black => true
  | white => false
  | primary red => true
  | primary _ => false
  end.
```

위의 `primary red`처럼, variant와 그 안의 값을 패턴매칭합니다. `_`는 와일드카드 문자로 사용됩니다.

## Modules

[[anchor, id=keyword module]][[/anchor]]

Module은 C++의 namespace와 비슷한 개념입니다. 아니, 그냥 똑같습니다.

```haskell, line_num
Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.
```

위의 코드에서 `Playground`라는 모듈을 정의하고 그 안에서 `b`라는 값을 정의했습니다. `b`는 모듈 안에서 정의됐으므로, global context에서 그냥 `b`와 `Playground.b`가 구분됩니다.

## Tuples

[[anchor, id=concept tuple]][[/anchor]]

Rust 혹은 Haskell을 다뤄본 적이 있다면 tuple이라는 개념이 아주 익숙하실 겁니다.

```haskell, line_num
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.
```

위와 같이 `bit` type 4개로 이뤄진 `bits`라는 type을 정의했습니다.

```haskell, line_num
Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute all_zero (bits B0 B0 B0 B0). (*{- = true : bool -}*)
```

Tuple을 패턴매칭하는 것도 위와 같이 어렵지 않습니다. 꼭 모든 원소들이 동일한 type일 필요는 없습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Inductive complex : Type :=
  | nums (ny : nybble) (int : nat).

Definition all_zero2 (compl: complex) : bool :=
  match compl with
  | nums n _ => all_zero n
  end.
```

`nybble`과 `nat`을 하나씩 원소로 가지는 tuple을 만들었습니다. `nat`이 뭔지는 [다음 장](Chap1-2.html)에 나옵니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

이전 글이 없습니다.

[[/left]]

[[right]]

[Chap1-2. Natural Numbers](Chap1-2.html) >>

[[/right]]