| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Polymorphism

[[box]]

Polymorphism이 뭔지 이미 아신다고 가정하고 설명하겠습니다. Polymorphism의 개념을 알고 싶으신 분들은 아래 링크의 글들을 읽어주시기 바랍니다.

- [Wikipedia: Polymorphism](https://en.wikipedia.org/wiki/Polymorphism_(computer_science))
  - In programming language theory and type theory, polymorphism is the provision of a single interface to entities of different types or the use of a single symbol to represent multiple different types.
  - 현재 엔진 오류로 위의 링크가 동작하지 않습니다. 빠른 시일내로 고치겠습니다.
- [Wikipedia: Generic programming](https://en.wikipedia.org/wiki/Generic_programming)
  - Generic programming is a style of computer programming in which algorithms are written in terms of types *to-be-specified-later* that are then instantiated when needed for specific types provided as parameters.

[[/box]]

오래 기다리셨습니다. 드디어 polymorphic list를 구현해볼 시간입니다. 아래의 정의를 봅시다.

```haskell, line_num
Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```

아주 직관적인 문법이 사용된 걸 보실 수 있습니다. 지금까지 봐왔던 것과 다르게 `Inductive` 키워드가 인자를 받습니다. 즉, `list`에 `nat`을 넘겨주면 자연수의 list가 되는 거고 `bool`을 넘겨주면 boolean의 list가 되는 겁니다.

즉 `list`는 `Type`을 받아서 `Type`을 내놓는 함수로 생각하실 수 있습니다. 실제로 `Check list.`를 해보면 `list: Type -> Type`이라고 나옵니다.

## repeat

`list`를 다시 정의했으니 함수들도 전부 다시 정의해야합니다. 전부 다시 정의하기는 번거로우니 대표로 `repeat`만 다시 정의해보겠습니다.

```haskell, line_num
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.
```

[기존](Chap3-2.html#definitionrepeat)의 정의와 거의 동일하지만 type parameter가 추가된 걸 볼 수 있습니다. Parameter가 하나 늘어나니까 type annotation도 길어졌네요. 다행히도 Coq에서는 type annotation을 생략할 수 있습니다. 아래를 봅시다.

## Type Inference

```haskell, line_num
Fixpoint repeat X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.
```

이전에 정의했던 repeat과 방금 정의한 repeat은 완벽히 동일한 함수입니다. 혹시나해서 type annotation의 일부만 생략해봤습니다. 아래처럼요.

```haskell, line_num
Fixpoint repeat X (x : X) count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.
```

이렇게 해도 지금까지 정의했던 함수와 동일하게 정의됩니다.

## Type inference with holes

방금 정의한 repeat을 자세히 보면 `Cons X x (repeat X x count')`라는 구절이 있습니다. Recursive한 call에서 type parameter가 `X`인 건 자명한데, 저걸 생략할 순 없을까요? 있습니다.`_`를 쓰면 Coq가 `_` 자리에 들어갈 type parameter를 추론[^chch]해서 집어넣습니다.

[^chch]: Coq는 맞는 추론만 하니까 걱정 안하셔도 됩니다.

```haskell, line_num
Fixpoint repeat X (x : X) count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat _ x count')
  end.
```

이전의 구현에서 `X`를 전부 `_`로 대체한 코드입니다. 저렇게 짜도 아무 문제없이 돌아갑니다. 이렇게 보면 `X`라고 쓰나 `_`라고 쓰나 별 차이가 없는 것 같지만 이름이 길 경우 얘기가 달라집니다.\
`cons nat 1 (cons nat 2 (cons nat 3 (nil nat)))`를\
`cons _ 1 (cons _ 2 (cons _ 3 (nil _)))`로 대체한다고 생각해보세요.

## Implicit Arguments

Type parameter 쓰는게 귀찮아서 생략하거나 `_`를 썼습니다. 만약 `_`를 쓰기도 귀찮고 매번 생략할지 말지 고민하기도 귀찮다면요? Coq가 항상 type parameter를 추론하기를 바라면 어떻게해야 할까요?

[[anchor, id = keyword arguments]][[/anchor]]

```haskell, line_num
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
```

위와 같이 `Arguments` 키워드를 쓰면 됩니다. `Arguments` 키워드에 함수 혹은 type 정의의 이름을 넣고 그 뒤에 implicit하게 쓰고 싶은 인수들의 이름을 중괄호 안에 넣으면, Coq가 해당 인수들은 항상 추론합니다.\
즉, 위와 같이 선언을 해두면 `cons 1 (cons 2 (cons 3 nil))`라고만 해도 Coq가 자동으로 list의 type을 추론합니다.

아래와 같이 함수 정의 안에 implicit arguments를 선언할 수도 있습니다.

```haskell, line_num
Inductive list {X : Type} : Type :=
  | nil
  | cons (x : X) (l : list).

Fixpoint repeat {X : Type} (x : X) (count : nat) : list :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.
```

인수를 정의하는 자리에 소괄호대신 중괄호를 써서 implicit argument를 선언할 수 있습니다.

[[box]]

Implicit argument가 어떤 식으로 구현돼 있는지 궁금해서 더 실험을 해보았습니다. 각 argument의 정의에 따라 CoqIDE가 어떻게 반응하는지를 아래에 정리해보았습니다.

- `{X : Type} (x : X) (count : nat)`
  - 위의 설명에서 쓰인 정의입니다. 잘 동작합니다.
- `(x : X) (count : nat) {X : Type}`
  - `{X : Type}`를 맨 뒤로 옮겨보았습니다.
  - 앞에 있는 `(x : X)`의 `X`가 정의되지 않았다고 에러가 뜹니다.
- `{X : Type} {x : X} (count : nat)`
  - `x`의 선언을 implicit하게 바꾸어보았습니다.
  -  [[red]]The term "x" has type "X" while it is expected to have type "nat".[[red]]라는 에러가 뜹니다.
- `{X : Type} (x : X) {count : nat}`
  - `count`의 선언을 implicit하게 바꾸어보았습니다.
  - 에러가 뜹니다.

Implicit argument를 응용하기는 아직 이른 것 같고 polymorphism을 구현하는 데에만 사용해야겠습니다.

[[/box]]

## Explicit Type Arguments

[[anchor, id = keyword at]][[/anchor]]

방금 봤던 중괄호 표시를 이용하면 Coq가 항상 type parameter를 추론하게 할 수 있습니다. 하지만, Coq가 type을 추론할 수 없는 상황도 있습니다. 그런 상황에선 어떻게 해야할까요? Type을 명시해줘야 하지만 type을 명시하지 않겠다고 이미 선언을 했는데요? Implicit argument 선언을 뒤집을 수 있는 문법이 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Fail Definition mynil_fail := nil.
Definition mynil := @nil nat.
```

위에서 `Arguments nil {X}.`이라고 선언을 했으므로 `nil nat`이라는 표현을 쓸 수는 없습니다. 하지만 그냥 `nil`이라고만 하면 Coq가 `nil`의 type을 알지 못해 에러가 납니다. 그럴 때 `@`를 `nil` 앞에 붙여서 `nil`이 type parameter를 받을 수 있도록 해주고 뒤에 type parameter를 주면 됩니다.

```haskell, line_num
Check @nil : forall X : Type, list X

Check nil : list where ?X : [ |- Type]
```

`nil`과 `@nil`의 type은 위와 같습니다. `nil`의 type은 무슨 뜻인지 아직 잘 모르겠네요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap3-4. Maps](Chap3-4.html)

[[/left]]

[[right]]

[Chap4-2. Higher Order Functions](Chap4-2.html) >>

[[/right]]