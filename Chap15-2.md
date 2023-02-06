| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Simply Typed Lambda Calculus

이 단원을 공부하기 전에 부록에 있는 [람다대수](lambda.html)를 먼저 읽고 오시는 걸 강력하게 권장드립니다.

이번에도 지난 단원들과 마찬가지로 간단한 언어를 정의한 뒤, 그 언어의 성질들을 위주로 살펴보겠습니다.

```line_num
t ::= x                         (variable)
    | \x:T,t                    (abstraction)
    | t t                       (application)
    | true                      (constant true)
    | false                     (constant false)
    | if t then t else t        (conditional)

T ::= Bool
    | T -> T
```

저희가 이번에 새로 정의할 언어입니다. `t`는 값이고 `T`는 타입입니다. 타입은 `Bool`과 함수의 2가지가 있습니다. 부록에서는 함수 정의에 `.`를 썼지만 여기선 `,`를 썼는데, 이는 Coq 문법의 `.`와의 충돌을 피하기위함입니다. 또한, 인수의 타입은 문법에 포함되지만 반환값의 타입은 적어주지 않습니다. 안 적어도 (무조건) 알 수 있거든요.

부록에서 봤던 함수들을 새로운 문법과 함께 다시 정의해보겠습니다.

- `\x:Bool, x`
  - 항등함수를 정의했습니다.
- `(\x:Bool, x) true`
  - 항등함수에 인수로 `true`를 줬습니다.
- `\x:Bool, if x then false else true`
  - `not` 함수입니다.
- `(\x:Bool, \y:Bool, x) false true`
  - 인수 2개를 받아서 첫번째 인수를 반환하는 함수를 만든 뒤, 인수 2개를 줬습니다.

TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 15-1. Basics](Chap15-1.html)

[[/left]]

[[right]]

[Chapter 15-3. TODO](Chap15-3.html) >>

[[/right]]