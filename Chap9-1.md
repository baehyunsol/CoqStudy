| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proof Objects

지금까지 Coq을 이용해서 증명을 하는 법들도 배웠고 프로그래밍을 하는 법도 배웠습니다. 이전의 단원들에서는 둘을 다른 것처럼 다뤘습니다. 과연 둘은 완전 분리된 개념일까요? 그렇지 않습니다. `Inductive`를 이용해서 `bool`과 `ev`를 둘 다 정의할 수 있던 건 우연이 아닙니다. 함수의 type을 `nat -> nat`이라고 쓰고 ~_p이면 q이다_~를 `p -> q`라고 썼죠? 둘 다 `->`가 들어가는 것도 우연이 아닙니다.

Coq의 증명을 프로그래밍에 비유해보겠습니다. [7장](Chap7-2.html#refevidence)에서 evidence라는 개념을 배웠죠? 증명은 evidence로 이뤄져있습니다. 예를 들어서 `A->B`의 증명은 `A`의 evidence를 `B`의 evidence로 바꾸는 과정이라고 생각할 수 있습니다. 여기서 우리는 아래와 같은 대응 관계를 얻을 수 있습니다.

| Coq 증명                 | 프로그래밍  |
|--------------------------|-------------|
| evidence                 | 값 (1, 2, 3...)  |
| `Prop`들                 | type (int, float...)  |
| 증명 (tree of evidences) | 자료구조      |

위의 대응관계를 이용해서 Coq 코드를 다시 읽어보겠습니다.

```haskell, line_num
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

`:`를 뭐라고 읽어야할까요? `(n: nat)`의 `:`는 ~_has type_~이라고 읽는게 적당합니다. 즉, `(n: nat)`은 ~_`n` has type `nat`_~이라고 읽습니다. 아래에서는요? `ev_0 : ev 0`의 `:`는 ~_is a proof of_~라고 읽습니다. 즉, `ev_0 : ev 0`는 ~_`ev_0` is a proof of `ev 0`_~라고 읽습니다.

첫번째 해석은 익숙하겠지만, 두번째 해석은 좀 낯설 수 있습니다. 또한, 첫번째 해석과 두번째 해석이 결과적으로 같은 말이라는 사실을 받아들이기는 더 어려울 수 있습니다. 이번 단원에서는 저 두 해석이 왜 동일한지 쭉 살펴보겠습니다.

... TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap8-2. Partial Maps](Chap8-2.html)

[[/left]]

[[right]]

[Chap9-2. ??](Chap9-2.html) >>

[[/right]]