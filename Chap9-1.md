| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Curry Howard Correspondence

지금까지 Coq을 이용해서 증명을 하는 법들도 배웠고 프로그래밍을 하는 법도 배웠습니다. 이전의 단원들에서는 둘을 다른 것처럼 다뤘습니다. 과연 둘은 완전 분리된 개념일까요? 그렇지 않습니다. `Inductive`를 이용해서 `bool`과 `ev`를 둘 다 정의할 수 있던 건 우연이 아닙니다. 함수의 type을 `nat -> nat`이라고 쓰고 ~_p이면 q이다_~를 `p -> q`라고 썼죠? 둘 다 `->`가 들어가는 것도 우연이 아닙니다.

Coq의 증명을 프로그래밍에 비유해보겠습니다. [7장](Chap7-2.html#refevidence)에서 증거라는 개념을 배웠죠? 증명은 증거로 이뤄져있습니다. 예를 들어서 `A->B`의 증명은 `A`의 증거를 `B`의 증거로 바꾸는 과정이라고 생각할 수 있습니다. 여기서 우리는 아래와 같은 대응 관계를 얻을 수 있습니다.

| Coq 증명                 | 프로그래밍  |
|--------------------------|-------------|
| 증거                     | 값 (1, 2, 3...)  |
| `Prop`들                 | type (int, float...)  |
| 증명 (증거들의 tree)      | 자료구조      |

위의 대응관계를 이용해서 Coq 코드를 다시 읽어보겠습니다.

```haskell, line_num
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

`:`를 뭐라고 읽어야할까요? `(n: nat)`의 `:`는 ~_has type_~이라고 읽는게 적당합니다. 즉, `(n: nat)`은 ~_`n` has type `nat`_~이라고 읽습니다. 아래에서는요? `ev_0 : ev 0`의 `:`는 ~_is a proof of_~라고 읽습니다. 즉, `ev_0 : ev 0`는 ~_`ev_0` is a proof of `ev 0`_~라고 읽습니다.

첫번째 해석은 익숙하겠지만, 두번째 해석은 좀 낯설 수 있습니다. 또한, 첫번째 해석과 두번째 해석이 결과적으로 같은 말이라는 사실을 받아들이기는 더 어려울 수 있습니다. 이번 단원에서는 저 두 해석이 왜 동일한지 쭉 살펴보겠습니다.

> 방금 본 대응관계를 *Curry-Howard correspondence*라고 합니다.

## Proof Object

방금 본 대응관계를 이용해서 `ev`를 더 자세하게 살펴보겠습니다.

```haskell, line_num
Check ev_SS : forall n : nat, ev n -> ev (S (S n)).
```

`ev_SS`의 type은 위와 같습니다. 저걸 대응관계에 넣어서 풀어보면 "`ev_SS`는 자연수 `n` 하나와 증거 `ev n` 하나를 받는 함수이며, 반환하는 값은 `ev (S (S n))`이라는 명제의 증거이다."라고 읽힙니다.

같은 맥락에서, 아래의 세 증명은 완전히 동일합니다.

```haskell, line_num
Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
  Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2).
  apply (ev_SS 0).
  apply (ev_0).
  Qed.

Theorem ev_4'' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 (ev_0))).
  Qed.

Print ev_4.   (*{- ev_4   = ev_SS 2 (ev_SS 0 ev_0) : ev 4 -}*)
Print ev_4'.  (*{- ev_4'  = ev_SS 2 (ev_SS 0 ev_0) : ev 4 -}*)
Print ev_4''. (*{- ev_4'' = ev_SS 2 (ev_SS 0 ev_0) : ev 4 -}*)
```

[6-4 단원](Chap6-4.html)에서 `apply`에 인수를 줄 수도 있고 안 줄 수도 있는 걸 봤죠? 그때는 `apply` 뒤에 함수가 왔고 이번엔 `ev`가 왔지만 `ev`와 함수는 본질적으로 동일합니다. `ev`도 인수를 받아서 증거를 반환하거든요. `ev`들이 반환하는 증거가 모여서 `ev 4`가 되면 증명이 끝납니다.

이것은 Coq가 내부적으로 동작하는 원리와도 연관돼 있습니다. `ev 4`를 증명하고 싶다고 하면 Coq는 ***`ev 4`라는 type을 가진*** Proof Object를 만듭니다. (type이 저렇게 생겼습니다!) 그리고 그 proof object를 증명하기 위한 모든 증거를 다 제공하면 증명이 끝납니다. 각 과정에서 proof object의 모양을 보고 싶으면 `Show Proof`라는 명령어를 쓰면 됩니다.

[[anchor, id = keyword show proof]][[/anchor]]

```haskell, line_num
Theorem ev_4 : ev 4.
Proof.
  Show Proof.   (*{- ?Goal -}*)
  apply ev_SS.
  Show Proof.   (*{- (ev_SS 2 ?Goal) -}*)
  apply ev_SS.
  Show Proof.   (*{- (ev_SS 2 (ev_SS 0 ?Goal)) -}*)
  apply ev_0.
  Show Proof.   (*{- (ev_SS 2 (ev_SS 0 ev_0)) -}*)
  Qed.
```

위와 같이 증명이 진행되는 과정을 Coq가 보여줍니다.

## Dependent Types

또다른 proof object를 살펴보겠습니다.

```haskell, line_num
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  Show Proof.   (*{- ?Goal -}*)
  intros n H.
  Show Proof.   (*{- (fun (n : nat) (H : ev n) => ?Goal) -}*)
  simpl.
  Show Proof.   (*{- (fun (n : nat) (H : ev n) => ?Goal : ev (4 + n)) -}*)
  apply ev_SS.
  Show Proof.   (*{- (fun (n : nat) (H : ev n) => ev_SS (S (S n)) ?Goal : ev (4 + n)) -}*)
  apply ev_SS.
  Show Proof.   (*{- (fun (n : nat) (H : ev n) => ev_SS (S (S n)) (ev_SS n ?Goal) : ev (4 + n)) -}*)
  apply H.
  Show Proof.   (*{- (fun (n : nat) (H : ev n) => ev_SS (S (S n)) (ev_SS n H) : ev (4 + n)) -}*)
Qed.
```

Proof object 자체의 내용은 크게 중요하지 않고, 복습을 위해서 적어보았습니다. 이번에 중요하게 살펴볼 것은 위 표현의 type들입니다. 우리가 증명하고자 하는 것의 type은 함수입니다. `forall n`과 증거 `ev n`을 받아서 또다른 증거 `ev (4 + n)`을 내놓습니다.

동일한 식을 다른 표현 방식으로 나타내보겠습니다. 아래를 봅시다.

```haskell, line_num
Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).
Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
```

`ev_plus4`와 `ev_plus4'`, `ev_plus4''`는 전부 동일한 식을 다른 표현으로 나타낸 것입니다.

- `ev_plus4'`는 `Theroem`이 아닌 `Definition`을 이용해서 나타냈습니다. `ev_plus4`의 증명이 최종적으로 만드는 proof object를 `:=` 옆에 한번에 적어버렸네요.
- `ev_plu4''`는 좀 더 함수스러운 형식으로 표현을 했습니다. `nat` 하나와 `ev n` 하나를 받아서 `ev (4 + n)`을 내놓는 type의 함수를 정의하고, 그 정의에는 proof object를 그대로 적었습니다.

`ev n`과 `ev (4 + n)`이 그 자체로 type인 점이 신기합니다. 왜냐하면 `n`은 함수의 첫번째 ~_인수_~거든요. 이런 type들을 *dependent type*이라고 부릅니다. 보통의 프로그래밍 언어에선 거의 쓰이지 않지만 함수형 언어들은 요긴하게 써먹습니다.

### `forall`과 `->`

방금 본 예제에서 (`ev_plus4'`와 `ev_plus4''`), `->`과 `forall`의 관계에 주목해봅시다. 얼핏 생각해보면 두 표현은 관련이 있어 보입니다. ~_모든 자연수에 대해, P이다_~라는 표현과 ~_자연수이면 P이다_~라는 표현은 같은 말 같거든요. 실제로도 그렇습니다. 아래에서 구체적인 예시를 보겠습니다.

```haskell, line_num
Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).
```

`ev_plus2`와 `ev_plus2'`, `ev_plus2''`는 동일한 정의입니다.

`ev_plus2`는 `forall`만을 이용한 정의입니다. `ev n`을 만족하는 모든 `n`이 `ev (n + 2)`도 만족한다는 뜻이죠. 근데 `E`를 보면 정의만 됐을 뿐, 언급되지 않습니다. 언급되지 않을 객체에 이름을 붙이는 건 낭비 같죠? 그래서 `ev_plus2'`에서는 `_`라는 빈 이름을 사용했습니다. 이렇게 써보니 `forall`과 `_`를 같이 사용하는 방식도 낭비 같습니다. 그래서 나온 표현이 가장 아래의 `->`를 사용한 표현입니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap8-2. Partial Maps](Chap8-2.html)

[[/left]]

[[right]]

[Chap9-2. Logical Connectives as Inductive Types](Chap9-2.html) >>

[[/right]]