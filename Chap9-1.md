| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Curry Howard Correspondence

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

> 방금 본 대응관계를 *Curry-Howard correspondence*라고 합니다.

## Proof Object

방금 본 대응관계를 이용해서 `ev`를 더 자세하게 살펴보겠습니다.

```haskell, line_num
Check ev_SS : forall n : nat, ev n -> ev (S (S n)).
```

`ev_SS`의 type은 위와 같습니다. 저걸 대응관계에 넣어서 풀어보면 "`ev_SS`는 자연수 `n` 하나와 evidence `ev n` 하나를 받는 함수이며, 반환하는 값은 `ev (S (S n))`이라는 명제의 evidence이다."라고 읽힙니다.

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

[6-4 단원](Chap6-4.html)에서 `apply`에 인수를 줄 수도 있고 안 줄 수도 있는 걸 봤죠? 그때는 `apply` 뒤에 함수가 왔고 이번엔 `ev`가 왔지만 `ev`와 함수는 본질적으로 동일합니다. `ev`도 인수를 받아서 evidence를 반환하거든요. `ev`들이 반환하는 evidence가 모여서 `ev 4`가 되면 증명이 끝납니다.

이것은 Coq가 내부적으로 동작하는 원리와도 연관돼 있습니다. `ev 4`를 증명하고 싶다고 하면 Coq는 ***`ev 4`라는 type을 가진*** Proof Object를 만듭니다. (type이 저렇게 생겼습니다!) 그리고 그 proof object를 증명하기 위한 모든 evidence를 다 제공하면 증명이 끝납니다. 각 과정에서 proof object의 모양을 보고 싶으면 `Show Proof`라는 명령어를 쓰면 됩니다.

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

## WIP

WIP

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