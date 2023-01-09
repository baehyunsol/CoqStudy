| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proof Rules

Hoare Logic으로 프로그램을 검증하기 위해선 간단한 정리들을 먼저 증명하고 시작해야합니다. 언제나 그랬듯이 간단한 정리들을 조합하여 복잡한 정리들을 증명하겠습니다.

## Skip

```haskell, line_num
Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP.
  inversion H;
  subst.
  assumption.
Qed.
```

먼저, `skip`을 하더라도 assertion이 변하지 않는다는 것을 증명했습니다.

## Sequencing

```haskell, line_num
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12;
  subst.
  eauto.
Qed.
```

어떤 명령어 `c1`과 `c2`에 대해서, `{P} c1 {Q}`이고 `{Q} c2 {R}`이면 `{P} c1;c2 {R}`이라는 것을 증명했습니다. 연속된 명령어는 각각의 명령어로 쪼갤 수 있다는 뜻이죠. [12-2 단원](Chap12-2.html#keywordauto)에서 배웠던 `auto`와 비슷한 `eauto`를 사용했습니다.

`hoare_seq`의 정의에 보면 `c2`가 `c1`보다 먼저 등장합니다. 윗 문단에서 한국어로 했던 정의와 순서가 반대네요. 왜 그럴까요? 보통 증명을 할 때 정보를 뒤에서부터 받기 때문입니다. 뒤에서도 더 보겠지만, 보통은 마지막 postcondition을 아는 상태에서 명령어를 반대로 받으면서 첫번째 precondition까지 거슬러 올라갑니다. 즉, `R`을 아는 상태에서 `c2`와 `c1`을 갖고 `P`를 관찰하는게 보편적입니다.

## Assignment

`{??} X := Y {X = 1}`라는 hoare triple을 생각해봅시다. precondition으로 들어갈 수 있는 건 뭐가 있을까요? `Y = 1`이 있겠네요. 말이 되긴 하지만 더 복잡한 상황에서도 일반화가 가능할까요? `{??} X := X + Y {X = 1}`에서는 precondition으로 뭐가 가능할까요? `X + Y = 1`이 가능하네요.

이제 일반화를 해봅시다. 방금 본 hoare triple들에서 대입의 좌변은 `X`, postcondition의 좌변도 `X`였습니다. 그때 precondition의 좌변에는 대입의 우변이 들어가고, precondition의 우변에는 postcondition의 우변이 들어갑니다. 이 규칙만 있으면 모든 대입 연산에 대해서 hoare triple을 만들 수 있습니다.

여기서 좀 더 일반화를 해봅시다. `{??} X := a {Q}`의 precondition으로 가능한 건 뭐가 있을까요? precondition에 `X`가 들어있었다면, `Q`에는 똑같은 자리에 `X` 대신 `a`가 들어있을 겁니다. 그걸 예쁘게 쓰면 `{Q [X |-> a]} X := a {Q}`가 됩니다. 안 예쁜가요? `Q [X |-> a]`는 ~_`Q`에서 `X`를 전부 없애고 그 자리에 `a`를 대신 써라_~라는 뜻입니다. Coq로 정의하면 아래와 같습니다.

```haskell, line_num
Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).
```

방금 한 얘기가 참이라는 걸 Coq으로 증명해보겠습니다. 아래를 봅시다.

```haskell, line_num
Theorem hoare_asgn: forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE.
  subst.
  unfold assn_sub in HQ.
  assumption.
  Qed.

Example assn_sub_example:
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.
  Qed.
```

## Consequences

Coq은 멍청합니다. `{(X = 3) [X |-> 3]} X := 3 {X = 3}`가 말이 되는 건 `hoare_asgn`을 이용해서 바로 증명이 되지만 `{True} X := 3 {X = 3}`은 안됩니다. 사람이 보기엔 둘이 같은 말인데 말이죠. Coq을 위해서 몇가지 정리를 추가해줍시다.

`{P} c {Q}`가 참일 때, 아래의 2가지도 참입니다.

- precondition이 강해지는 경우, 즉 `P' ->> P`일 때 `{P'} c {Q}`
- postcondition이 약해지는 경우, 즉 `Q ->> Q'`일 때 `{P} c {Q'}`

TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-1. Hoare Logic](Chap14-1.html)

[[/left]]

[[right]]

[Chapter 14-3. ??](Chap14-3.html) >>

[[/right]]