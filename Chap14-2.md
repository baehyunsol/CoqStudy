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

어떤 명령어 `c1`과 `c2`에 대해서, `{P} c1 {Q}`이고 `{Q} c2 {R}`이면 `{P} c1;c2 {R}`이라는 것을 증명했습니다. 연속된 명령어는 각각의 명령어로 쪼갤 수 있다는 뜻이죠. [12-2 단원](Chap12-2.html#keywordauto)에서 배웠던 `auto`와 비슷한 `eauto`를 사용했습니다. `eauto`의 설명은 [아래](#keywordeauto)에 자세하게 있습니다.

`hoare_seq`의 정의에 보면 `c2`가 `c1`보다 먼저 등장합니다. 윗 문단에서 한국어로 했던 정의와 순서가 반대네요. 왜 그럴까요? 보통 증명을 할 때 정보를 뒤에서부터 받기 때문입니다. 뒤에서도 더 보겠지만, 보통은 마지막 postcondition을 아는 상태에서 명령어를 반대로 받으면서 첫번째 precondition까지 거슬러 올라갑니다. 즉, `R`을 아는 상태에서 `c2`와 `c1`을 갖고 `P`를 관찰하는게 보편적입니다.

`hoare_seq`를 그림으로 나타내보면 아래와 같이 나타낼 수도 있습니다.

```line_num, copy_button(false)
    { P } c1 { Q }
    { Q } c2 { R }
-------------------------
  { P } c1;c2 { R }
```

가로선 위에 있는 hoare triple들이 참이면 아래도 참이라는 뜻입니다. 앞으로 자주 나올 그림이니 익숙해집시다.

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

-  precondition이 강해지는 경우, 즉 `P' ->> P`일 때 `{P'} c {Q}`
- postcondition이 약해지는 경우, 즉 `Q ->> Q'`일 때 `{P} c {Q'}`

직관적으론 말이 되죠? Coq으로 저 2가지를 증명해보겠습니다.

[[anchor, id = pre1]][[/anchor]]

```haskell, line_num
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros p p' q c H0 H1 st st' H2 H3.
  apply H0 with st. (*{- H0: {p'} c {q} -}*)
  - (*{- st =[ c ]=> st' -}*)
    apply H2. (*{- H2: st =[ c ]=> st' -}*)
  - (*{- p' st -}*)
    apply H1. (*{- H1: p ->> p' -}*)
    apply H3. (*{- H3: p st -}*)
  Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros p q q' c H0 H1 st st' H2 H3.
  apply H1. (*{- H1: q' ->> q -}*)
  apply H0 with st. (*{- H0: {p} c {q'} -}*)
  - (*{- st =[ c ]=> st' -}*)
    apply H2. (*{- H2: st =[ c ]=> st' -}*)
  - (*{- p st -}*)
    apply H3. (*{- H3: p st -}*)
  Qed.
```

증명은 간단합니다. 증명의 목표는 context의 어떤 명제와 goal의 모양이 같도록 만드는 것이고, context에 있는 명제들을 잘 `apply`해서 goal의 모양을 적절히 바꾸면 됩니다.

```haskell, line_num
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - (*{- {P'} c {Q} -}*)
    apply hoare_consequence_post with (Q' := Q').
    + (*{- {P'} c {Q'} -}*)
      assumption.
    + (*{- Q' ->> Q -}*)
      assumption.
  - (*{- P ->> P' -}*)
    assumption.
  Qed.
```

pre와 post를 하나로 합친 정리입니다.

이번에도 그림으로 나타내보면 아래처럼 나옵니다.

```line_num, copy_button(false)
    {P'} c {Q}
      P ->> P'
-------------------
     {P} c {Q}
```

```line_num, copy_button(false)
    {P} c {Q'}
      Q' ->> Q
-------------------
     {P} c {Q}
```

```line_num, copy_button(false)
    {P'} c {Q'}
      P ->> P'
      Q' ->> Q
-------------------
     {P} c {Q}
```

## 증명 자동화, `eauto`와 `eapply`, `LTac`

[이전](Chap12-2.html#keywordauto)에 `auto`라는 tactic에 대해서 배웠죠? `intros`와 `apply`로만 이뤄진 증명은 `auto`로 한방에 끝낼 수 있습니다. 방금 본 `hoare_consequence_pre`도 역시 `intros`와 `apply`, `assumption`으로만 이뤄져있습니다. `assumption`도 `apply`의 간략화된 버전이니 `auto`를 쓸 수 있겠네요?

먼저 아래의 코드를 추가해줍시다.

```haskell, line_num
Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.
```

Coq가 `auto`를 쓸 때 저 정리들도 참고하라고 알려주는 것입니다. 이제 `auto`를 써보면...

```haskell, line_num
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto.
  Abort.
```

오잉...?? 증명이 되지 않습니다! 왜냐면 `hoare_consequence_pre`에 들어간 tactic은 `apply`가 아니고 `apply with`거든요. `auto`는 `apply with`를 만나면 `with` 뒤에 뭘 넣을지 판단하지 못합니다. 저 판단을 도와주는 `eapply`와 `eauto`에 대해서 알아보겠습니다.

### `eapply`

[[anchor, id = keyword eapply]][[/anchor]]

먼저, `eapply`부터 봅시다. `apply X with Y`을 했지만 정작 `Y`가 필요없는 경우가 많습니다. 그냥 아무 값이나 넣어두고 증명을 진행할 순 없을까요? 그럴 때 사용하는게 바로 `eapply`입니다. 아래의 코드를 [위](#pre1)와 비교해봅시다.

```haskell, line_num
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros p p' q c H0 H1 st st' H2 H3.
  eapply H0.
  - (*{- ?st =[ c ]=> st' -}*)
    apply H2. (*{- H2: st =[ c ]=> st' -}*)
  - (*{- p' st -}*)
    apply H1. (*{- H1: p ->> p' -}*)
    apply H3. (*{- H3: p st -}*)
  Qed.
```

나머지는 그대로고 7번줄의 `apply H0 with st`만 `eapply H0`로 바뀌었습니다. 어차피 `st`에 뭐가 들어가든 상관이 없거든요.

### `eauto`

[[anchor, id = keyword eauto]][[/anchor]]

`eapply`와 `intros`로만 이뤄진 증명은 `eauto`로 자동화할 수 있습니다.

```haskell, line_num
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
  Qed.
```

좋아요.

### `Ltac`

[[anchor, id = keyword ltac]][[/anchor]]

본격적으로 `Ltac`을 다루기 전에, 아까 정의한 것들로 예시를 몇가지 만들어보겠습니다.

```haskell, line_num
Example hoare_asgn_example1:
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - (*{- {?P'} X := 1 {X = 1} -}*)
    eapply hoare_asgn.
  - (*{- True ->> {(X = 1) [X |-> 1]} -}*)
    intros st true_p.
    simpl.
    reflexivity.
  Qed.
```

`hoare_asgn`만 가지고는 위의 정리를 증명할 수 없습니다. `True`랑 `1 = 1`이랑 같은 말인 거 같지만 Coq은 그렇게 생각 안하거든요. 그래서 `hoare_consequence_pre`를 이용해서 `True`면 `1 = 1`이라고 Coq한테 알려줬습니다.

```haskell, line_num
Example assn_sub_example2:
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - (*{- {?P'} X := X + 1 {X < 5} -}*)
    apply hoare_asgn.
  - (*{- X < 4 ->> {(X < 5) [X |-> X + 1]} -}*)
    unfold "->>", assn_sub, t_update.
    intros st H.
    simpl in *.
    lia.
  Qed.
```

이번에도 비슷한 증명을 했습니다. `lia`는 `->>`나 `|->` 같은 기호를 이해하지 못하기 때문에 10번 줄에서 전부 `unfold`하고 시작했습니다. 하다보니까 비슷한 tactic이 반복해서 나오죠? 저런 tactic들을 하나로 묶으려면 어떻게 할까요? 바로 `Ltac`을 사용하면 됩니다.

```haskell, line_num
Ltac assn_auto :=
  try auto;
  try (
    unfold "->>", assn_sub, t_update;
    intros;
    simpl in *;
    lia
  ).
```

`assn_auto`라는 tactic을 정의했습니다. 바로 사용해보겠습니다.

```haskell, line_num
Example assn_sub_example2':
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example hoare_asgn_example1':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.
```

좋아요.

`assn_auto`를 이용해서 증명을 하나 더 해보겠습니다.

```haskell, line_num
Example hoare_asgn_example :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  apply hoare_seq with (Q := (X = 1)%assertion).
  - (*{- {X = 1} Y := 2 {X = 1 /\ Y = 2} -}*)
    apply hoare_consequence_pre with (P' := ((X = 1 /\ Y = 2) [Y |-> 2])%assertion).
    + (*{- {(X = 1 /\ Y = 2) [Y |-> 2]} Y := 2 {X = 1 /\ Y = 2} -}*)
      apply hoare_asgn.
    + (*{- X = 1 ->> (X = 1 /\ Y = 2) [ Y |-> 2] -}*)
      assn_auto.
  - (*{- {True} X := 1 {X = 1} -}*)
    apply hoare_consequence_pre with (P' := ((X = 1) [X |-> 1])%assertion).
    + (*{- {(X = 1) [X |-> 1]} X := 1 {X = 1} -}*)
      apply hoare_asgn.
    + (*{- True ->> (X = 1) [X |-> 1] -}*)
      assn_auto.
  Qed.
```

방금 정의한 `assn_auto`를 사용했습니다. `eauto`나 `eapply`등을 사용하면 증명을 훨씬 더 간략하게 할 수 있지만 지금은 공부를 하는 입장이니 최대한 길게 썼습니다. 9번과 15번 줄에서 `P'`를 줄 때 `%assertion`이 없으면 Coq이 알아듣지를 못합니다. `X = 1`만 보고는 이게 Imp의 문법인지 Coq의 문법인지 모르거든요. 그래서 `%assertion`을 줬습니다.

[[anchor, id = keyword ampersand]][[/anchor]]

## Conditionals

if문을 가지고 hoare triple에 어떤 장난을 칠 수 있을까요?

```line_num, copy_button(false)
         {P} c1 {Q}
         {P} c2 {Q}
--------------------------------
  {P} if b then c1 else c2 {Q}
```

가장 쉽게 생각할 수 있는 경우는 위와 같습니다. 근데 어딘가 부족해보이죠? 저렇게 쓰면 [[giant]]~_조건_~[[/giant]]문의 특징을 전혀 못 살립니다. `b`가 참이든 거짓이든 신경쓰지를 않잖아요. 아래같은 예시를 생각해봅시다.

```line_num
{ True }
if X = 0
  then Y := 2
  else Y := X + 1
end
{ X <= Y }
```

너무 자명하게 참이지만 방금 만든 규칙으로는 증명이 불가능합니다. 좀더 조건문스럽게 규칙을 바꿔볼까요?

```line_num, copy_button(false)
        {P /\   b} c1 {Q}
        {P /\ ~ b} c2 {Q}
------------------------------------
  {P} if b then c1 else c2 end {Q}
```

이제 `b`가 참인지 거짓인지를 신경 씁니다. 더 많은 정보를 담고 있습니다. 한결 낫네요.

하지만 여전히 걸리는 점이 하나 있습니다. `P`는 assertion이고 `b`는 boolean이에요. 그래서 `P /\ b`는 말이 되지 않습니다. 저걸 어떻게 고쳐야할까요? 먼저 boolean을 assertion으로 고쳐주는 함수를 정의하겠습니다.

```haskell, line_num
Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.
Arguments bassn /.
```

단순히 함수만 정의한게 아니고 몇몇 특수문법을 추가했습니다. 이제 `Assertion`과 `bexp`를 섞어서 써도 Coq이 알아서 type을 바꿔줄 겁니다.

```haskell, line_num
Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  congruence.
  Qed.

Hint Resolve bexp_eval_false : core.
```

[[anchor, id = keyword congruence]][[/anchor]]

`bassn`에 관한 유용한 사실 하나도 증명했습니다. 이따 쓸 거 거든요. `congruence`라는 tactic이 나오는데 아주 간단한 tactic입니다. `congruence`는 `A = true`라는 가정과 `A = false`라는 가정이 동시에 있는 걸 확인하면 그 즉시 `discriminate`를 사용해서 증명을 끝내버립니다.

이제 `if`의 hoare triple을 증명해봅시다.

```haskell, line_num
Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 H1 H2 st st' H3 H4.
  inversion H3;
  eauto.
  Qed.
```

`eauto`를 쓰지 않고 해보려다가 도저히 안되겠어서 `eauto`로 했습니다... 어쨌든 `hoare_if`를 증명했으니 사용해봅시다.

```haskell, line_num
Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (*{- X = 0 -}*)
    apply (hoare_consequence_pre (True /\ <{X = 0}>)%assertion ((X <= Y) [Y |-> 2])%assertion (X <= Y)%assertion <{Y := 2}>).
    + (*{- {X <= Y [Y |-> 2]} Y := 2 {X <= Y} -}*)
      apply hoare_asgn.
    + (*{- True /\ X = 0 ->> X <= Y [Y |-> 2] -}*)
      unfold assert_implies, assn_sub, t_update, bassn.
      intros st.
      simpl in *.
      rewrite -> (eqb_eq (st X) 0).
      try lia.
  - (*{- X != 0 -}*)
    apply (hoare_consequence_pre (True /\ ~<{X = 0}>)%assertion ((X <= Y) [Y |-> X + 1])%assertion (X <= Y)%assertion).
    + (*{- {X <= Y [Y |-> X + 1]} Y := X + 1 {X <= Y} -}*)
      apply hoare_asgn.
    + (*{- True /\ X != 0 ->> X <= Y [Y |-> X + 1] -}*)
      unfold assert_implies, assn_sub, t_update, bassn.
      intros st.
      simpl in *.
      rewrite -> (eqb_eq (st X) 0).
      try lia.
  Qed.
```

`if`를 설명하기 위해 처음에 사용했던 예시를 증명했습니다. 비슷한 패턴이 반복되죠? 축약해봅시다.

```haskell, line_num
Ltac assn_auto :=
  unfold assert_implies, assn_sub, t_update, bassn;
  intros st;
  simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;
  auto;
  try lia.
```

아까 정의한 `assn_auto`를 좀 더 강력하게 다시 정의했습니다.

```haskell, line_num
Example if_example2 :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if;
  eapply hoare_consequence_pre;
  try apply hoare_asgn;
  try assn_auto.
  Qed.
```

아주 간단하죠?

## loops

`while`의 hoare triple에서는 어떤 정보를 뽑아낼 수 있을까요? 가장 먼저 떠오르는 모양은 아래와 같습니다.

```line_num
        {P} c {P}
--------------------------
 {P} while b do c end {P}
```

`c`를 한번 해도 `P`라는 assertion이 변하지 않는다면 `c`를 여러번 해도 마찬가지겠죠. 이걸 loop-invariant라고 부릅니다. 이것도 좋은 정보지만 loop에서 뽑아낼 수 있는 정보는 더 많습니다. 예를 들어서, `b`가 참이어지만 loop에 들어가고 loop에서 나올 때는 `b`가 거짓이겠죠. 그림으로 그리면 아래와 비슷하겠네요.

```line_num
            {P /\ b} c {P}
----------------------------------
  {P} while b do c end {P /\ ~b}
```

멋지네요. 증명해봅시다.

```haskell, line_num
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c H_hoare st st' H_while H_P.
  remember <{ while b do c end }> as while_.
  induction H_while;
  try (inversion Heqwhile_);
  subst;
  eauto.
  Qed.
```

그냥 `eauto`로 했습니다. `hoare_while`을 이용해서 간단한 증명 몇가지를 해보겠습니다.

```haskell, line_num
Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - (*{- {X <= 3} while_loop { X <= 3 /\ ~(X <= 2) } -}*)
    apply hoare_while.
    eapply hoare_consequence_pre.
    + (*{- {X <= 3 [X |-> X + 1]} X := X + 1 {X <= 3} -}*)
      apply hoare_asgn.
    + (*{- X <= 3 /\ X <= 2 ->> X <= 3 [X |-> X + 1] -}*)
      assn_auto.
  - (*{- X <= 3 /\ ~(X <= 2) ->> X = 3 -}*)
    assn_auto.
Qed.
```

아주 간단합니다. loop에서 나왔다는 거는 `X <= 2`라는 조건이 끝났다는 뜻이죠? `X`를 1씩 늘렸으니까 `X = 3`인 조건을 만족하면서 loop를 나오게 됩니다.

[[box]]

만약 `while`이 무한루프를 돈다면 hoare triple은 어떻게 될까요? `{P} while true do c end {Q}`의 경우 `Q`에 뭐가 오든 상관없이 hoare triple은 항상 참입니다.[^proof] 조금 이상하죠? 원래 hoare triple은 종료하는 명령어들에 대해서만 유효합니다. 어떤 명령어가 종료하는지 안하는지 증명을 하지 않을 경우 그 hoare triple은 부분적으로 유효하다고 (partial correctness) 합니다. 어떤 명령어가 무한루프에 빠지지 않는다는 걸 추가로 증명하면 그 hoare triple은 완전해집니다 (total correctness).

무한루프에 빠지지 않는다는 걸 증명하는 과정은 너무 복잡하니 생략하겠습니다.

[^proof]: 증명은 여백이 부족해서 생략했습니다.

[[/box]]

## 정리

증명을 하다보면 Imp 코드의 모양과 증명의 단계가 비슷하다는 것을 눈치채실 겁니다. 여러 단계로 돼 있는 코드를 `hoare_seq`을 이용해서 쪼개고, 대입을 만나면 `hoare_asgn`을 쓰고, `if`를 만나면 `hoare_if`를 쓰고, ...

이게 hoare logic의 핵심 중 하나입니다. 앞으로 Imp의 hoare triple과 관련된 증명을 할 때 Coq 수준으로 `unfold`를 하는 것이 [[giant]]아니라[[/giant]], 이번 장에서 증명한 정리들만 가지고 hoare triple을 쪼갤 수 있습니다. 다음 장부터 hoare triple을 갖고 노는 방법들을 자세히 살펴보겠습니다.

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