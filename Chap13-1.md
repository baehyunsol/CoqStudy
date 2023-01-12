| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Behavioral Equivalence

[12단원](Chap12-1.html#optimizations)에서 최적화를 배울 때, 최적화를 하든 안하든 프로그램의 동작이 항상 동일하단 걸 증명했습니다. 동작의 동일성을 증명하는 것은 프로그램 검증에서 아주 중요한 부분인데요, 이번 단원에서는 동일성에 대해서 얘기를 해보겠습니다.

Imp에서 `X - X`와 `0`은 항상 동일한 값입니다... 항상 동일한 값일까요? 저게 동일한 값이면 `X - X = 0`과 `true`도 항상 동일한 값일까요? 이런 식으로 손과 머리만 써서 동일성을 검증하기엔 제약이 너무 많습니다. ~_동일함_~을 Coq으로 정의를 하고, 동일성을 Coq을 이용해서 확인해봅시다.

```coq, line_num
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.
```

먼저 `aeval`과 `beval`의 동일성을 정의했습니다. 저 정의를 갖고 `X - X`와 `0`이 동일한지 확인해봅시다.

```coq, line_num
Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st.
  simpl.
  lia.
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  reflexivity.
Qed.
```

Coq을 이용해서 `X - X`와 `0`은 항상 같다는 걸 증명했습니다.

`aequiv`와 `bequiv`는 값들의 동일성입니다. 값이 아니고 명령어끼리도 동일성을 증명할 순 없을까요? `b`가 항상 참이라면 `if b then c1 else c2`를 `c1`으로 갈아끼울 수 있습니다. 이런 식이면 컴파일러가 최적화하기 쉬울텐데 말이죠. 아래의 `cequiv`를 봅시다.

```coq, line_num
Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').
```

어떤 명령어 `c1`과 `c2`가 동일하다는 뜻은, 어떤 상태에서든지 `c1`의 실행결과와 `c2`의 실행결과가 동일하다는 뜻입니다. 저 정의를 갖고 방금 얘기한 명령어의 동일성을 증명해보겠습니다.

```coq, line_num
Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  intros c st st'.
  split;
  intros H.
  - (* skip;c -> c *)
    inversion H.
    subst.
    inversion H2.
    subst.
    assumption.
  - (* c -> skip;c *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.
```

13번 줄을 실행하고 나면 context에 `H5: st'0 =[ c ]=> st'`가 생기고 goal도 `st'0 =[ c ]=> st'`가 돼서 `assumption` tactic으로 손쉽게 처리할 수 있습니다. 원래대로면 `split`의 각 경우마다 첫 tactic은 `intros H`가 돼야 합니다. `intros H`를 2번 쓰기는 귀찮으니 [12-2 단원](Chap12-2.html#keywordsemicolon)에서 배웠던 `;`를 사용했습니다.

```coq, line_num
Theorem skip_right : forall c,
  cequiv
    <{ c; skip }>
    c.
Proof.
  intros c st st'.
  split;
  intros H.
  - (* c;skip -> c *)
    inversion H.
    subst.
    inversion H5.
    subst.
    assumption.
  - (* c -> c;skip *)
    apply E_Seq with st'.
    + (* st =[ c ]=> st' *)
      assumption.
    + (* st' =[ skip ]=> st' *)
      apply E_Skip.
  Qed.
```

반대방향으로도 가 보았습니다.

```coq, line_num
Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 H st st'.
  split;
  intros H2.
  - (* if -> c1 *)
    inversion H2;
    subst.
    + (* H7: st =[c1]=> st' *)
      assumption.
    + (* H7: st =[c2]=> st' *)
      rewrite H in H6.
      unfold beval in H6.
      discriminate.
  - (* c1 -> if *)
    apply E_IfTrue.
    + (* b = true *)
      apply H.
    + (* st =[c1]=> st' *)
      assumption.
  Qed.
```

첫 설명에서 언급했던 ~_`b`가 참이면 `if b then c1 else c2`는 `c1`과 동치이다_~ 의 증명입니다. 11번 줄에서 `inversion H2`를 하면 `b`가 참인 경우와 거짓인 경우로 나눠집니다. `b`가 참이면 `assumption`을 통해서 바로 증명이 되고 `b`가 거짓일 경우 context에 있는 `b = true`를 이용해서 가정을 깨서 증명을 끝냅니다.

19번 줄부터는 `c1`이 `if b then c1 else c2`와 같음을 증명합니다. `if`문에 `apply E_IfTrue`를 하면 두가지 증거를 요구합니다. 첫번째는 `b`가 참이라는 거고 두번째는 `st =[c1]=> st'`이라는 건데 둘 다 context에 있으니 그대로 써주면 됩니다.

```coq, line_num
Theorem if_false: forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 H st st'.
  split;
  intros H2.
  - (* if -> c2 *)
    inversion H2;
    subst.
    + (* H7: st =[ c1 ]=> st' *)
      rewrite H in H6.
      unfold beval in H6.
      discriminate.
    + (* H7: st =[c2]=> st' *)
      assumption.
  - (* c2 -> if *)
    apply E_IfFalse.
    + (* b = false *)
      apply H.
    + (* st =[c2]=> st' *)
      assumption.
  Qed.
```

이번에는 반대로 `b`가 `false`인 경우를 증명해봤습니다. 아까랑 거의 똑같은 증명입니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 12-3. States and Commands](Chap12-3.html)

[[/left]]

[[right]]

[Chapter 13-2. Program Equivalence](Chap13-2.html) >>

[[/right]]