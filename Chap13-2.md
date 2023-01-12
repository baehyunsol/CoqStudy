| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Program Equivalence

이전 단원에서 `aequiv`, `bequiv`, `cequiv`를 살펴 봤습니다. 쟤네가 진짜 등호인지 볼까요? 등호는 3가지 아래의 성질이 성립합니다.

1. reflexivity : `a = a`
1. symmetry : `a = b -> b = a`
1. transitivity : `a = b -> b = c -> a = c`

`aequiv`와 `bequiv`, `cequiv`도 저 성질들이 성립하는지 볼까요?

```coq, line_num
Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st.
  reflexivity.
  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H st.
  symmetry.
  apply H.
  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv.
  intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st).
  rewrite (H23 st).
  reflexivity.
  Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  intros b st.
  reflexivity.
  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  intros b1 b2 H st.
  symmetry.
  apply H.
  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st).
  rewrite (H23 st).
  reflexivity.
  Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  intros c st st'.
  reflexivity.
  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv.
  intros c1 c2 H st st'.
  rewrite H.
  reflexivity.
  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv.
  intros c1 c2 c3 H12 H23 st st'.
  rewrite H12.
  apply H23.
  Qed.
```

모든 증명들을 첨부해두었습니다. Coq으로 직접 실행시켜보면서 공부해보세요. 또한, 나중에 저 정리들을 자주 쓸테니까 잘 기억해두시기 바랍니다.

## Congruence

또한 행동이 동일하면 congruence도 성립합니다. 작은 프로그램 2개가 동일하면 그 프로그램들이 포함된 큰 프로그램 2개도 동일하다는 뜻입니다. 아래의 표기를 보겠습니다.

```
        aequiv a a'
-------------------------
cequiv (x := a) (x := a')


     cequiv c1 c1'
     cequiv c2 c2'
-----------------------
cequiv (c1;c2) (c1';c2')
```

위는 congruence의 예시인데, 예를 들어서 `a`와 `a'`가 동일하면 `x := a`와 `x := a'`도 동일합니다. 아래에서 증명을 보겠습니다.

```coq, line_num
Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' H st st'.
  split;
  intros H2;
  inversion H2;
  subst;
  apply E_Asgn;
  rewrite H;
  reflexivity.
  Qed.
```

Congruence는 별거 없어 보이지만 아주 중요합니다. 아주 큰 프로그램을 가지고 증명을 진행한다고 생각해보세요. 가정들을 적고 이름을 관리하는 것만 해도 머리가 아픕니다. 하지만 큰 프로그램들을 작은 프로그램들로 나눠서 작은 증명들을 한 뒤, 그 증명들을 합칠 수 있다고 생각하면 마음이 편해집니다. 뒤에서도 계속 나오는 내용이니 잘 봐둡시다.

```coq, line_num
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2 st st'.
  split;
  intros H3;
  inversion H3;
  subst.
  - (* c1 -> c1' *)
    assert (H5: st =[ c1' ]=> st'0).
      { apply H1. apply H4. }
    assert (H6: st'0 =[ c2' ]=> st').
      { apply H2. apply H7. }
    apply (E_Seq c1' c2' st st'0 st' H5 H6).
  - (* c1' -> c1 *)
    assert (H5: st =[ c1 ]=> st'0).
      { apply H1. apply H4. }
    assert (H6: st'0 =[ c2 ]=> st').
      { apply H2. apply H7. }
    apply (E_Seq c1 c2 st st'0 st' H5 H6).
  Qed.
```

또다른 congruence를 증명해보았습니다. 증명의 핵심은 `E_Seq`를 적용하는 것입니다. `E_Seq`이 필요로하는 인수들을 `assert`를 이용해서 만들어줬습니다.

```coq, line_num
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  intros b b' c1 c1' c2 c2' H1 H2 H3 st st'.
  split;
  intros H4;
  inversion H4;
  subst.
  - (* b -> b', b = true *)
    assert (H5: beval st b' = true).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c1' ]=> st').
    { apply H2. apply H9. }
    apply (E_IfTrue st st' b' c1' c2' H5 H6).
  - (* b -> b', b = false *)
    assert (H5: beval st b' = false).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c2' ]=> st').
    { apply H3. apply H9. }
    apply (E_IfFalse st st' b' c1' c2' H5 H6).
  - (* b' -> b, b' = true *)
    assert (H5: beval st b = true).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c1 ]=> st').
    { apply H2. apply H9. }
    apply (E_IfTrue st st' b c1 c2 H5 H6).
  - (* b' -> b, b' = false *)
    assert (H5: beval st b = false).
    { rewrite <- H8. rewrite H1. reflexivity. }
    assert (H6: st =[ c2 ]=> st').
    { apply H3. apply H9. }
    apply (E_IfFalse st st' b c1 c2 H5 H6).
  Qed.
```

이번에는 `if`에 대해서도 증명해보았습니다. 역시나 방식은 똑같습니다. 최종목표는 `E_IfTrue`와 `E_IfFalse`를 만드는 것인데, 거기에 필요한 인수들을 먼저 `assert`를 이용해서 만들고, 최종적으로 `E_IfTrue`/`E_IfFalse`를 만들어서 적용시켰습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 13-1. Behavioral Equivalence](Chap13-1.html)

[[/left]]

[[right]]

[Chapter 13-3. Program Transformation](Chap13-3.html) >>

[[/right]]