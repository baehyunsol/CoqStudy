| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Program Transformation

이번 장에서는 프로그램의 변환을 보겠습니다. 프로그램 변환은 말그대로 프로그램 (`aexp`, `bexp` 혹은 `com`)을 다른 프로그램으로 바꾸는 것입니다. 예를 들어서 constant folding이라는 컴파일러 최적화를 생각해봅시다. 프로그래머가 `3 + 4` 혹은 `4 - 5`와 같은 코드를 입력할 경우, 저 값들은 컴파일러가 미리 계산할 수 있습니다. 굳이 실행 시간에 덧셈이나 뺄셈을 하는 건 시간낭비겠죠? 저런 식으로 상수로만 된 식들을 컴파일러가 미리 계산하는 걸 constant folding이라고 합니다. Imp에서의 constant folding을 구현해보겠습니다.

```coq, line_num
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ a1 + a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.
```

`fold_constants_aexp`는 모든 형태의 `aexp`를 뜯어서 상수와 상수의 연산을 찾으면 걔를 미리 계산합니다. `aexp`에 대해서 상수를 계산할 수 있으면 이걸 토대로 `bexp`에 대해서도 constant folding을 정의할 수 있습니다. 아래를 봅시다.

```coq, line_num
Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.
```

`bexp`는 비교 연산자들입니다. 비교를 하는 양변이 상수이면 결과가 `true`인지 `false`인지 미리 알 수 있으므로 그걸 컴파일 시간에 계산합니다. 이제 `aexp`와 `bexp`를 미리 계산할 수 있으니 이걸 토대로 `com`에 대해서도 constant folding을 정의할 수 있습니다.

```coq, line_num
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}> => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.
```

`com`의 경우는 더 간단합니다. `com`의 내부에서 `aexp`나 `bexp`가 등장하는 부분들은 전부 constant folding 안에 넣었습니다.

지금까지 여러 종류의 최적화들을 정의해보았습니다. 과연 저 최적화들은 타당할까요? 저 최적화를 해서 프로그램의 동작이 바뀌는 건 아닐까요? 이런 걱정을 덜어주기 위해서 Coq로 최적화의 타당성을 검증해보겠습니다.

## Program Transformation Soundness

먼저 transformation soundness를 정의하겠습니다.

```coq, line_num
Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).
```

정의에서 보듯, 변환 전의 프로그램과 변환 후의 프로그램이 동일하면 그 변환은 타당합니다. 모든 정의들이 다 됐으니 constant folding이 타당한 최적화인지 검증해봅시다.

### aexp soundness

```coq, line_num
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  intros a st.
  induction a;
  simpl;
  try reflexivity;
  try (
    destruct (fold_constants_aexp a1);
    destruct (fold_constants_aexp a2);
    rewrite IHa1;
    rewrite IHa2;
    reflexivity
  ).
  Qed.
```

먼저 `aexp`부터 증명했습니다. 저 증명을 Coq에 돌려도 무슨 일이 일어나는지 알기 매우 힘드므로 한 줄씩 뜯어보겠습니다. 5번 줄에서 `induction a`를 하면 `a`를 `aexp`의 5가지 경우 (상수, 변수, 덧셈, 뺄셈, 곱셈)로 나눕니다. 상수와 변수의 경우는 7번줄의 `reflexivity`만으로 증명이 끝납니다. 하지만 나머지 경우들은 그렇지 않아요. 6번 줄의 `simpl`은 `aexp`의 연산을 쪼갭니다. 예를 들어 곱셈의 경우 `a1 * a2`로 쪼갠 다음에 `a1`과 `a2`가 같음을 증명하라고 요구합니다. `a1`과 `a2`는 각각 `aexp`이기 때문에 5가지씩의 경우가 있어요. 그 경우들을 다시 9번 줄과 10번 줄의 `destruct`가 쪼갭니다. 이렇게 다 쪼개고 나면 goal의 좌변에는 `a1`, `a2`가 남고 우변에는 쪼개진 모양이 남습니다. 각 쪼개진 모양이 `a1`, `a2`와 같다는 얘기가 `IHa1`과 `IHa2`에 있으므로 모든 경우를 `rewrite`해서 증명이 끝납니다.

### bexp soundness

```coq, line_num
Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  intros b st.
  induction b.
  - (* BTrue *)
    reflexivity.
  - (* BFalse *)
    reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';
    destruct a2';
    try reflexivity.
    + (* a1' = n, a2' = n0 *)
      simpl.
      destruct (n =? n0);
      reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';
    destruct a2';
    try reflexivity.
    + (* a1' = n, a2' = n0 *)
      simpl.
      destruct (n =? n0);
      reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';
    destruct a2';
    try reflexivity.
    + (* a1' = n, a2' = n0 *)
      simpl.
      destruct (n <=? n0);
      reflexivity.
  - (* BGt *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';
    destruct a2';
    try reflexivity.
    + (* a1' = n, a2' = n0 *)
      simpl.
      destruct (n <=? n0);
      reflexivity.
  - (* BNot *)
    simpl.
    remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b';
    try reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1.
    rewrite IHb2.
    destruct b1';
    destruct b2';
    try reflexivity.
  Qed.
```

이번에는 `bexp`의 constant folding이 올바른지 확인해보았습니다. `BTrue`와 `BFalse`는 형태가 아주 단순하므로 `reflexivity`만 가지고 증명이 됐습니다.

[[anchor, id = keyword replace]][[/anchor]]

`BEq`의 경우, `simpl`을 하면 `fold_constants_aexp a1`이 포함된 아주 복잡한 식이 나옵니다. 거기서 `remember (fold_constants_aexp a1) as a1'`을 하면 `fold_constants_aexp a1`이 전부 `a1'`으로 대체됩니다. 또한, `a1' = fold_constants_aexp a1`이 context에 추가됩니다. 근데 `a1'`과 `fold_constants_aexp a1`은 동일하니까 식에 포함된 모든 `a1`은 `a1'`으로 대체할 수 있겠네요? 그러기 위해서 `replace _ with _`라는 tactic을 사용했습니다. `replace A with B`는 식에 포함된 모든 `A`를 `B`로 대체해줍니다. 저 대체가 가능하다는 근거를 `by` 뒤에 적어줘야 합니다.

식에 있는 모든 `fold_constants_aexp`를 없앤 다음에는 `destruct`를 이용해서 `a1'`, `a2'`의 모든 경우에 대해서 등호가 성립한다는 걸 보여야 합니다. `a1'` 혹은 `a2'`가 상수가 아닌 경우에는 `reflexivity`로 증명이 끝나고, `a1' = n, a2' = n0`인 경우에는 `n =? n0`의 경우들을 나눠서 각각 `reflexivity`를 쓰면 증명이 끝납니다.

대충 Coq 증명이 어떤 식으로 돌아가는지 감이 잡히기 시작하네요. `A = B`를 증명하고자 한다면, 이미 증명된 정리들을 사용하여 `A`와 `B`의 모양을 최대한 비슷하게 바꾸고 모든 경우에 대해서 등호가 성립함을 보이면 됩니다. ~_모든 경우_~를 보이기 위해선 보통 `induction`, `destruct`, `inversion`등을 이용해서 집합을 각 constructor들로 쪼갭니다.

`BNeq`, `BLe`, `BGt`도 `BEq`와 동일한 방식으로 증명이 가능합니다. `;`을 이용해서 식을 간략하게 만들 수 있을 거 같은데 책에선 왜 굳이 장황하게 썼는지 모르겠네요.

### cexp soundness

```coq, line_num
Theorem fold_constants_com_sound:
  ctrans_sound fold_constants_com.
Proof.
  intros c.
  induction c;
  simpl.
  - (* CSkip *)
    apply refl_cequiv.
  - (* CAsgn *)
    apply CAsgn_congruence.
    apply fold_constants_aexp_sound.
  - (* CSeq *)
    apply CSeq_congruence;
    assumption.
  - (* Cif *)
    assert (H: bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b);
    try (apply CIf_congruence; assumption).
    + (* b = true *)
      apply trans_cequiv with c1.
      apply if_true.
      apply H.
      apply IHc1.
    + (* b = false *)
      apply trans_cequiv with c2.
      apply if_false.
      apply H.
      apply IHc2.
  - (* CWhile *)
    assert (H: bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b);
    try (apply CWhile_congruence; assumption).
    + (* infinite loop *)
      apply while_true.
      assumption.
    + (* b = false *)
      apply while_false.
      assumption.
  Qed.
```

마찬가지로 `com`의 constant folding에 대해서도 증명해보았습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 13-2. Program Equivalence](Chap13-2.html)

[[/left]]

[[right]]

[Chapter 14-1. Hoare Logic](Chap14-1.html) >>

[[/right]]