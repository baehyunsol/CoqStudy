| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Regular Expressions

지금까지 봤던 `Inductive` 예제들은 너무 시시했습니다. `Fixpoint`로 정의한 `le`, `ev`와 큰 차이가 없었어요. 그래서 이번에는 `Inductive`를 이용해서 정규표현식을 정의해보겠습니다.

> 정규표현식이 뭔지 모르시는 분들은 이 단원은 넘어가도 무방합니다.

## reg_exp

```coq, line_num
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.
```

먼저 정규표현식 자체를 정의했습니다. `T`는 `Char`, 즉 각 글자들의 타입입니다.

- `EmptySet`: 아무 문자열에도 대응되지 않습니다.
- `EmptyStr`: `[]`, 즉 빈 문자열에 대응됩니다.
- `Char t`: 한 글자짜리 문자열입니다.
- `App r1 r2`: 유효한 문자열 2개의 합 (concatenation)입니다.
- `Union r1 r2`: 정규표현식의 `|`에 해당됩니다.
- `Star r`: 정규표현식의 `*`에 해당됩니다.

[[anchor, id=yogi]][[/anchor]]

여기서 사용한 `Inductive`는 `ev`, `le`를 정의할 때 사용한 `Inductive`보다는 `bool`, `bin`등을 정의할 때 사용한 `Inductive`에 가깝습니다. 즉, 7장에서 새로 본 `Prop`을 반환하는 `Inductive`가 아니고 [옛날](Chap1-1.html#keywordinductive)에 Rust의 enum에 비유하면서 설명했던 그 `Inductive`에 가깝습니다.

## exp_match

[[anchor, id=keyword reserved]][[/anchor]]

```line_num
Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).
```

다음으로는 각 정규표현식이 문자열과 대응되는 규칙을 정의했습니다. `[]`, `++` 등의 기호는 [이전](Chap3-2.html)에 list를 정의하면서 봤으니, 기억이 안 나시는 분들은 참고해주세요.

각 규칙들을 자세히 뜯어보겠습니다. 먼저, `s =~ re`라는 기호를 정의했습니다. `s`라는 문자열이 `re`라는 정규표현식에 대응된다는 뜻입니다. `exp_match`의 정의 안에서 `~=` 기호를 사용하기 위해서 `Reserved`라는 keyword를 사용했습니다.

또한 `exp_match`의 타입이 `list T -> reg_exp T -> Prop`이란 것도 주목할 필요가 있습니다. `exp_match`는 문자열과 정규표현식을 하나씩 받아서 둘이 대응이 되는지를 알려준다는 뜻입니다. [방금 전](#yogi)에 분류한 거에 따르면 전자의 정의에 가깝죠.

- `MEmpty`
  - 빈 문자열은 `EmptyStr`에 대응됩니다.
- `MChar x`
  - `x` 한 글자로 이뤄진 문자열은 `Char x`에 대응됩니다.
- `MApp s1 re1 s2 re2`
  - `s1`이라는 문자열은 `re1`이라는 정규표현식에 대응되고, `s2`이라는 문자열은 `re2`이라는 정규표현식에 대응될 때,
  - `s1 ++ s2`는 `App re1 re2`에 대응됩니다.
- `MUnionL s1 re1 re2`, `MUnionR re1 s2 re2`
  - `s1`이라는 문자열이 `re1`이라는 정규표현식에 대응되면 `s1`은 `Union re1 re2`에도 대응됩니다.
  - `Union`은 교환법칙이 성립하는데, 그걸 표현하기 위해서 `MUnionL`과 `MUnionR`을 따로 정의했습니다.
- `MStar0`
  - 모든 정규표현식 `re`에 대해서, 빈 문자열은 `Star re`에 대응됩니다.
- `MStarApp s1 s2 re`
  - 문자열 `s1`이 정규표현식 `re`에 대응되고, `s2`가 `Star re`에 대응되면 `s1 ++ s2`는 `Star re`에 대응됩니다.
  - 즉, `re`에 대응되는 문자열을 0번 이상 반복한 문자열은 `Star re`에 대응됩니다.

## 활용

방금 한 정의를 이용해서 간단한 증명 몇가지를 해보겠습니다.

### 간단한 정규식 대응

```coq, line_num
Example reg_exp_ex1 : [1] =~ Union (Char 1) (Char 2).
Proof.
  apply (MUnionL [1] (Char 1) (Char 2)).
  - (* [1] =~ Char 1 *)
    apply (MChar 1).
  Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] (Char 1) [2] (Char 2)).
  - (* [1] =~ Char 1 *)
    apply (MChar 1).
  - (* [2] =~ Char 2 *)
    apply (MChar 2).
Qed.
```

비슷한 형태의 증명을 2가지 했습니다. 먼저, 증명해야하는 식의 모양을 `MUnionL`과 `MApp`의 형태로 바꿨습니다. `MUnionL`과 `MApp`의 인수는 전부 적었습니다. `MUnionL`은 정의에 `H1: s1 =~ re1`가 있죠? `exp_match`를 하나 더 보이라고 요구합니다. 그래서 `apply`를 한번 더 써서 증명했습니다. `MApp`은 요구하는 추가로 `exp_match`가 2개여서 2번 했습니다.

책에는 저 식들이 훨씬 더 축약된 형태로 나와있습니다. 예를 들면 10번 줄을 `apply (MApp [1]).`이라고만 적어도 동일한 과정으로 증명이 끝납니다. 혹은, 5번과 12번, 14번 줄을 `apply MChar.`라고만 적어도 증명이 동일하게 진행됩니다. 처음에는 책의 축약된 형태만 보고 한참을 헤맸는데 여러분은 저처럼 헤매지 말라고 축약되지 않은 형태로 적었습니다. 익숙해지면 축약된 형태로 적겠습니다.

### EmptySet

```coq, line_num
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s.
  unfold not.
  intros H.
  inversion H.
  Qed.
```

`exp_match`의 정의에는 `EmptySet`과 대응시키는 규칙이 정의가 안 돼 있습니다. `EmptySet`과 대응되는 문자열은 존재하지 않기 때문이죠. 그걸 증명했습니다. 지난번에 배웠듯 `inversion` tactic은 해당되지 않는 경우들을 전부 알아서 `discriminate`해주기 때문에 증명이 바로 끝닙니다.

### `remember`

```coq, line_num
Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
```

`Star`는 합칠 수 있다는 것을 몇번의 시행착오를 거쳐서 증명해보겠습니다.

```coq, line_num
Proof.
  intros T s1 s2 re H.
  inversion H.
  - (* [] = s1 *)
    intros H1.
    simpl.
    apply H1.
  - (* s0 ++ s3 = s1 *)
    intros H4.
    rewrite H0.
    Abort.
```

첫번째 시도입니다. 실패했습니다.

단순히 `inversion`을 사용하려고 하면 중간에 막힙니다. `Abort`를 하는 순간 goal에는 `s1 ++ s2 =~ Star re`가 남아 있습니다. 즉, 처음과 완전히 동일한 형태의 식이 남아서 순환하게됩니다.

```coq, line_num
Proof.
  intros T s1 s2 re H.
  induction H as [].
  - (* s2 =~ EmptyStr -> [ ] ++ s2 =~ EmptyStr *)
    intros H1.
    simpl.
    apply H1.
  - (* s2 =~ Char x -> [x] ++ s2 =~ Char x *)
    Abort.
```

두번째 시도입니다. 하다보니까 조금 이상합니다. 분명 처음에는 `s1`, `s2`가 `Star`인 경우에 대해서만 얘기하고 있었는데 `EmptyStr`, `Char`, `App` 등등 모든 경우에 대해서 다 증명하고 있습니다. `induction` tactic이 `s1 =~ Star re`를 쪼개면서 정보들을 날려서 그렇습니다. 즉, `s1 =~ Star re`였다는 사실을 얘가 까먹은 겁니다.

`s1 =~ Star re`를 까먹었더라도 7가지 경우를 전부 증명해버리면 안되나? 라고 생각하실 수도 있습니다. 하지만 그것도 안 됩니다. `induction`을 하는 순간 `s1`이 7가지 종류의 `reg_exp`에 모두 대응됨을 보여야 합니다. 그게 `induction`이 하는 일이거든요. 하지만 `s1 =~ Star re`만 주어졌고 다른 관계들은 대응이 될지 안될지 모릅니다. 실제로 증명을 해보면 8번 줄에서 보듯 불가능한 증명이 나옵니다.

까먹은게 하나 더 있습니다. [지난](Chap5-3.html#keywordgeneralize) 번에 봤듯이 `forall` 2개를 동시에 `intros`를 해버리면 귀납법을 쓸 수가 없습니다. 그래서 둘 중 하나를 `generalize dependent`를 이용해서 일반화를 해줘야합니다.

[[anchor, id = keyword remember]][[/anchor]]

```coq, line_num
Proof.
  intros T s1 s2 re H.
  generalize dependent s2.
  remember (Star re) as re'.
  induction H as [].
  - (* EmptyStr = Star re *)
    discriminate.
  - (* Char X = Star re *)
    discriminate.
  - (* App re1 re2 = Star re *)
    discriminate.
  - (* Union re1 re2 = Star re *)
    discriminate.
  - (* Union re1 re2 = Star re *)
    discriminate.
  - (* Star re0 = Star re, s1 = [] *)
    intros s2 H.
    simpl.
    apply H.
  - (* Star re0 = Star re, s1 =~ re0 *)
    intros s0 H1.
    rewrite <- app_assoc.
    apply MStarApp.
    * (* s1 =~ re0 *)
      apply H.
    * (* s2 ++ s0 =~ Star re0 *)
      apply IHexp_match2.
      + (* Star re0 = Star re *)
        apply Heqre'.
      + (* s0 =~ Star re0 *)
        apply H1.
  Qed.
```

최종 증명입니다. 일단, _번 줄에서 `generalize dependent s2`를 통해서 `s2`를 `forall`로 만들어줬습니다. 또한, 4번 줄에서 `remember (Star re) as re'`라는 tactic을 사용했습니다. 이 덕분에 `s1 =~ Star re`라는 사실을 context가 기억합니다. 그 덕분에 6번 줄에서 context에 `EmptyStr = Star re`라는 조건이 들어가서 `discriminate` tactic을 사용할 수 있습니다. 똑같은 방식으로 `Star`를 제외한 모든 경우들을 지웠습니다. 그 다음에는 식의 형태에 맞게 `apply`를 적절히 사용하여 증명을 완료했습니다.

참고로 `app_assoc`은 `(s1 ++ s2) ++ s0`을 `s1 ++ s2 ++ s0`로 바꿔줍니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap7-2. Using Evidence in Proofs](Chap7-2.html)

[[/left]]

[[right]]

[Chap8-1. Total Maps](Chap8-1.html) >>

[[/right]]