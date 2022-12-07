| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Regular Expressions

지금까지 봤던 `Inductive` 예제들은 너무 시시했습니다. `Fixpoint`로 정의한 `le`, `ev`와 큰 차이가 없었어요. 그래서 이번에는 `Inductive`를 이용해서 정규표현식을 정의해보겠습니다.

> 정규표현식이 뭔지 모르시는 분들은 이 단원은 넘어가도 무방합니다.

```haskell, line_num
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

먼저 정규표현식 자체를 정의했습니다. `T`는 `Char`, 즉 각 글자들의 type입니다.

- `EmptySet`: 아무 문자열에도 대응되지 않습니다.
- `EmptyStr`: `[]`, 즉 빈 문자열에 대응됩니다.
- `Char t`: 한 글자짜리 문자열입니다.
- `App r1 r2`: 유효한 문자열 2개의 합 (concatenation)입니다.
- `Union r1 r2`: 정규표현식의 `|`에 해당됩니다.
- `Star r`: 정규표현식의 `*`에 해당됩니다.

[[anchor, id=yogi]][[/anchor]]

여기서 사용한 `Inductive`는 `ev`, `le`를 정의할 때 사용한 `Inductive`보다는 `bool`, `bin`등을 정의할 때 사용한 `Inductive`에 가깝습니다. 즉, 7장에서 새로 본 `Prop`을 반환하는 `Inductive`가 아니고 [옛날](Chap1-1.html#keywordinductive)에 Rust의 enum에 비유하면서 설명했던 그 `Inductive`에 가깝습니다.

[[anchor, id=keyword reserved]][[/anchor]]

```haskell, line_num
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

또한 `exp_match`의 type이 `list T -> reg_exp T -> Prop`이란 것도 주목할 필요가 있습니다. `exp_match`는 문자열과 정규표현식을 하나씩 받아서 둘이 대응이 되는지를 알려준다는 뜻입니다. [방금 전](#yogi)에 분류한 거에 따르면 전자의 정의에 가깝죠.

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

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap7-2. Using Evidence in Proofs](Chap7-2.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]