| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Inversion, Again

`Inductive`와 관련된 내용을 조금 더 공부했으니 `inversion` tactic을 복습하겠습니다. context에 `H`라는 가설이 있고 `H`의 type은 `P`일 때, `inversion H`를 하면 아래와 같은 일들이 일어납니다.

- `P`의 각각의 constructor를 `C`라고 할 때, 각 `C`에 대하여
  1. `H`가 `C`로 construct 됐다고 가정하는 subgoal을 추가합니다.
  1. `C`가 참이 되기 위해서 필요한 인수들을 context에 추가합니다.
  1. `C`의 결과로 나올 type과 현재 goal을 비교해서 필요한 등식들을 context에 추가합니다.
  1. 만약 `C`가 참이 되는게 불가능하다고 판단될 경우 (ex: `S n = 0`같은게 context에 추가될 경우), 그 subgoal을 없애버립니다.

아래의 예시들에서 1~4번 단계를 언급할텐데 그건 전부 위의 목록에 있는 단계들입니다.

## 예시들

저렇게만 보면 조금 추상적이니 예시들과 함께 설명하겠습니다.

### 예시 1, `and`

```haskell, line_num
Theorem and_t : forall P Q : Prop, P /\ Q -> P.

Proof.
  intros P Q H.
  inversion H.
  apply H0.
  Qed.
```

증명을 다 볼 필요는 없고, `inversion`이 하는 일만 보겠습니다. `and`의 정의가 기억이 안 나면 [여기](Chap9-2.html#conjunction)를 참고해주세요.

`and`의 constructor는 `conj` 하나밖에 없습니다. 그래서 Coq는 `P /\ Q`가 `conj P Q`로 됐다고 가정합니다. `conj P Q`가 되기 위해선 `P`와 `Q`가 필요하니 2번 단계에서 context에 `P`와 `Q`를 추가합니다. `and`의 결과는 `P`와 `Q`에 추가적인 제약을 가하지 않으므로 3번 단계에선 추가적인 등식이 생성되지 않습니다.

### 예시 2, `or`

```haskell, line_num
Theorem or_t : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H.
  - (*{- H0: P -}*)
    right.
    apply H0.
  - (*{- H0: Q -}*)
    left.
    apply H0.
  Qed.
```

`or`의 정의가 기억이 안 나면 [여기](Chap9-2.html#disjunction)를 참고해주세요. `or`의 constructor는 `or_introl P`와 `or_intror Q`의 2개가 있습니다. 그래서 1번 단계에서 subgoal이 2개가 나옵니다. 첫번째 subgoal은 `or_introl P`가 참이라고 가정했으므로 context에 `H0: P`가 추가되고 두번째 subgoal은 `or_intror Q`가 참이라고 가정했으므로 context에 `H0: Q`가 추가됩니다. 이번에도 마찬가지로 3번 단계에서 추가적인 등식이 생성되지는 않습니다.

### 예시 3, `eq`

```haskell, line_num
Theorem eq_t : forall m n : nat, S m = S n -> m = n.
Proof.
  intros m n H.
  inversion H.
  reflexivity.
  Qed.
```

`eq`의 정의가 기억이 안 나면 [여기](Chap9-3.html#equality)를 참고해주세요. `eq`의 constructor는 `eq_refl` 하나 뿐이므로 1번 단계에서 subgoal은 하나만 생성됩니다. 하지만 `eq_refl`의 결과를 보면 `m = n`이라는 추가적인 정보를 알 수 있으므로 3번 단계에서 `H1: m = n`이 context에 추가됩니다. 물론 이건 너무 급하게 만든 예제라 `H1`을 사용하지 않고 증명했습니다.

### 예시 4, `ev`

```haskell, line_num
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E.
  apply H0.
  Qed.
```

`ev`의 정의가 기억이 안 나면 [여기](Chap7-2.html)를 참고해주세요. `ev`의 constructor는 `ev_0`와 `ev_SS`로 2개입니다. `ev_0`가 참일 경우 context에 `0 = S (S n)`이 추가돼야 하는데, 이는 말이 안되므로 `ev_0`는 4번 단계에서 버려집니다. 그리고 `ev_SS`가 참이므로 `ev_SS`의 인수들이 2번 단계에서 context에 추가됩니다. 그 인수들은 `n0: nat`과 `H0: ev n`입니다.

[[box]]

## Coq's Trusted Computing Base

Coq으로 다른 명제/프로그램에 결점이 없다는 건 증명할 수 있지만 Coq 자체를 검증할 순 없습니다. 그럼 Coq이 결점이 없다는 건 어떻게 증명할까요?? 못합니다.

그대신 Coq은 아주 작은 토대만 손으로 증명을 하고, 나머지 부분들은 그 토대를 이용해서 정의해놨습니다. 그래서 Coq은 믿을 수 있습니다. 그 토대를 쌓아가는 부분이 우리가 이번 단원에서 봤던 Curry-Howard correspondance입니다. 증거와 증명들을 type과 값들처럼 다루기 때문에 Coq 자체가 무결하다는 것도 type-checker를 이용해서 검증이 가능합니다. Type-checker 자체는 상대적으로 간단하고 단순하기 때문에 쉽게 믿을 수 있습니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap9-3. More Inductives](Chap9-3.html)

[[/left]]

[[right]]

[Chap10-1. Induction Principles](Chap10-1.html) >>

[[/right]]