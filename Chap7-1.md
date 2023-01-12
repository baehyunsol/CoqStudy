| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Inductively defined Propositions

제목에서 알 수 있듯, 이번 장에서는 `Inductive` 키워드를 집중적으로 살펴볼 예정입니다.

[[anchor, id = keyword inductive]][[/anchor]]

## 콜라츠 추측

책에서는 콜라츠 추측을 이용해서 예시를 듭니다. 콜라츠 추측은 아주 간단하니 설명은 생략하겠습니다. 혹시 콜라츠 수열이 뭔지 모르시는 분들은 [인터넷](https://en.wikipedia.org/wiki/Collatz_conjecture)을 참고해주세요.

콜라츠 추측을 Coq로 표현하려면 어떻게 해야할까요? 먼저 콜라츠 함수를 아래와 같이 정의해보겠습니다.

```coq, line_num
Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.
```

아주 간단하군요. 그럼 콜라츠 수열이 항상 1로 끝난다는 사실을 Coq로 표현하려면 어떻게 할까요?

```coq, line_num
Fixpoint reaches_1 (n : nat) :=
  if n =? 1 then true
  else reaches_1 (f n).

Conjecture collatz : forall n, reaches_1 n = true.
```

아주 간단하게 써봤습니다. `n`이 1에 도달했으면 `true`를 반환하고 아직 1이 아니면 `f n`이 1인지 재귀적으로 확인합니다. 그렇게 해서 모든 `n`이 1에 도달하면 콜라츠 추측이 참이겠죠.

아쉽지만 위의 코드는 Coq가 허락해주지 않습니다. Coq는 `Fixpoint`를 쓸 때 재귀가 유한한지 확인합니다. 하지만 `reaches_1`의 재귀가 유한한지 확인하는 건 콜라츠 추측을 증명하는 것과 동치죠, Coq가 할 수 있을 리가 없습니다.

이번에는 `Fixpoint`가 아닌 `Inductive`를 이용해서 콜라츠 추측을 표현해보겠습니다.

```coq, line_num
Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Conjecture collatz : forall n, reaches_1 n.
```

방금 전에 `Fixpoint`로 정의한 `reaches_1`과 거의 동일한 형태입니다. 하지만 `Fixpoint`대신 `Inductive` 키워드를 사용했습니다.

## `Inductive`

예시 하나만 봐서는 `Inductive`가 무슨 일을 하는지 잘 알기 힘듭니다. 책에서 나온 다른 예시들도 살펴보겠습니다.

### le

```coq, line_num
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
```

~_작거나 같다_~를 `Inductive`를 이용해서 정의해보았습니다. 작거나 같을 조건은 2개가 있고, 그 조건들을 각각 `le_n`과 `ls_S`를 통해서 표현했습니다.

- `le_n`: [[math]] n leq n [[/math]]이다.
- `le_S`: [[math]] n leq m [[/math]]이면 [[math]] n leq m + 1[[/math]]이다.

이렇게 정의를 하면, `le a b`는 ~_`a`가 `b`보다 작거나 같다_~라는 뜻의 `Prop`이 됩니다. 이 정의를 이용해서 [[math]] 3 leq 4 [[/math]]를 증명해보겠습니다.

```coq, line_num
Theorem le34 : le 3 4.
Proof.
  apply le_S.
  apply le_n.
  Qed.
```

먼저, `le_S`를 이용해서 `le 3 4`를 `le 3 3`으로 바꿨습니다. 그 다음에 `le_n`을 이용해서 `le 3 3`이 참임을 보였습니다. 쉽죠?

### permutation

> `Perm3 x y` := `x`는 `y`의 permutation[^perm]이다.

`x`와 `y`를 받아서 위와 같은 뜻을 가진 `Prop`를 반환하는 `Perm3`를 정의해보겠습니다.

```coq, line_num
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.
```

모든 길이의 list에 대해서 정의하는 건 복잡하니 길이가 3인 list에 대해서만 정의했습니다. 이 정의를 이용해서 `[4; 5; 6]`과 `[6; 5; 4]`가 permutation임을 증명해보겠습니다.

[^perm]: 두 list `x`와 `y`가 원소들은 같고 순서만 (같거나) 다를 때, 둘을 permutation이라고 합니다.

```coq, line_num
Theorem perm3ex : Perm3 [4; 5; 6] [6; 5; 4].
Proof.
  assert (Perm3 [4; 5; 6] [5; 6; 4]).
    {
      apply (perm3_trans [4; 5; 6] [5; 4; 6] [5; 6; 4]).
      apply perm3_swap12.
      apply perm3_swap23.
    }
  assert (Perm3 [5; 6; 4] [6; 5; 4]).
    { apply perm3_swap12. }
  apply (perm3_trans [4; 5; 6] [5; 6; 4] [6; 5; 4]).
  apply H.
  apply H0.
  Qed.
```

`[4; 5; 6]`을 `[6; 5; 4]`로 만들기 위해서는 swap을 3번 해야합니다. `perm3_trans`는 swap을 한번에 2개까지만 할 수 있으므로 중간 단계를 추가해서 `perm3_trans`를 3번 했습니다.

### 정리

이번에 본 `Inductive`의 사용은 기존에 보던 것들과 많이 다릅니다. `nat`의 정의와 `list`, `le`의 정의를 놓고 비교해보겠습니다.

```coq, line_num
Inductive nat : Type :=
  | O
  | S (n: nat).

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
```

`nat`은 `Type` 그 자체이고 `list`는 `Type`을 내놓는 함수입니다. 그에반해 `le`는 자연수 2개를 받아서 `Prop`을 내놓는 함수입니다. 즉, `le`는 타입이 아니고 자연수의 성질입니다. 또한, `list`와 `le`는 둘다 함수이지만 인수를 받는 방식이 다릅니다. `list`는 `Type` 하나를 인수로 받는데 그 인수가 `:`의 왼쪽에 있습니다. (5번 줄) 그래서 인수라기보다는 다른 언어들의 generic에 가까운 느낌입니다. 그에반해 `le`는 인수들이 `:`의 오른쪽에 있고 (9번 줄), 그래서 `le 3 5`와 같은 방식으로 인수를 받습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-5. Axioms](Chap6-5.html)

[[/left]]

[[right]]

[Chap7-2. Using Evidence in Proofs](Chap7-2.html) >>

[[/right]]