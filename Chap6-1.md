| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Conjunction and Disjunction

지금까지 저희는 아주 간단한 논리들 (`p -> q`, `x = y` 등)만 봤습니다. Coq가 다룰 수 있는 논리는 이것들보다 훨씬 많은데, 이번 장에서는 그 논리들을 살펴보겠습니다.

그 전에, `Prop`이라는 type에 대해서 먼저 알아보겠습니다.

## Prop

[이전](Chap4-2.html#higher-order-functions)에 Coq에서 함수가 일급시민이라고 언급했습니다. 그것과 마찬가지로, 모든 명제들도 일급시민입니다. 모든 명제들은 `Prop`이라는 type을 가지며, 함수의 인자로 쓰거나 반환값으로 쓰는 등 다양한 연산[^fc]을 할 수 있습니다.

[^fc]: 즉, `nat`이나 `bool`등이 할 수 있는 걸 `Prop`도 전부 할 수 있습니다.

```haskell, line_num
Check 2 = 2.     (*{- : Prop -}*)
Check 3 = 2.     (*{- : Prop -}*)
Check (forall n: nat, n + 0 = 0 + n).  (*{- : Prop -}*)
Compute 3 = 3.   (*{- 3 = 3 : Prop -}*)
Compute 3 = 2.   (*{- 3 = 2 : Prop -}*)
```

위에서처럼 `Check`나 `Compute`를 할 수도 있고, 아래처럼 함수와 조합하여 더 놀라운 것들도 할 수 있습니다.

```haskell, line_num
Definition is_injective {A B} (f : A -> B) :=
  forall x y : A,
  f x = f y -> x = y.
```

`is_injective`는 함수를 받아서 `Prop`을 내놓는 함수입니다. `is_injective`가 받는 함수가 injective하면 반환된 `Prop`이 참이고 아니면 반환된 `Prop`이 거짓입니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem S_injective : is_injective S.

Proof.
  intros n m H.
  injection H as H1.
  apply H1.
  Qed.
```

자연수를 정의할 때 쓰는 `S`가 injective하단 걸 증명하기 위해 `is_injective S`라는 아주 간단한 표현을 썼습니다. 쉽죠?

[[box]]

### eq

[[anchor, id = notation eq]][[/anchor]]

참고로 `x = y` 할 때의 `=`도 내장특수 문법이 아닌 일반 함수입니다. `=`는 Coq 표준 라이브러리에 정의돼 있으며 이름은 `eq`입니다. Type을 확인해보면 아래와 같습니다.

```haskell
Check @eq : forall A : Type, A -> A -> Prop.
```

즉, `eq`는 `A`라는 type의 instance 2개를 받아서 그 둘이 같은지 다른지의 `Prop`을 반환하는 함수입니다.

### ->

[[anchor, id = notation implies]][[/anchor]]

그럼 `a = b -> c = d`의 type은 뭘까요? 저 친구도 마찬가지로 `Prop`입니다. Coq 내부에서 `->`라는 Notation은 아래와 같이 정의돼 있습니다.

```haskell
Notation "A -> B" := (forall (_ : A), B) : type_scope.
```

[[/box]]

## Conjunction

Conjunction은 *logical and*입니다. `and`라는 이름으로 정의돼 있고, `/\`라는 Notation이 내장돼 있습니다. 아래의 예시를 보겠습니다.

[[anchor, id = keyword split]][[/anchor]]

```haskell, line_num
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (*{- 3 + 4 = 7 -}*)
    reflexivity.
  - (*{- 2 * 2 = 4 -}*)
    reflexivity.
Qed.
```

`3 + 4 = 7`이라는 `Prop`과 `2 * 2 = 4`라는 `Prop`을 and로 묶었습니다. ~_A and B_~라는 명제를 증명하기 위해선 A와 B를 따로 증명해야하죠? 그럴 때 `split`이란 tactic을 사용합니다. 그럼 `3 + 4 = 7`과 `2 * 2 = 4`의 subgoal이 따로 등록됩니다.

[[anchor, id = keyword destruct]][[/anchor]]

혹은 `destruct` tactic을 이용할 수도 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.
```

원래 context에 `H: n = 0 /\ m = 0`이 들어있었는데 `destruct`로 인해서 `Hn: n = 0`과 `Hm: m = 0`으로 나눠집니다. `destruct`하기 귀찮다면 `intros n m [Hn Hm]`을 이용하는 방법도 있습니다. `intros` 안에 있는 대괄호로 인해서 `destruct`가 자동으로 됩니다.

마지막으로 연습 하나만 하고 넘어가겠습니다.

```haskell, line_num
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - (*{- P /\ Q -}*)
    split.
    + (*{- P -}*)
      apply HP.
    + (*{- Q -}*)
      apply HQ.
  - (*{- R -}*)
    apply HR.
  Qed.
```

`/\`가 여러겹으로 돼 있는 구문도 `[HP [HQ HR]]`의 문법을 통해서 깔끔하게 `destruct`했습니다. 위의 증명을 직접 해보면서 `destruct`와 `split`이 어떤 식으로 동작하는지 확인해보시기 바랍니다.

## Disjunction

logical and를 공부했으니 이번엔 logical or를 보겠습니다.

```haskell, line_num
Lemma mult_0:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
  - (* Hn: n = 0 *)
    rewrite Hn.
    reflexivity.
  - (* Hm: m = 0 *)
    rewrite Hm.
    rewrite <- mult_n_O.
    reflexivity.
  Qed.
```

이번에는 아까와 `destruct`하는 문법이 조금 바뀌었습니다. and를 적용할 때는 `Hn`과 `Hm`이 동시에 context로 들어갔고, 동시에 사용가능했지만 이번에는 `Hn`과 `Hm`에 대해서 각각 증명을 해야합니다 (그게 or이니까요). 그래서 `[Hn | Hm]`이라고 쓴 걸 볼 수 있습니다. 이번에도 and 때와 마찬가지로 `intros n m [Hn | Hm]`을 이용해서 `destruct`를 간편하게 할 수 있습니다.

`\/`가 goal에 있으면 어떻게 할까요? 아래의 예시를 보겠습니다.

[[anchor, id = keyword left]][[/anchor]][[anchor, id = keyword right]][[/anchor]]

```haskell, line_num
Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.
```

~_A or B_~를 증명하기 위해선 A와 B 중에서 하나만 증명해도 되죠? 그럴 때 쓰는 tactic이 `left`와 `right`입니다. 증명하고자 하는 명제가 `A \/ B`일 때 `left`를 쓰면 `A`만 남깁니다. `right`도 마찬가지입니다.

책에 재밌는 예시들이 있길래 하나 더 갖고 왔습니다.

```haskell, line_num
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [ | n'].
  - (*{- n = 0 -}*)
    left.
    reflexivity.
  - (*{- n = S n' -}*)
    right.
    reflexivity.
Qed.
```

`intros [ | n']`은 `\/`를 쪼개는게 아니고 `n`을 쪼개는 겁니다. 저는 처음에 헷갈렸는데 헷갈리지 않으시길 바랍니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap5-3. More tactics](Chap5-3.html)

[[/left]]

[[right]]

[Chap6-2. True and False Propositions](Chap6-2.html) >>

[[/right]]