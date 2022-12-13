| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Programming with Propositions

Coq 프로그래밍은 재밌습니다. Coq에서는 명제 자체를 반환하는 함수와 명제를 인수로 받는 함수를 이용해서 다양한 것들을 할 수 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.
```

두 개의 함수를 정의했습니다. `In x l`은 `l` 안에 `x`가 있는지 없는지를 말하는 명제를 반환하는 함수이고, `All P l`은 `l`의 모든 원소가 `P`를 만족하는지 아닌지를 말하는 명제를 반환하는 함수입니다. 보통의 프로그래밍 언어는 위와 같은 상황에서 boolean 값을 반환하는 함수를 쓰지만 Coq에서는 명제 자체를 반환하는 함수를 씁니다.

저 함수를 이용해서 몇가지 증명을 해보겠습니다.

```haskell, line_num
Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [ | x' l' IHl'].
  - (*{- l = [] -}*)
    simpl.
    intros H.
    destruct H.
  - (*{- l = x'::l' -}*)
    simpl.
    intros H.
    destruct H as [H1 | H2].
    * (*{- x' = x -}*)
      left.
      rewrite H1.
      reflexivity.
    * (*{- In x l' -}*)
      right.
      apply IHl'.
      apply H2.
  Qed.
```

`l` 안에 `x`가 있으면 `l`과 `x`를 `f`라는 함수에 넣어도 여전히 `In`이 참이라고 말하는 명제입니다. `l`이 비었을 경우 가정이 거짓이므로 명제가 참이라고 증명하고, `l`이 비지 않았을 경우 수학적 귀납법으로 증명했습니다.

```haskell, line_num
Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - (*{- (forall x, In x l -> P x) -> All P l -}*)
    induction l as [ | x' l' IHl'].
    * (*{- l = [] -}*)
      simpl.
      reflexivity.
    * (*{- l = x'::l' -}*)
      simpl.
      split.
      + (*{- P x' -}*)
        apply H.
        left.
        reflexivity.
      + (*{- All P l' -}*)
        apply IHl'.
        intros x H2.
        apply H.
        right.
        apply H2.
  - (*{- All P l -> forall x, In x l -> P x -}*)
    induction l as [ | x' l' IHl'].
    * (*{- l = [] -}*)
      intros _ x H.
      unfold In in H.
      destruct H.
    * (*{- l = x'::l' -}*)
      simpl.
      intros H.
      destruct H as [H1 H2].
      intros x H3.
      destruct H3 as [H4 | H5].
      + (*{- x' = x -}*)
        rewrite <- H4.
        apply H1.
      + (*{- In x l' -}*)
        apply IHl'.
        ** (*{- All P l' -}*)
           apply H2.
        ** (*{- In x l' -}*)
           apply H5.
  Qed.
```

`l`의 모든 원소가 `P`라는 성질을 만족하면 `All P l`이 참이라고 말하는 명제입니다. 즉, `All`을 다른 방식으로 정의하고 참이 되는지 확인하는 예제입니다.

하다보니까 새로운 걸 알게 됐습니다. context에 `H: p -> q`가 있고 goal에 `q`가 있을 때 `apply H`를 하면 goal이 `p`로 바뀝니다. 생각해보니까 당연하네요.

## Applying Theorems to Arguments

함수형 언어 얘기를 하면서 Coq에선 함수들이 일급 시민이라고 했던 걸 기억하시나요? Coq에선 함수뿐만 아니라 명제들도 일급입니다. 이를 이용해서 다양한 기술들을 구사할 수 있지만 여기선 `rewrite`와 관련된 걸 살펴보겠습니다.

```haskell, line_num
Theorem add_comm : forall n m : nat,
  n + m = m + n.

Lemma add_comm3 : forall x y z,
  x + (y + z) = (z + y) + x.
```

`add_comm`을 이용해서 `add_comm3`를 증명해봅시다. 얼핏 보기에는 `add_comm`을 2번 쓰면 될 것 같습니다. 하지만 그렇게하면 똑같은 부분에 `add_comm`이 2번 적용돼서 원점으로 돌아옵니다. `add_comm`을 어디에 적용할지 정하려면 어떤 방법을 써야할까요? [옛날](Chap2-2.html#keywordassert)에 봤던 것처럼 `assert`를 쓸 수도 있지만 그것보다 더 간편한 방법이 있습니다. 아래를 봅시다.

[[anchor, id = keyword rewrite]][[/anchor]]

```haskell, line_num
Lemma add_comm3 : forall x y z,
  x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
  Qed.
```

마치 함수에 인수를 주듯 `add_comm`에 `y`와 `z`라는 인수를 줬습니다. 그 결과 `add_comm`이 어느 덧셈에 적용될지 정할 수 있게 됐습니다.

이 예시에선 그럴 일이 없지만 증명을 하다보면 일부 인수만 사용하고 싶을 때도 있습니다. 예를 들면 방금 전의 상황에서 `add_comm`을 `z`에만 적용하고 싶으면 어떻게 할까요? `rewrite (add_comm _ z)`처럼 하면 됩니다.

### `apply ... with ...` tactics

방금 `rewrite`에 인수를 줬던 것처럼 이번엔 `apply`에 인수를 줘보겠습니다. 예시에 쓰일 함수와 명제들을 먼저 정의하겠습니다.

```haskell, line_num
Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not.
  induction l as [ | h' t' IHl'].
  - (*{- l = [] -}*)
    simpl in H.
    destruct H.
  - (*{- l = h' :: t' -}*)
    intros H2.
    rewrite H2 in H.
    destruct H.
  Qed.
```

`x`가 `l`에 포함되면 `l`은 빈 list가 아니라는 명제입니다. 저걸 이용해서 42가 `l`에 포함되면 `l`은 빈 list가 아니라는 명제를 증명해보겠습니다.

[[anchor, id = keyword apply with]][[/anchor]]

```haskell, line_num
Theorem in_not_nil_42 :
  forall (l : list nat), In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with ( x := 42).
  apply H.
  Qed.
```

증명은 간단합니다. goal에는 `l <> []`가 있고, context에는 `In 42 l`이 있는 상황입니다. 또한, `in_not_nil with ( x := 42 )`는 `In 42 l -> l <> []`가 참이라고 말해줍니다. `In 42 l -> l <> []`가 참이므로 goal의 `l <> []`가 참임을 보이는 것은 `In 42 l`이 참임을 보이는 것과 동치입니다. 그럼 context에 `In 42 l`이 있으므로 증명이 끝나네요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-3. Existential Quantification](Chap6-3.html)

[[/left]]

[[right]]

[Chap6-5. Axioms](Chap6-5.html) >>

[[/right]]