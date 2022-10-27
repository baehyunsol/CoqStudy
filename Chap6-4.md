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

Applying Theorems to Arguments부터 ㄱㄱ

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-3. Existential Quantification](Chap6-3.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]