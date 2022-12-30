| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Logical Connectives as Inductive Types

[옛날](Chap6-1.html)에 `\/`와 `/\`를 공부했죠? `\/`와 `/\`도 전부 `Inductive`를 이용해서 정의돼 있습니다. 이번 장에는 그 정의들을 살펴보겠습니다.

## Conjunction

먼저 `/\`의 정의를 살펴보겠습니다.

```haskell, line_num
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.
```

`Arguments`가 무슨 뜻인지 기억이 안 나면 [여기](Chap4-1.html#keywordarguments)를 참고해주세요.

정의는 아주 간단합니다. `P`도 참이고 `Q`도 참이면 `P /\ Q`도 참이죠. 정의가 저렇게 생겼기 때문에 `destruct` tactic이 잘 작동합니다.

```haskell, line_num
Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.          (*{- HPQ: P /\ Q -}*)
  destruct HPQ as [HP HQ]. (*{- HP: P, HQ: Q -}*)
  Show Proof.  (*{- (fun (P Q : Prop) (HPQ : P /\ Q) => match HPQ with | conj x x0 => (fun (HP : P) (HQ : Q) => ?Goal) x x0 end) -}*)
  apply HP.
  Show Proof.  (*{- (fun (P Q : Prop) (HPQ : P /\ Q) => match HPQ with | conj x x0 => (fun (HP : P) (_ : Q) => HP) x x0 end) -}*)
Qed.
```

증명 자체는 [옛날](Chap6-1.html)에 봤던 것들과 비슷하니 자세히 설명하지 않겠습니다. 다만, `/\`의 정의를 알았으니 `destruct` tactic이 어떻게 쪼개는지 알았다는 것에 초점을 두겠습니다.

[[anchor, id = keyword destruct]][[/anchor]]

`destruct`는 `Inductive`로 정의된 객체를 각 constructor로 쪼갭니다. 예를 들어서 `bool`은 `true`와 `false`로 쪼개고, `nat`은 `O`와 `S n`으로 쪼갭니다. 또한, `S n`처럼 인수를 받는 constructor들은 각 인수에도 이름을 붙일 수 있습니다. `/\`의 constructor는 `conj`밖에 없고 `conj`는 인수를 2개 받으니 위와 같이 쪼개짐을 알 수 있습니다.

[[anchor, id = keyword split]][[/anchor]]

`destruct`를 자세히 봤으니 `split`이 어떻게 동작하는지도 자세히 살펴봅시다.

```haskell, line_num
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
  - (*{- P /\ Q -> Q /\ P -}*)
    intros [HP HQ].
    split.  (*{- `Q /\ P`가 `Q`와 `P`로 나눠집니다. -}*)
    + (*{- Q -}*)
      apply HQ.
    + (*{- P -}*)
      apply HP.
  - (*{- Q /\ P -> P /\ Q -}*)
    intros [HQ HP].
    split.  (*{- `P /\ Q`가 `P`와 `Q`로 나눠집니다. -}*)
    + (*{- P -}*)
      apply HP.
    + (*{- Q -}*)
      apply HQ.
Qed.
```

예제는 너무 쉬우니 따로 설명하지 않겠습니다.

`split` tactic은 constructor가 1개인 `Inductive`에만 적용할 수 있습니다. `/\`의 constructor는 `conj`로 유일하므로 `split`을 쓰면 `conj`의 두 인수로 쪼개집니다.

`/\`의 정의를 알면 proof object를 곧바로 적을 수도 있습니다. `and_comm`을 다른 방식으로 표현한 것들을 아래에서 보겠습니다.

```haskell, line_num
Definition and_comm_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm_aux P Q) (and_comm_aux Q P).
```

위와 같이 `and_comm'`을 `Theorem`이 아닌 `Definition`으로 정의했습니다. `and_comm_aux`라는 이름으로 `/\`의 교환법칙을 증명하고, 그걸 이용해서 `and_comm'`을 증명했습니다. 혹시나 까먹은 분을 위해 말씀 드리면, `P <-> Q`는 `(P -> Q) /\ (Q -> P)`의 축약이므로 `and_comm'`의 `conj`는 `<->`를 나타냅니다.

## Disjunction

이번엔 `\/`의 정의를 살펴보겠습니다.

```haskell, line_num
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.
```

이번에도 마찬가지로 `left` tactic은 첫번째 constructor를 나타내고 `right`는 두번째 constructor를 나타낸다고 생각할 수 있습니다.

## Existential Quantification

Coq에서 자주 쓰이는 `exists`는 어떻게 정의돼 있는지 살펴봅시다.

```haskell, line_num
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
```

TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap9-1. Curry Howard Correspondence](Chap9-1.html)

[[/left]]

[[right]]

[Chap9-3. ??](Chap9-3.html) >>

[[/right]]