| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# More Inductives

지난 단원에 이어서 Coq에서 자주 쓰이는 정의들을 뜯어보겠습니다.

## Existential Quantification

Coq에서 자주 쓰이는 `exists`는 어떻게 정의돼 있는지 살펴봅시다.

```coq, line_num
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
```

TODO: 왜 `forall`로 정의했는지 모르겠네요...

## `True` and `False`

`True`와 `False`의 정의도 살펴보겠습니다. 아주 간단합니다.

```coq, line_num
Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .
```

[6-2 단원](Chap6-2.html)에서 봤던 정의와 동일합니다. `True`는 constructor가 하나인 `Inductive`이고 `False`는 constructor가 0개인 (그래서 증거를 만들 수 없는) `Inductive`입니다.

## Equality

Coq의 등호도 Coq를 이용해서 정의돼 있습니다. Coq가 강력한 언어라는게 새삼 느껴지네요.

```coq, line_num
Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                     (at level 70, no associativity)
                     : type_scope.
```

`eq`는 constructor를 하나 갖는 `Inductive`입니다. 동일한 인수 두개가 들어와야지만 `eq_refl`합니다. 따라서 증명에서도 아래와 같이 사용할 수 있습니다.

> TODO: 책에선 Notation을 `==`라고 정의했는데 실제 Coq에서는 `=`로 정의돼 있습니다. 지금까지 `eq`의 기호로 써오던 `=`와 이번에 정의한 `==`가 어떻게 다른지 모르겠네요.

```coq, line_num
Lemma four: 2 + 2 == 1 + 3.

Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
```

지금까지 써오던 `reflexivity` tactic이 사실은 `apply eq_refl`에 불과했습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap9-2. Logical Connectives as Inductive Types](Chap9-2.html)

[[/left]]

[[right]]

[Chap9-4. Inversion, Again](Chap9-4.html) >>

[[/right]]