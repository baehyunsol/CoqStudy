| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Arithmetic and Boolean Expressions

이제부터는 Coq를 이용해서 간단한 프로그래밍 언어를 만들어보겠습니다. 이번 단원에서는 간단한 문법과 의미만 정의하고, 뒷 단원에서 언어를 요리조리 뜯어볼 계획입니다.

```haskell, line_num
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

언어의 가장 기본이 되는 `Inductive` 2가지를 정의했습니다. `aexp`는 숫자와 관련된 식(expression)들이고, `bexp`는 숫자 비교와 boolean과 관련된 식들을 정의합니다. 식을 정의했으면 그 식들을 계산하는 것도 정의해야겠죠? 아래의 코드를 봅시다.

```haskell, line_num
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
```

코드는 아주 간단합니다. 이미 Coq에서 정의해 놓은 연산들이니 그걸 각 식들에 대응시키기만 하면 되거든요. 7장에서 열심히 공부한 `Inductive`를 이용해서도 정의를 해보겠습니다. 아래를 봅시다.

```haskell, line_num
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

Theorem eval_practice : (APlus (ANum 4) (ANum 5)) ==> 9.
Proof.
  apply (E_APlus (ANum 4) (ANum 5) 4 5).
  - (*{- ANum 4 ==> 4 -}*)
    apply (E_ANum 4).
  - (*{- ANum 5 ==> 5 -}*)
    apply (E_ANum 5).
  Qed.
```

Notation 정의한 김에 사용예제도 하나 추가해봤습니다.

## Optimizations

```haskell, line_num
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.
```

책에서 아주 간단한 최적화도 소개하길래 저도 소개해봤습니다. `aexp`가 있으면 그 안을 샅샅이 뒤져서 `0+n`의 꼴을 전부 찾아내서 `n`으로 바꿔주는 최적화입니다. 심심하신 분들은 아래의 정리도 증명해보세요!

```haskell, line_num
Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
```

최적화를 하든 안하든 결과가 항상 같다는 정리입니다. 사소해보이지만 아주 중요한 정리입니다. Coq로 컴파일러 최적화를 검증할 수 있는데 (실제로 그렇게 많이 쓰입니다), 저희가 방금 한게 컴파일러 최적화 검증의 첫걸음이거든요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 11-?. TODO](Chap11-?.html)

[[/left]]

[[right]]

[Chapter 12-2. Coq Automation](Chap12-2.html) >>

[[/right]]