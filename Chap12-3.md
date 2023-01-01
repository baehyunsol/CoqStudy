| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# States and Commands

[12-1 단원](Chap12-1.html)에서 간단한 프로그래밍 언어를 만들었습니다. 거기서 만든 언어는 너무 간단해서 어떻게 쓸지 애매했는데, 이번 단원에서 언어를 발전시켜보겠습니다. 이번 단원에서는 언어에 변수를 추가해보겠습니다. 간단하게 하기 위해서 변수의 범위(scope)는 전혀 신경 쓰지 않고, 정수형만 다루겠습니다.

모든 변수의 이름과 값이 저장돼 있는 자료구조를 상태(state)라고 합니다. 상태를 구현하기 위해서 [8단원](Chap8-1.html)에서 봤던 `total_map`을 사용하겠습니다. 또한 변수가 추가됐으니 `aexp`의 형태도 조금 바꾸겠습니다.

```haskell, line_num
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
```

변수 자체도 하나의 숫자니 `aexp`에 `AId`를 추가했습니다. 또한, 책에서 아래와 같은 Notation들을 추가했습니다.

```haskell, line_num
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
```

아주 긴데, 겁먹으실 필요는 전혀 없습니다. `<{ e }>`가 정의들을 핵심입니다. `e` 자리에 들어오는 식은 Coq 문법이 아니고 우리의 프로그래밍 언어의 문법으로 해석하라는 뜻입니다. 그 아래에 정의한 문법들 역시 Coq의 Notation이 아니고 우리가 만드는 언어의 Notation입니다.

## Commands

변수를 만들었으니 몇가지 명령어를 추가해보겠습니다.

```haskell, line_num
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
```

`com`이라는 `Inductive`를 만들고 걔네의 Notation을 추가했습니다. `CSkip`은 아무것도 하지 말라는 뜻, `CAsgn`은 대입 명령어, `CSeq`은 여러 명령어를 순차적으로 실행하라는 뜻입니다.

## ceval

명령어를 추가했으니 명령어를 실행하는 법도 Coq에게 알려줘야죠. 아래의 정의를 봅시다.

```haskell, line_num
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
```

새로운 Notation을 추가했습니다. `st =[ c ]=> st'`에서 `st`와 `st'`는 상태고, `c`는 명령어입니다. `st`라는 상태에서 `c`를 실행하면 `st'`이 된다는 뜻입니다. 즉, 프로그래밍 언어를 상태와 명령어로만 봅니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 12-2. Coq Automation](Chap12-2.html)

[[/left]]

[[right]]

[Chapter 13-1. ??](Chap13-1.html) >>

[[/right]]