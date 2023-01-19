| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Basics

이번 단원에서는 프로그래밍 언어의 아주 큰 주제 중 하나인 type system에 대해서 공부하겠습니다. 언제나 그랬듯이 간단한 언어를 하나 정의하고 그 언어를 통해서 개념을 공부하겠습니다.

## tm

이번에 정의할 언어는 14단원 [끝자락](14-6.html#tm)에서 정의한 tm과 비슷하게 생겼습니다. 다만 tm은 너무 단순해서 타입을 정의할 수가 없으니 bool과 자연수 타입을 가지는 좀 더 복잡한 언어를 정의해봅시다.

```line_num
t ::= true
    | false
    | if t then t else t
    | 0
    | succ t
    | pred t
    | iszero t
```

Coq으로 한 정의는 너무 길어서 간략한 정의만 실었습니다. 위의 표기들이 tm이 가질 수 있는 모든 표기입니다. 14단원에서도 `value`를 정의했죠? 더 이상 계산이 불가능한 상수 상태를 `value`로 정의했습니다. 이번에도 똑같이 정의해보겠습니다.

```coq, line_num
Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.
```

이번에는 tm이 가질 수 있는 값의 종류가 2 종류라서 `bvalue`와 `nvalue`를 따로 정의하고 둘을 합쳐서 `value`라고 정의했습니다.

### Operational Semantics

새로 만든 tm의 single-step relation을 정의해보겠습니다. 이번에도 Coq 정의는 생략하고 글로만 적겠습니다.

```line_num

           -------------------------------                   (ST_IfTrue)
           if true then t1 else t2 --> t1

           -------------------------------                  (ST_IfFalse)
           if false then t1 else t2 --> t2

                       t1 --> t1'
    ------------------------------------------------             (ST_If)
    if t1 then t2 else t3 --> if t1' then t2 else t3

                     t1 --> t1'
                 --------------------                          (ST_Succ)
                 succ t1 --> succ t1'

                   ------------                               (ST_Pred0)
                   pred 0 --> 0

                 numeric value v
                -------------------                        (ST_PredSucc)
                pred (succ v) --> v

                      t1 --> t1'
                 --------------------                          (ST_Pred)
                 pred t1 --> pred t1'

                  -----------------                         (ST_IsZero0)
                  iszero 0 --> true

                 numeric value v
              -------------------------                  (ST_IszeroSucc)
              iszero (succ v) --> false

                    t1 --> t1'
               ------------------------                      (ST_Iszero)
               iszero t1 --> iszero t1'
```

각 상황마다 다음 단계로 넘어가는 step을 정의했습니다. 타입이 맞지 않은 식을 넣으면 (예: `succ if true then true else false`), 할 수 있는한 최대한 step을 많이 밟은 후, 상수가 되지 못하고 멈추게(stuck) 됩니다. (예: `succ true`)

이번 tm은 14장의 tm과 다르게 멈추는 경우가 있으므로 normal form과 관련된 정의도 다시 해줘야합니다.

```coq, line_num
Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.
```

이제는 `value`가 아니지만 더 이상 step을 밟을 수 없는 경우가 생겼습니다. 하지만 여전히 `value`에서 step을 밟을 수 있는 경우는 존재하지 않습니다.

|                   | Value임  | Value가 아님  |
|-------------------|----------|--------------|
| Step 밟을 수 있음  | 無       | 有           |
| Step 밟을 수 없음  | 有       | 有           |

## Types

이제 타입과 관련된 정의들을 살펴보겠습니다. 먼저 타입을 나타내는 `ty`라는 `Type`을 추가하겠습니다.

```coq, line_num
Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
```

첫번째 줄에서 `ty`는 tm의 타입이고, `Type`은 Coq의 타입입니다. 또, 타입을 나타내는 기호도 하나 추가하겠습니다. `⊢ t ∈ T`라고 쓰면 ~_`t` has type `T`_~라는 뜻입니다. 이 기호를 이용해서 tm의 모든 표현에 타입을 부여할 수 있습니다. 아래처럼요.

```line_num

                  --------------                      (T_True)
                  ⊢ true ∈ Bool

                 ---------------                      (T_False)
                 ⊢ false ∈ Bool

        ⊢ t1 ∈ Bool    ⊢ t2 ∈ T    ⊢ t3 ∈ T
    --------------------------------------------      (T_If)
           ⊢ if t1 then t2 else t3 ∈ T

                    ---------                         (T_0)
                    ⊢ 0 ∈ Nat

                   ⊢ t1 ∈ Nat
                 ---------------                      (T_Succ)
                 ⊢ succ t1 ∈ Nat

                   ⊢ t1 ∈ Nat
                 ---------------                      (T_Pred)
                 ⊢ pred t1 ∈ Nat

                   ⊢ t1 ∈ Nat
                 ------------------                   (T_Iszero)
                 ⊢ iszero t1 ∈ Bool
```

정의를 자세히 살펴보면, `0`과 `true`, `false` 같은 기초적인 값들은 타입을 직접 부여했고, `succ`과 `pred`, `iszero`등의 함수는 인수와 반환값의 타입을 정의했습니다. 또한 `if`의 타입도 정의했습니다. 이 언어에서 `if`는 문(statement)이 아니고 식(expression)이거든요. Coq으로 정의하면 아래와 같습니다.

```line_num
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- <{ true }> \in Bool
  | T_False :
       |- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |- t1 \in Nat ->
       |- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |- t1 \in Nat ->
       |- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |- t1 \in Nat ->
       |- <{ iszero t1 }> \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.
```

방금 정의한 타입은 보수적(conservative)입니다. 타입이 맞을 때는 맞다고 알려주지만 틀렸을 때는 아무런 정보도 주지 않습니다. 아래의 예시를 보겠습니다.

```coq, line_num
Example has_type_not :
  ~ ( |- <{ if false then 0 else true}> \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

Example has_type_not2 :
  ~ ( |- <{ if false then 0 else true}> \in Nat ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.
```

`if false then 0 else true`라는 식의 타입은 정의할 수 없습니다. 하지만 Coq은 이 식의 타입을 정의할 수 없다는 건 안 알려주고 이 식이 `Bool`도 아니고 `Nat`도 아니라고만 합니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-6. Small-Step Operational Semantics](Chap14-6.html)

[[/left]]

[[right]]

[Chapter 15-2. TODO](Chap15-2.html) >>

[[/right]]