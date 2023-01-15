| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Basics

이번 단원에서는 프로그래밍 언어의 아주 큰 주제 중 하나인 type system에 대해서 공부하겠습니다. 언제나 그랬듯이 간단한 언어를 하나 정의하고 그 언어를 통해서 개념을 공부하겠습니다.

## tm

이번에 정의할 언어는 14단원 [끝자락](14-6.html#tm)에서 정의한 tm과 비슷하게 생겼습니다. 다만 tm은 너무 단순해서 type을 정의할 수가 없으니 bool과 자연수 type을 가지는 좀 더 복잡한 언어를 정의해봅시다.

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

각 상황마다 다음 단계로 넘어가는 step을 정의했습니다. Type이 맞지 않은 식을 넣으면 (예: `succ if true then true else false`), 할 수 있는한 최대한 step을 많이 밟은 후, 상수가 되지 못하고 멈추게(stuck) 됩니다. (예: `succ true`)

이번 tm은 14장의 tm과 다르게 멈추는 경우가 있으므로 normal form과 관련된 정의도 다시 해줘야합니다.

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