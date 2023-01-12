| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Hoare Logic

이번 장부터는 Hoare Logic에 대해서 공부하겠습니다. Hoare Logic은 어떤 프로그램의 동작을 수학적으로 표현하는 방법 중 하나입니다. Hoare Logic을 간단하게 표현해보면 ~_X라는 조건(들)을 만족하는 프로그램이 Y라는 동작을 하고 나면 Z라는 조건(들)을 만족한다_~ 정도가 됩니다. 예를 들어서 정렬을 하고 나면 (Y), 배열의 숫자들이 순서대로 있겠죠(Z).

## Assertions

Hoare Logic에선 조건들이 나온다고 했죠? 조건들을 Coq에서 나타내는 방식이 바로 Assertion입니다. 다른 언어로 프로그래밍을 해본 적이 있으시면 테스트를 짜면서 assert 구문을 많이 봤을 텐데 바로 그 assert입니다.

```coq
Definition Assertion := state -> Prop.
```

`Assertion`은 `state`를 받아서 `Prop`을 반환하는 함수입니다. 아래에서 몇가지 예시들을 보겠습니다.

- `fun st => st X = 3`
  - `X`의 값이 3인 `st`들은 해당 assertion을 만족합니다.
- `fun st => True`
  - 모든 `st`는 해당 assertion을 만족합니다.
- `fun st => False`
  - 어떤 `st`도 해당 assertion을 만족하지 않습니다.

문법이 살짝 장황하죠? 앞으로는 축약해서 쓰겠습니다. `fun st => st`는 항상 등장하니 생략하고, `X = 3`만 쓰겠습니다. 또한, 이제부터 대문자 `X`, `Y`, `Z`는 Imp의 변수고 소문자들은 Coq의 변수(`nat`)라고 간주하겠습니다.

Assertion 사이에는 포함관계가 있을 수도 있습니다. 아래를 봅시다.

```coq, line_num
Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
```

`P`라는 assertion이 참일 때 `Q`도 항상 참인 경우, `P ->> Q`라고 표현하기로 했습니다. 하는 김에 Notation들을 더 정의해보겠습니다.

```coq, line_num
Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).
Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).
```

무슨 뜻인지는 저도 잘 몰라요. 몇가지만 보자면, Coq의 문법의 한계로 assertion 안에서 함수 호출이 깔끔하게 되지 않습니다. 그래서 `ap`, `ap2`라는 함수호출함수를 만들었습니다. Assertion 안에서 함수를 호출하려면 `ap2 max X Y`와 같은 형식으로 해야합니다.

## Hoare Triples

Hoare Logic을 표현하는 대표적인 방식은 Hoare Triple입니다.

> [[giant]]{P} c {Q}[[/giant]]

라고 쓰면 아래와 같은 뜻입니다.

1. Assertion `P`를 만족하는 상태에서
1. c를 실행한다
1. c가 종료되면서 상태가 변한다.
1. 새로운 상태는 assertion `Q`를 만족한다.

예를 들어서, `{X = 0} X := X + 1 {X = 1}`이란 Hoare Triple이 있다고 합시다. 이 triple은 말이 됩니다. 한국말로 번역하자면 ~_X가 0일 때 X에 X + 1을 대입하면 X는 1이 된다_~가 되거든요. 말이 되죠?

저 정의에서 `P`를 precondition이라고 하고 `Q`를 postcondition이라고 합니다.

방금은 한국말로 정의한 Hoare Triple이었고, 이젠 Coq로 정의해봅시다. 아래를 봅시다.

```coq, line_num
Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Check ({{True}} X := 0 {{True}}).
```

Coq을 통해서 Hoare Triple을 정의했습니다. 중괄호가 이미 사용 중인 기호여서 부득이하게 이중 중괄호를 사용했습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 13-3. Program Transformation](Chap13-3.html)

[[/left]]

[[right]]

[Chapter 14-2. Proof Rules](Chap14-2.html) >>

[[/right]]