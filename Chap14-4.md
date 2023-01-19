| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proof Automation

## 정의

본격적으로 증명을 자동화하기에 앞서 `verification_conditions`라는 타입을 정의하겠습니다. `verification_conditions`는 precondition과 `dcom` 하나를 받아서 걔네로 만든 hoare triple이 참인지 아닌지를 나타내는 명제를 반환합니다. 정의를 먼저 보고 설명하겠습니다.

```coq, line_num
Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (P ->> post d)
      /\ ((post d /\ b) ->> Pbody)%assertion
      /\ ((post d /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.
```

- `DCSkip Q => (P ->> Q)`
  - `{P} skip {Q}`라는 형태의 hoare triple이 있을 경우, `skip`은 아무것도 하지 않기 때문에 `P`만 가지고 `Q`를 만들어낼 수 있어야 합니다. 그래서 `P ->> Q`를 확인합니다.
- `DCSeq d1 d2`
  - `{P} d1 {post d1} d2`의 경우, `P`가 `d1`의 precondition으로 오는게 가능해야 하고, `d1`의 postcondition이 `d2`의 precondition으로 오는 것도 가능해야 합니다. 그걸 확인합니다.
- 나머지 경우들도 [14-2 단원](Chap14-2.html)에서 봤던 정의들을 그대로 표현하고 있습니다.

`verification_conditions P d`가 참이면 `P`와 `d`로 만든 hoare triple도 참일까요? 당연히 참이겠지만, 증명을 하고 넘어가야겠죠? 책에서도 당연히 참이라는 사실만 강조하고 증명은 그닥 중요하게 소개하지 않으니, 그냥 넘어가겠습니다.

```coq, line_num
Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof. (* 생략 *) Qed.
```

이제 거의 다 왔습니다. `Assertion`과 `dcom`을 갖고 hoare triple을 만들었으니 `decorated`를 갖고도 hoare triple을 만들어봅시다.

```coq, line_num
Definition verification_conditions_dec
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec ->
  outer_triple_valid dec.
Proof. (* 생략 *) Qed.
```

좋습니다. 이제 장식된 프로그램을 만들어서 `verification_correct_dec`에 넣어주기만 하면 프로그램의 스펙을 검증할 수 있습니다.

## 자동화

귀찮은 정의들은 이미 끝났으니, 자동화는 놀라울 정도로 간단합니다. 아래의 예시를 봅시다.

```coq, line_num
Definition swap_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.

Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof.
  intros;
  apply verification_correct;
  verify_assn.
  Qed.
```

장식된 프로그램을 Coq에게 던져주고 조건들이 유효한지를 물었습니다. 먼저, `verification_correct`를 이용해서 assertion과 명령어 사이의 관계들이 유효한지를 다 검사합니다. 검사하고 남은 찌꺼기들은 `verify_assn` tactic이 전부 처리합니다.

## Loop Invariants

위에서는 장식된 프로그램을 Coq에게 줬죠? 사실 장식이 안 돼있고 가장 첫 precondition과 마지막 postcondition만 있는 순수 hoare triple이어도 중간 단계의 assertion들을 찾는 건 어렵지 않습니다. [14-2 단원](Chap14-2.html)에서 봤던 규칙들을 이용해서 기계적으로 찾을 수 있거든요. 기계적으로 찾을 수 없는 게 딱 하나 있습니다. 바로, loop invariant를 찾는 것입니다. 아래의 예시 프로그램을 보면서 설명하겠습니다.

```line_num
{{ X = m /\ Y = n }}
  while X <> 0 do
    Y := Y - 1;
    X := X - 1
  end
{{ Y = n - m }}
```

저 조건들이 참인 건 사람 눈에는 자명해 보입니다. 어떻게 assertion을 넣어야 Coq이 한번에 증명할 수 있을까요? 손으로 assertion들을 넣어봅시다.

```line_num
{{ X = m /\ Y = n }}  ->>
{{ Inv }}
  while X <> 0 do
          {{ Inv /\ X <> 0 }}  ->>
          {{ Inv [X |-> X-1] [Y |-> Y-1] }}
    Y := Y - 1;
          {{ Inv [X |-> X-1] }}
    X := X - 1
          {{ Inv }}
  end
{{ Inv /\ ~(X <> 0) }}  ->>
{{ Y = n - m }}
```

대입 전후의 assertion은 기계적인 방법으로 찾을 수 있지만 loop invariant를 찾아내는 간단한 알고리즘은 없습니다. 그래서 일단은 loop invariant를 찾지 못하고 `Inv`라는 이름을 붙여놓았습니다. `Inv`를 찾는 똘똘한 방법이 없을까요? `Inv`가 만족해야하는 조건들을 생각해봅시다.

- 먼저, 1번 줄에서 2번 줄로 가는 `->>`가 유효해야 합니다. `Inv` 조건이 너무 빡빡하면 힘들겠죠.
- 또한, 11번 줄에서 12번 줄로 가는 `->>`도 유효해야 합니다. `Inv` 조건이 너무 약하면 힘들겠죠.
- 마지막으로, loop-invariant라는 이름에서 보듯 while문 안에서 `Inv`가 계속 성립을 해야합니다. 즉, 4번 줄에서 5번 줄로 가는 `->>`가 유효해야 합니다.

음, 저걸 어떻게 찾을까요... Coq은 고사하고 인간이 찾는 것도 힘들어 보입니다. 사람이 찾는 방법은 2가지입니다.

1. 직관을 이용한다.
1. 될 때까지 해본다.

보통은 두가지를 섞어서 쓰죠. 가장 간단해보이는 조건 (예: `Inv`가 `True`일까?)에서 시작을 하고, 성공할 때까지 계속 시도해보는 것입니다. 실패할 때마다 거기서 알게된 지식을 다음 시도에 반영하고요. 위의 예시에서도 `Inv`가 `Y - X = n - m`이면 모든 조건을 만족합니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-3. Decorations](Chap14-3.html)

[[/left]]

[[right]]

[Chapter 14-5. Hoare Logic as a Logic](Chap14-5.html) >>

[[/right]]