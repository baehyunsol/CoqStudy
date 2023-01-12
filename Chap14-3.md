| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Decorations

## 복습

### 예시 1

지난 시간에 배운 걸 복습도 할 겸, 간단한 프로그램 하나를 갖고 와서 동작을 증명해보겠습니다.

```line_num
X := m;
Z := p;

while X <> 0 do
  Z := Z - 1;
  X := X - 1
end
```

위의 프로그램을 실행하면 어떻게 될까요? `Z`에서 `m`을 빼니까 최종적으로 `Z = p - m`이 되겠죠. 그걸 hoare triple로 표현해보면 아래와 같습니다.

```line_num
{True}
X := m;
Z := p;

while X <> 0 do
  Z := Z - 1;
  X := X - 1
end
{Z = p - m}
```

저 hoare triple이 제대로 된 건지를 지난 시간에 정의한 정리들을 이용해서 증명해보겠습니다. 일단은 손으로 해봅시다.

```line_num
    {True} ->>
    {m = m}
  X := m;
    {X = m} ->>
    {X = m /\ p = p}
  Z := p;

    {X = m /\ Z = p} ->>
    {Z - X = p - m}
  while X <> 0 do
      {Z - X = p - m /\ X <> 0} ->>
      {(Z - 1) - (X - 1) = p - m}
    Z := Z - 1;
      {Z - (X - 1) = p - m}
    X := X - 1
      {Z - X = p - m}
  end

    {Z - X = p - m /\ ~(X <> 0)} ->>
    {Z = p - m}
```

조금 복잡하죠? 지난 단원에서 Coq으로 하던 걸 손으로 표현한 겁니다. 한 줄씩 뜯어보겠습니다.

1. 처음에는 1번줄과 20번줄만 가지고 시작합니다. 20번줄부터 시작해서 assertion을 하나씩 추가해가면서 최종적으로 1번줄에 도달할 수 있는지 확인하겠습니다.
1. 20번 줄에 `hoare_while`을 사용하기 위해선 그에 맞는 형태로 바꿔줘야합니다. 그래서 19번 줄을 선언했습니다.
  - 19번 줄을 증명하면 20번 줄도 증명이 된다는 사실은 `hoare_consequence_post`를 사용해서 보일 수 있습니다.
1. `hoare_while`은 loop invariant를 하나 필요로 하죠? 저희가 고른 loop-invariant는 9번 줄의 assertion입니다.
1. loop가 한 단계 진행할 때마다 loop invariant가 변하지 않는다는 걸 보여야 합니다. 그게 11 ~ 16번 줄입니다.
  - 16번 줄에는 19번 줄의 loop invariant가 그대로 들어갔습니다.
  - 14번과 12번 줄은 각각 `hoare_asgn`을 이용해서 만들었습니다.
  - loop invariant와 loop의 조건만을 이용해서 12번 줄을 만들어낼 수 있음을 11번 줄에서 보였습니다.
1. 그 윗부분은 1 ~ 6번 줄을 이용해서 loop invariant를 만들 수 있음을 보이는 과정입니다.
  - 정확히 말하자면, 9번 줄에다가 `hoare_asgn`을 2번 해서 1번 줄까지 갈 수 있음을 보였습니다.

### 예시 2

재밌죠? 하나 더 해봅시다.

```line_num
{X = m /\ Y = n}
X := X + Y;
Y := X - Y;
X := X - Y
{X = n /\ Y = m}
```

임시 변수 없이 두 변수의 값을 바꾸는 아주 유명한 트릭입니다. 저 트릭이 제대로 동작하는지 확인해봅시다.

```line_num
  {X = m /\ Y = n} ->>
  {(X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m}
X := X + Y;
  {X - (X - Y) = n /\ X - Y = m}
Y := X - Y;
  {X - Y = n /\ Y = m}
X := X - Y
  {X = n /\ Y = m}
```

이번에는 아주 간단합니다.

1. 8번 줄에서 `hoare_asgn`을 사용해서 6번 줄을 만듭니다.
1. 6번 줄에서 `hoare_asgn`을 사용해서 4번 줄을 만듭니다.
1. 4번 줄에서 `hoare_asgn`을 사용해서 2번 줄을 만듭니다.
1. 2번 줄과 1번 줄이 포함관계가 있어야 전체 증명이 말이 되므로 `->>`를 하나 추가해줍니다.

### 예시 3

마지막으로 하나만 더 해보겠습니다.

```line_num
{True}
while X <> 0 do
  X := X - 1
end
{X = 0}
```

```line_num
  {True}
while X <> 0 do
    {True /\ X <> 0} ->>
    {True}
  X := X - 1
    {True}
end
  {True /\ ~(X <> 0)} ->>
  {X = 0}
```

아주 간단합니다. 저희의 목표는 9번 줄에서 출발해서 1번 줄로 도착할 수 있음을 보이는 것입니다. 그러기 위해선 `hoare_while`을 사용해야 하는데 그에 맞는 형태의 assertion을 만들기 위해서 8번줄을 추가했습니다. 9번 줄이 8번 줄을 포함한다는 것은 `hoare_consequence`를 이용해서 보이면 됩니다. 그다음, loop 안의 각 명령어들을 지나갈 때마다 loop invariant가 참이라는 것을 보였습니다. 여기선 loop invariant가 `True`여서 딱히 증명해야할 게 없습니다.

## Formal Decoration

Decoration에 대해서 설명하기 전에, 방금 손으로 증명했던 것들을 Coq으로 증명해보겠습니다. 그 전에 유용한 tactic 하나를 정의하고 넘어가겠습니다.

```line_num
Ltac verify_assn :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [ | (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.
```

무시무시하죠? hoare와 직접적으로 관련되지 않은 부분들을 한번에 정리해주는 tactic입니다. 교과서의 저자가 만들어주신 건데 자세한 내용은 이해할 필요없다고 하시네요.

먼저 가장 쉬운 [예시3](#예시-3)부터 증명해보겠습니다.

```coq, line_num
Theorem ex3_correct :
  {{True}}
    <{ while X <> 0 do
      X := X - 1
    end }>
  {{X = 0}}.
Proof.
  eapply hoare_consequence_post.
  - (* {True} while_loop {?Q'} *)
    apply hoare_while.
    + (* { loop_inv /\ start } loop_body { loop_inv } *)
      eapply hoare_consequence_pre.
      * (* {?P'} X := X - 1 {True} *)
        apply hoare_asgn.
      * (* True /\ X != 0 ->> True [X |-> X - 1] *)
        verify_assn.
  - (* True /\ ~ X != 0 ->> X = 0 *)
    verify_assn.
Qed.
```

손으로 했던 증명과 동일한 순서로 진행되는 것을 볼 수 있습니다.

긴 프로그램의 증명을 하기 위해서 명령어들 사이에 추가적인 assertion들을 적었죠? 이걸 장식(decoration)이라고 합니다. 장식들을 Coq의 문법을 이용해서 적을 수 있으면 증명을 거의 자동으로 할 수 있습니다. 그래서, 장식들을 Coq으로 정의하는 과정을 먼저 살펴보겠습니다.

### `dcom`

명령어에 assertion들이 포함된 type을 Coq으로 만들어봅시다. 이름은 *decorated command*를 줄여서 `dcom`이라고 하겠습니다. 단순하게 모든 명령어마다 precondition과 postcondition을 추가해주는 방식으로 만드는 것은 문제가 있습니다. `skip; skip`이라는 명령어가 있다고 생각해보세요. 저 명령어의 `dcom`은 아래와 같은 모양일 겁니다.

> `{P} ({P} skip {P});({P} skip {P}) {P}`

아주 높은 확률로 모든 assertion은 동일한 형태일 겁니다. 한번만 써도 될 걸 6번이나 썼죠? 프로그래밍 하는 사람들이 제일 싫어하는게 불필요한 반복입니다. 저걸 없애보겠습니다.

- `skip {Q}`
  - `skip`은 postcondition만 적겠습니다.
  - `skip`의 precondition은 다른 맥락을 보고 알 수 있는 상황이 아주 많거든요. 다른 명령어들도 마찬가지로 precondition은 생략하겠습니다.
- `d1; d2`
  - 명령어가 연속으로 올 때, `;`로 인해서 생기는 assertion은 적지 않겠습니다.
  - `d1`과 `d2`도 `dcom`이기 때문에 각각 자신의 assertion이 포함돼 있습니다. 그래서 추가로 assertion을 적을 필요가 없어요.
- `if b then {P1} d1 else {P2} d2 end {Q}`
  - `if`는 각 경우의 precondition과 if문 전체의 postcondition만 적겠습니다.
- `while b do {P} d end {Q}`
  - `while`은 내부의 precondition과 전체의 postcondition만 적겠습니다.
  - 저기 들어간 `P`는 loop invariant입니다.
- `->> {P} d`, `d ->> {Q}`
  - 어떤 `d`에 대해서 `->>`를 이용해서 추가적인 assertion을 제공할 수 있습니다.
  - 전자의 경우는 외부에서 precondition을 따로 제공해줘야 `{P'} ->> {P} d`와 같은 형태가 돼서 말이 되고요,
  - 후자의 경우는 `d` 안에 있는 postcondition 덕분에 말이 됩니다.

저 정의를 Coq으로 옮겨보면 아래와 같습니다.

```coq, line_num
Inductive dcom : Type :=
| DCSkip (Q : Assertion)
| DCSeq (d1 d2 : dcom)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
| DCPre (P : Assertion) (d : dcom)
| DCPost (d : dcom) (Q : Assertion).
```

처음에도 말했듯이 precondition은 대부분 생략돼 있습니다. 생략된 precondition은 이전의 명령어의 postcondition을 이용해서 유추가 가능하지만 첫번째 명령어의 precondition은 유추할 수 없습니다. 이건 hoare triple을 만드는 사람이 주는 거거든요. 그래서 첫번째 명령어의 precondition을 받을 수 있도록 새로운 type을 추가하겠습니다.

```coq, line_num
Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.
```

이제 장식이된 hoare triple을 표현할 수 있는 방법이 생겼습니다. 짧은 시간 동안 많은 type들을 정의했는데, 저 type들 간에 상호 변환을 하는 함수들도 만들어줘야합니다. 지금까지 증명은 전부 `com`과 `Assertion`을 이용해서만 했으니, 저 type들로 바꿔줘야죠.

```coq, line_num
Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => CSkip
  | DCSeq d1 d2 => CSeq (extract d1) (extract d2)
  | DCAsgn X a _ => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _ => CWhile b (extract d)
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition outer_triple_valid (dec : decorated) :=
  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.
```

먼저, `extract`와 `extract_dec`은 장식된 프로그램에서 `com`만 뽑아냅니다. 마찬가지로 `pre_dec`, `post`, `post_dec`은 장식된 프로그램에서 precondition이나 postcondition을 뽑아냅니다. 위에서 설명했듯 `dcom`은 precondition을 포함하지 않기 때문에 `pre`는 없습니다.

마지막으로, `outer_triple_valid`는 장식된 프로그램을 `hoare_triple`로 바꿔줍니다.

뒷장에서 계속 나오는 함수들이니 잘 익혀둡시다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-2. Proof Rules](Chap14-2.html)

[[/left]]

[[right]]

[Chapter 14-4. Proof Automation](Chap14-4.html) >>

[[/right]]