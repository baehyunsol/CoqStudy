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

아주 간단한 증명입니다. loop-variant를 굳이 안 정해도 loop의 조건만 가지고도 증명이 끝납니다.

## Formal Decoration

Decoration에 대해서 설명하기 전에, 방금 손으로 증명했던 것들을 Coq으로 증명해보겠습니다. 그 전에 유용한 tactic 하나를 정의하고 넘어가겠습니다.

```haskell, line_num
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

```haskell, line_num
Theorem ex3_correct :
  {{True}}
    <{ while X <> 0 do
      X := X - 1
    end }>
  {{X = 0}}.
Proof.
  eapply hoare_consequence_post.
  - (*{- {True} while_loop {?Q'} -}*)
    apply hoare_while.
    + (*{- { loop_inv /\ start } loop_body { loop_inv } -}*)
      eapply hoare_consequence_pre.
      * (*{- {?P'} X := X - 1 {True} -}*)
        apply hoare_asgn.
      * (*{- True /\ X != 0 ->> True [X |-> X - 1] -}*)
        verify_assn.
  - (*{- True /\ ~ X != 0 ->> X = 0 -}*)
    verify_assn.
Qed.
```

손으로 했던 증명과 동일한 순서로 진행되는 것을 볼 수 있습니다.

TODO: 예시 1도 Coq으로 해보기

긴 프로그램의 증명을 하기 위해서 명령어들 사이에 추가적인 assertion들을 적었죠? 이걸 장식(decoration)이라고 합니다. 장식들을 Coq의 문법을 이용해서 적을 수 있으면 증명을 거의 자동으로 할 수 있습니다. 그래서, 장식들을 Coq으로 정의하는 과정을 먼저 살펴보겠습니다.

TODO

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-2. Proof Rules](Chap14-2.html)

[[/left]]

[[right]]

[Chapter 14-4. ??](Chap14-4.html) >>

[[/right]]