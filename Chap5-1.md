| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Apply

5장에서는 더 다양한 tactic들을 살펴보겠습니다.

## apply

황당한 예시와 함께 5장을 시작해보겠습니다. 아래를 봅시다.

```haskell, line_num
Theorem ridiculous: forall (a b c d: nat),
  a = b ->
  (a = b -> c = d) ->
  c = d.
```

위의 theorem을 증명하는 것은 아주 직관적입니다. `rewrite`를 2번 쓰면 끝입니다. 아래처럼요.

```haskell, line_num
Proof.
  intros a b c d eq1 eq2.
  rewrite eq2.
  reflexivity.
  rewrite eq1.
  reflexivity.
  Qed.
```

[[anchor, id = keyword apply]][[/anchor]]

간단하긴 하지만 더 간단한 방법이 있어보입니다. 증명을 하다보면 `rewrite` 뒤에 `reflexivity`가 바로 따라오는 경우가 많아요. 그런 상황을 간단하게 처리할 수 있는 tactic이 없을까요? 바로 `apply` tactic이 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Proof.
  intros a b c d eq1 eq2.
  apply eq2.
  apply eq1.
  Qed.
```

동일한 theorem을 `apply`를 이용해서 증명한 예시입니다. 코드가 훨씬 간결해진 걸 확인할 수 있습니다. 좀 더 복잡한 예시를 보겠습니다.

```haskell, line_num
Theorem less_ridiculous : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.

Proof.
  intros p eq1 eq2 eq3.
  apply eq2.  (*{- forall n : nat, even n = false -> odd n = true -}*)
  apply eq1.  (*{- forall n : nat, even n = true -> even (S n) = false -}*)
  apply eq3.  (*{- even p = true -}*)
  Qed.
```

`apply`들의 순서를 바꿔보면, 다른 순서는 증명이 안됩니다. CoqIDE를 이용해서 직접 증명을 따라가보면 매 tactic마다 딱맞는 모양들이 나오는 걸 볼 수 있으실겁니다.

## apply with

```haskell, line_num
Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
  Qed.
```

[[anchor, id = keyword apply with]][[/anchor]]

앞으로 증명을 하면서 위의 성질을 쓸 일이 아주 많을 겁니다. 그래서 지금 정의해놓고 앞으로 필요할 때마다 `trans_eq`를 사용하기로 했습니다.

```haskell, line_num
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq.
```

이게 웬걸? 위의 코드는 에러가 납니다. `apply trans_eq`를 하면 Coq는 주어진 조건들에서 `m`을 찾으려고 시도합니다. 하지만 지금 증명하려는 식에는 `m`이 없습니다. `m`이 뭔지 알려주려면 어떻게 해야할까요? 아래와 같이 증명하면 됩니다.

```haskell, line_num
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1.
  apply eq2.
  Qed.
```

`apply trans_eq with (m := [c;d])`라는 tactic을 통해서 `m` 자리에 `[c;d]`를 넣고 쓰면 된다고 Coq에게 명시적으로 알려주었습니다. 그럼 문제없이 `apply`를 사용할 수 있습니다. Coq는 추론능력이 뛰어나기 때문에 `apply trans_eq with [c;d]`라고만 해도 위의 증명이 문제없이 됩니다. 명시적인 걸 좋아하면 `m := [c;d]`를, 아니면 `[c;d]`를 쓰면 될 것 같습니다.

[[box]]

[[anchor, id = keyword transitivity]][[/anchor]]

위에서본 `trans_eq`는 워낙 자주 등장하는 성질이라 Coq에 기본적으로 정의돼 있습니다. 바로 `transitivity` tactic입니다.

```
Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1.
  apply eq2.
  Qed.
```

위의 증명에서 `transitivity`는 `apply trans_eq with`와 같습니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap4-2. Higher Order Fuctions](Chap4-2.html)

[[/left]]

[[right]]

[Chap5-2. 가제](Chap5-2.html) >>

[[/right]]