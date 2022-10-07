| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# 가제

## Injective and Disjoint

자연수의 정의를 다시 떠올려볼까요?

```haskell, line_num
Inductive nat : Type :=
  | O
  | S (n : nat).
```

위의 정의에서 저희는 아주 당연한 사실 2가지를 생각해볼 수 있습니다.

- `S`는 injective[^inj]합니다. 즉, `S n = S m`이면 `n = m`입니다.
- `O`와 `S`는 disjoint[^disj]합니다. 즉, `O`와 `S n'`은 항상 다릅니다.

[^inj]: 한국말로는 단사라고 합니다. 글에선 그냥 영어로 쓰겠습니다.

[^disj]: 한국말로 뭐라고 하는지 기억이 안 나네요. 글에선 그냥 영어로 쓰겠습니다.

### injection

[[anchor, id = keyword injection]][[/anchor]]

방금 설명한 injective를 구현한 tactic이 바로 `injection`입니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.
```

위의 예시에서 `n = o`와 `m = o`는 자명해보입니다. 그 자명한 걸 표현하는 tactic이 `injection H as H1 H2`입니다.\
저 tactic을 사용하고 나면 `H : [n; m] = [o; o]`가 사라지고 `H1 : n = o`와 `H2 : m = o`가 생깁니다. `injection`이 무슨 역할을 하는지 대충 감이 오죠?

### discriminate

[[anchor, id = keyword discriminate]][[/anchor]]

이번에는 아까 설명한 disjointness를 다뤄보겠습니다. Disjointness가 뭔지 다시 간략히 설명하자면, ~_`S`와 `O`는 같지 않다_~입니다. 근데 조금 이상하죠. 지금까지 증명을 하면서 `!=`나 `~=` 같은 걸 본 적이 없습니다. 그나마 있다고 해도 값들의 비교에서였지, 명제끼리 같지 않다고 말하는 건 들은 적이 없습니다. 그럼 과연 disjointness는 어디에 쓸까요?

잠시 논리학을 복습하겠습니다. ~_p이면 q이다_~에서 `p`가 거짓이면 어떻게 되죠? 그럼 묻지도 따지지도 않고 명제는 참입니다. 즉, 가정이 거짓이면 명제는 참입니다. Coq에서도 이 방식으로 disjointness를 사용합니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.

Proof.
  intros n m contra.
  discriminate contra.
  Qed.
```

위의 예시에서 `discriminate` tactic이 그 역할을 합니다. Coq에게 `discriminate contra`라는 명령을 하면 Coq는 `contra`의 가정이 거짓인지 확인하고 (이 과정에서 아까 설명한 disjointness를 사용합니다.) 가정이 거짓이라면 `contra`가 참이라고 합니다.

Using Tactics on Hypotheses부터 ㄱㄱ

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap5-1. Apply](Chap5-1.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]