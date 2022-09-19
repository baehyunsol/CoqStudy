| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proofs within proofs

Rust 코드 예시로 시작하겠습니다. 아래의 두 코드를 비교해봅시다.

```rust, line_num
fn main() {
    (0..100).map(|n| n + 1);
}
```

```rust, line_num
fn add1(n: usize) -> usize {
    n + 1
}

fn main() {
    (0..100).map(add1);
}
```

위의 코드들은 동일한 동작을 수행하지만, 첫번째 코드가 훨씬 깔끔합니다. `add1`을 한번만 사용할 거라면 굳이 이름을 지을 필요가 없거든요. Coq에서도 비슷한 상황들이 많습니다. 큰 theorem을 증명하기 위해서 작은 sub-theorem들이 필요할 일이 있는데, 매번 `Theorem` 키워드로 이름을 짓고 `Proof` 키워드로 증명하긴 귀찮습니다.

또한, 함수형 언어를 사용해본 적이 있는 분들은 closure를 사용해본 적이 있을 겁니다. Closure는 단순 anonymous function을 넘어서 또다른 기능을 제공해줍니다. Coq에서도 closure와 비슷한 기능이 필요할 때가 있어요.

그래서 Coq는 `assert`라는 tactic을 제공합니다. 아래의 예시[^by]를 보겠습니다.

[[anchor, id = keyword assert]][[/anchor]]

```haskell, line_num
Theorem mult_0_plus : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.
```

`assert`라는 tactic을 이용해서 sub-theorem 하나를 정의했습니다. `assert` 뒤의 중괄호에는 해당 sub-theorem의 증명이 들어갑니다. 이렇게 하면 context에 `H: n + 0 + 0 = n`이 들어갑니다.

[^by]: 책에 있는 예제를 그대로 갖고 왔는데 예제를 위한 예제라는 느낌이 강하게 드네요.

## Smarter `rewrite`

이번에는 좀더 실용적인 예제를 보여드리겠습니다.

```haskell, line_num
Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
```

아주 간단하죠? 저희가 해야할 일은 `(n + m)`을 `(m + n)`으로 바꾸는 것밖에 없습니다. [이전](Chap2-1.html#theoremaddcomm)에 증명했던 `add_comm`을 사용하면 간편하겠군요. 아쉽게도 그렇지 않습니다. `rewrite add_comm`은 어떤 덧셈에 교환법칙을 적용해야할 지 모릅니다. 저희는 괄호 안의 덧셈을 바꾸고 싶지만 Coq는 괄호 밖의 덧셈을 바꿉니다.

이런 상황에 `assert`를 유용하게 쓸 수 있습니다.

```haskell, line_num
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
```

`assert` 안에 등장하는 `n`과 `m`은 아까 `intros`에서 언급했던 그 `n`과 `m`입니다. 실제로 `H`를 `H: x + y = y + x`라고 쓰면 실행이 되지 않습니다. 똑같은 식처럼 보이지만 context 안에 `x`와 `y`가 없거든요.

이 방법으로 `add_comm`을 어떤 덧셈에 적용시킬지 정확히 정할 수 있습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap2-1. Proofs by induction](Chap2-1.html)

[[/left]]

[[right]]

[Chap2-3. Binary](Chap2-3.html) >>

[[/right]]