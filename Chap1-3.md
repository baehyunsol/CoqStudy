| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Proofs

Coq는 *theorem prover*입니다. 즉, 증명이 핵심입니다. 아쉽게도 Coq가 증명을 대신 해주지는 않습니다. 사람이 theorem을 입력하고 그걸 증명하는데 사용할 전략들을 알려주면 Coq가 증명을 *보조*해줍니다. 이번 챕터에서는 증명의 전략들을 알아보겠습니다.

## By Simplification

[[anchor, id=ex1]][[/anchor]]

```haskell, line_num
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
```

위의 코드는 Coq를 이용한 간단한 증명과정을 나타냅니다.

1. 먼저, `Theorem` 키워드를 이용해서 정리를 정의합니다.
  - 여기서는 `plus_O_n`이라는 정리를 정의했습니다.
  - 정리의 내용은 '*모든 자연수 n에 대해서 0 + n = n이다*'입니다.
1. 바로 다음에 `Proof` 키워드를 이용해서 `plus_O_n`을 증명합니다.
1. `Proof` 키워드 다음에 증명에 쓰일 tactic이 쭉 나오고, `Qed` 키워드를 이용해서 증명이 끝났음을 선언합니다.

각 tactic이 무슨 역할을 하는지는 아래의 [키워드 정리](#키워드-정리)에서 자세하게 설명하겠습니다.

## By Rewriting

[[anchor, id=ex2]][[/anchor]]

```haskell, line_num
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  intros n m.    (*{- n m : nat -}*)
  intros H.      (*{- H: n = m -}*)
  rewrite -> H.  (*{- `n + n = m + m`이 `m + m = m + m`이 됩니다. -}*)
  reflexivity.   (*{- 양변이 같음을 확인합니다. -}*)
  Qed.
```

이번에는 theorem의 형태가 조금 바뀌었죠? `->` 기호가 들어갔습니다. `->` 기호는 `p이면 q이다`의 의미를 나타내기 위해 쓰이며, *implies*라고 읽습니다.

`intros`도 2번 등장합니다. 첫번째 `intros n m`은 Theorem 속에 `forall n m`으로 돼 있는 부분을 context에 집어넣고, 두번째 `intros H`는 `p이면 q이다`의 `p`를 context에 집어넣습니다. 즉, context 안에는 `H`라는 hypothesis가 있으며, `H`의 내용은 `H: n = m`입니다.

## By Case Analysis

```haskell, line_num
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
```

위와 같은 theorem을 생각해보겠습니다. 저걸 증명하려면 어떻게 해야할까요? 여기서는 `simpl` tactic이 통하지 않습니다. 덧셈 함수의 정의상 왼쪽 피연산자가 상수여야지만 pattern matching이 가능한데 그렇지 않거든요. `eqb` 함수 입장에서도 왼쪽의 `n + 1`을 pattern matching에 넣을 방법이 없습니다.

이때 사용하는 것이 `destruct` tactic입니다. 아래 예시를 봅시다.

[[anchor, id=ex3]][[/anchor]]

```line_num
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```

이제 `n`을 `O`와 `S n'`의 두 가지 경우로 나눠서 생각합니다. `[| n']`은 `n`을 어떻게 나눌지를 정합니다. `n`의 type은 `nat`이고, `nat`의 constructor는 2개가 있으므로 우리는 대괄호 안에 두 개의 원소를 줘야합니다. 각 원소는 `|`로 구분합니다. `O`는 인수가 필요없는 constructor이므로, 첫번째 원소는 null이고 (그래서 `|` 앞에 아무것도 쓰지 않았습니다.) 두번째 원소는 `n'`을 줬습니다. 이렇게 해서 subgoal이 2개가 생겼습니다.

그러면 Coq은 `n`을 `O`와 `S n'`의 두가지 경우로 나눠서 생각하고, 저희는 각 경우에 대해서 증명을 하면 됩니다. 뒤의 `eqn: E`로 인해 context에 `E`가 추가됐습니다. 각 경우별로 `E: n = 0`과 `E: n = S n'`으로 생성이 됩니다. 또한 저희가 증명해야할 문제는 `(0 + 1 =? 0) = false`과 `(S n' + 1 =? 0) = false`이 됩니다.

그 다음의 `-`는 각 subgoal을 풀 tactic을 보여줍니다. 여기서는 각각 `reflexivity`만으로 증명이 되니까 상관이 없지만, 각 subgoal을 증명하는 과정이 길어질 경우 하나의 증명을 마치고 `-`를 쓰고 다음 증명을 시작하면 됩니다. 이렇게 2개의 subgoal을 풀고 나면 전체가 증명이 끝납니다. `-`은 쓰지 않아도 됩니다. 다만, 가독성을 위해서 쓰는 것을 권장합니다.

## 키워드 정리

[[box]]

[[anchor, id=keyword destruct]][[/anchor]]

[[giant]]destruct[[/giant]]

예시에 자세히 설명이 돼 있으니 아래 링크를 참고해주세요.

위에서 쓰지 않았던 또다른 예시를 보여드리겠습니다.

```haskell, line_num
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```

`bool` type은 variant가 2개밖에 없습니다. 또한, 각 variant의 constructor는 인수가 0개라서 `as`와 대괄호를 쓸 필요가 없습니다. 위와 같은 방식으로 증명을 하면, Coq은 theorem에다가 `true`와 `false`를 각각 집어넣어서 식이 성립하는지 확인합니다.

또다른 예시를 보여드리겠습니다.

```haskell
Theorem andb_commutative : forall b c, andb b c = andb c b.
```

위와 같은 theorem을 증명하려면 어떻게 해야할까요? `b`와 `c`로 가능한 모든 경우의 수가 4가지밖에 없으니 브루트포스로 검증하는게 합리적입니다.

```haskell, line_num
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```

그래서 위와 같이 2번째 줄에서 `b`를 `true`와 `false`로 나눈 뒤, 각각의 경우에 대해 `c`를 destruct하여 (3, 6번 줄) 모든 경우의 수를 따졌습니다. `b`, `c`의 값이 각각 확정되면 `reflexivity` tactic만을 이용해서 손쉽게 증명할 수 있습니다. `andb`의 정의에 직접 대입하면 결과가 나오거든요.

- [예시1](#ex3)

[[/box]]

[[box]]

[[anchor, id=keyword theorem]][[/anchor]] [[anchor, id=keyword example]][[/anchor]]

[[giant]]Theorem, Example[[/giant]]

참이라고 주장하고 싶은 정리를 선언하는데 쓰입니다. `Theorem`과 `Example`은 semantic한 차이가 거의 없다고 문서에 나와있습니다. 문맥에 따라서 사람이 읽기 쉬운 키워드를 고르면 될 듯 합니다. 책에서는 `Theorem`이 수학적 증명에 가깝고, `Example`은 unit test에 가까운 용례로 쓰이는 듯 합니다.

`Theorem`이나 `Example`의 뒤에는 바로 `Proof`가 와서 증명을 제공해야합니다.

```haskell, line_num
Example test_even1: is_even 2 = true.
Theorem plus_O_n : forall n : nat, 0 + n = n.
```

위의 예시들은 책에서 쓰인 용례들을 그대로 갖고 온 것입니다. 책에서 `Theorem`과 `Example`을 어떤 뉘앙스로 사용하는지 확인하실 수 있습니다. 또한 저 용례에서 `Example`과 `Theorem`을 뒤바꿔서 실행해도 문제없이 돌아갑니다.

`Lemma`, `Fact`, `Remark` 등의 키워드들도 위 키워드들과 거의 비슷한 역할을 합니다.

- [stackoverflow](https://stackoverflow.com/questions/60101214/what-is-the-difference-between-definitions-and-theorems)
- [예시1](#ex1)
- [예시2](Chap1-2.html#ex1)
- [예시3](#ex2)

[[/box]]

[[box]]

[[anchor, id=keyword intros]][[/anchor]][[anchor, id=keyword intro]][[/anchor]]

[[giant]]intros, intro[[/giant]]

`intro` 키워드에 복수형 s가 붙은 형태입니다. 원래 `intro` 키워드는 한번에 하나만 *introduce* 할 수 있지만 `intros`는 여러 개를 introduce 할 수 있습니다. 여기서 둘이 동시에 설명하겠습니다.

`intro` 키워드는 Theorem에 있는 식들을 context에 넣습니다. Theorem에 `forall n, m: nat`이 있을 때 `intros n m`을 하면 `n`과 `m`이 context에 들어가고, 그때부터 증명과정에서 `n`과 `m`을 사용할 수 있게 됩니다. `n`과 `m`이 아닌 다른 이름을 사용해도 상관없습니다. `intros` 키워드는 이름을 기준으로 context에 넣는게 아니고, 앞에서부터 순서대로 context에 집어넣습니다. 즉, `forall n, m : nat`에다가 `intros a b`를 하면 `n`, `m`이 순서대로 `a`, `b`라는 이름으로 context에 들어갑니다.

`n = m -> n + n = m + m` 같은 경우, `n = m`이라는 명제도 context에 넣어야 증명이 가능합니다. 저 상황에서 `intros H`를 하면 context에 `H: n = m`이 들어간 것을 확인할 수 있습니다. 그럼 `rewrite H`와 같은 방식으로 `n = m`을 증명에 사용할 수 있습니다.

[[box]]

`intros`를 하면 `forall`을 없어지고 context에 들어온다는 설명을 봤는데, `forall`이 없어진다는게 정확히 무슨 의미인지 아직 모르겠습니다.

[[/box]]

- [stackoverflow](https://stackoverflow.com/questions/70482977/understanding-the-intros-keyword-work-in-coq)
- [공식 문서 참고](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.intros)
- [예시1](#ex1)
- [예시2](#ex2)

[[/box]]

[[box]]

[[anchor, id=keyword reflexivity]][[/anchor]]

[[giant]]reflexivity[[/giant]]

등식의 양변이 동일한 값을 갖고 있는지 확인합니다.

- [예시1](#ex1)

[[/box]]

[[box]]

[[anchor, id=keyword rewrite]][[/anchor]]

[[giant]]rewrite[[/giant]]

`H: n = m`을 가지고 `rewrite -> H.`를 할 경우 theorem 안의 모든 `n`을 `m`으로 rewrite합니다. 화살표를 반대방향으로 (`<-`) 쓸 경우 `m`을 `n`으로 rewrite합니다. 화살표는 생략가능하며, 생략할 경우 `->`의 방향으로 적용됩니다.

- [예시1](#ex2)

[[/box]]

[[box]]

[[anchor, id=keyword simpl]][[/anchor]]

[[giant]]simpl[[/giant]]

등식의 양변을 간단한 형태로 정리합니다.

Coq 인터프리터에 `forall n : nat, 1 + n = S n`을 넣고 `simpl` tactic을 통과시키면 goal에 있던 `1 + n = S n`이 `S n = S n`으로 바뀌는 것을 확인할 수 있습니다. 덧셈함수의 [정의](Chap1-2.html#functionnatplus)에 따르면 `(plus 1 n)`은 `(S (plus 0 n))`이고 그 값은 다시 `(S n)`이 되죠? Coq도 이 과정을 동일하게 거쳐서 `1 + n`을 `S n`으로 고칩니다.

함수의 정의에 값을 그대로 넣어서 간단한 형태로 정리한다는게 중요합니다. 만약 `1 + n = S n`이 아니라 `n + 1 = S n`을 넣고 `simpl`을 통과시키면 Coq는 아무것도 하지 못합니다. 정의를 이용해서는 첫번째 인수만 줄일 수 있거든요.

- [예시1](#ex1)

[[/box]]

---

아직 정리 안된 친구들!

[[box]]

Admitted

원래는 `Theorem` 뒤에 바로 `Proof`가 나와서 `Qed`로 마무리를 해야하는데, 증명을 나중으로 미루고 싶을 경우 `Admitted` 키워드를 사용할 수 있습니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap1-2. Natrual Numbers](Chap1-2.html)

[[/left]]

[[right]]

[Chap2-1. Proofs by Induction](Chap2-1.html) >>

[[/right]]