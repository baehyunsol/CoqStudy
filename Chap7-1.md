| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Inductively defined Propositions

제목에서 알 수 있듯, 이번 장에서는 `Inductive` 키워드를 집중적으로 살펴볼 예정입니다.

## 콜라츠 추측

책에서는 콜라츠 추측을 이용해서 예시를 듭니다. 콜라츠 추측은 아주 간단하니 설명은 생략하겠습니다. 혹시 콜라츠 수열이 뭔지 모르시는 분들은 [인터넷](https://en.wikipedia.org/wiki/Collatz_conjecture)을 참고해주세요.

콜라츠 추측을 Coq로 표현하려면 어떻게 해야할까요? 먼저 콜라츠 함수를 아래와 같이 정의해보겠습니다.

```haskell, line_num
Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.
```

아주 간단하군요. 그럼 콜라츠 수열이 항상 1로 끝난다는 사실을 Coq로 표현하려면 어떻게 할까요?

```haskell, line_num
Fixpoint reaches_1 (n : nat) :=
  if n =? 1 then true
  else reaches_1 (f n).

Conjecture collatz : forall n, reaches_1 n.
```

아주 간단하게 써봤습니다. `n`이 1에 도달했으면 `true`를 반환하고 아직 1이 아니면 `f n`이 1인지 재귀적으로 확인합니다. 그렇게 해서 모든 `n`이 1에 도달하면 콜라츠 추측이 참이겠죠.

아쉽지만 위의 코드는 Coq가 허락해주지 않습니다. Coq는 `Fixpoint`를 쓸 때 재귀가 유한한지 확인합니다. 하지만 `reaches_1`의 재귀가 유한한지 확인하는 건 콜라츠 추측을 증명하는 것과 동치죠, Coq가 할 수 있을 리가 없습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-5. Axioms](Chap6-5.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]