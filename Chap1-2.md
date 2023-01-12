| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Natural Numbers

첫 장을 읽으시면서 이상한 점을 느끼는 분들이 많으셨을 겁니다. 보통 프로그래밍 언어를 처음 배울 때, 그 언어의 정수 자료형, 정수 연산자 등을 배우고 시작하지만, Coq에서는 정수에 대한 언급이 전혀 없었습니다. 심지어 `==` 같은 연산자도 아직 안 나왔습니다.

Coq에서는 정수형을 아주 특이한 방식으로 다룹니다. 이번 장에서는 Coq에서 자연수를 어떻게 다루는지 살펴보겠습니다.

## 정의

Boolean이 그러했듯, 자연수도 특별한 내장함수를 쓰지 않고 Coq의 문법으로 정의할 수 있습니다. 지금까지 봤던 type들과 달리, 자연수는 무한히 많으므로 특별한 방식의 정의를 사용합니다.

```coq, line_num
Inductive nat : Type :=
  | O
  | S (n: nat).
```

정의에서 `O`는 숫자 0을 나타내고, `S n`은 0이 아닌 수를 나타냅니다. `S`는 Gye-~_S_~ueng-Ja의 머릿말로, `S n`은 `n` 다음의 수를 나타냅니다. 즉, `S O`는 `O` 다음의 수, 즉 1을 나타내고, `S (S O)`는 `O` 다음다음의 수, 즉 2를 나타냅니다. 페아노 공리계에서 자연수를 정의하는 방식과 비슷합니다.[^Peano]

이 방법으로 우리는 모든 자연수를 표현할 수 있습니다! 지금까지 보던 방식과 많이 다르죠?

[^Peano]: 제가 수학 전공자가 아니라서 자세히는 모릅니다.

[[box]]

책에선 아래 구절을 강조하고 있습니다. 저 말은 `Inductive`라는 키워드의 의미와 연관돼 있는데, [나중](Chap7-1.html)에 7장에서 자세히 다룰 예정입니다.

> `nat`을 구성하는 방법은 오직 `O`와 `S n`밖에 없고, `O`와 `S n`은 항상 `nat`이다.

[[/box]]

[[box]]

프로그래밍 언어처럼 생각하면, 위에서 정의한 `S`는 `nat -> nat`의 type을 가지는 함수입니다. Haskell에서 type을 만들면 동일한 이름으로 constructor가 생기는 것과 동일하게 생각하면 됩니다.

[[/box]]

## 기본 연산

### minus_two

Coq가 자연수를 어떻게 ***표현***하는지 살펴보았습니다. 지금까지 본 것은 representation에 불과합니다. 저걸 자연수로 받아들이려면 자연수의 여러 연산들을 구현해야합니다. `S`와 `O`만 정의했기 때문에 숫자 0과 (+ 1)함수만을 이용해서 모든 연산을 정의해야합니다. 재밌겠죠?

```coq, line_num
Definition minus_two (n: nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
```

주어진 수에서 2를 빼는 함수를 정의했습니다. 0 혹은 1은 0을 반환하고, (n + 2)는 n을 반환하도록 했습니다.

### is_even

```coq, line_num
Fixpoint is_even (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => is_even n'
  end.
```

주어진 수가 짝수인지 홀수인지 판별하는 함수를 정의했습니다. 0은 짝수이고 1은 홀수이며, (n + 2)는 n과 동일한 결과를 반환하도록 했습니다.

[[anchor, id=keyword fixpoint]][[/anchor]]

이번에는 함수 정의에 `Definition`이 아닌 `Fixpoint`라는 키워드를 사용했습니다. 이는 `is_even`이 재귀함수이기 때문입니다. `Definition` 키워드를 사용하면 `is_even`이 정의가 덜 된 상태에서 함수 body 안에서 `is_even`을 만나게 되고, Coq는 아직 정의되지 않은 이름을 만나서 당황하게 됩니다. 그래서 `Fixpoint`라는 특별한 키워드를 사용해서 Coq에게 이 함수가 재귀적이라고 미리 알려줍니다.

[[box]]

`Fixpoint`로 선언한 재귀함수는 반드시 무한재귀에 빠지지 않는다는 보장이 있어야합니다. 하지만 함수 선언만 보고 그 함수가 무한재귀에 빠질지 아닐지 판단하는 건 불가능합니다. 그건 [정지문제](https://en.wikipedia.org/wiki/Halting_problem)를 푸는 거랑 똑같거든요. 그래서 Coq는 좀 더 보수적인 접근법을 취합니다. 어떤 함수 `f(n)` 안에 `f(g(n))`이 들어있을 경우 `g(n)`이 `n`보다 작을 때만 `Fixpoint`의 정의가 가능합니다. 저 조건에서는 무한재귀에 빠지지 않는다는게 보장이 되거든요. 무한재귀에 빠지지 않지만 저 조건을 만족하지 않는 함수들은 `Fixpoint`로 정의가 불가능합니다.

[[/box]]

[[anchor, id=ex1]][[/anchor]]

```coq, line_num
Example test_even1: is_even 2 = true.
Proof.
  simpl.
  reflexivity.
  Qed.

Example test_even2: is_even 5 = false.
Proof.
  simpl.
  reflexivity.
  Qed.
```

방금 만든 함수들이 제대로 동작하는지 검사하는 코드입니다.[^unittest] 저기서 나오는 키워드들이 무슨 뜻인지는 [다음 장](Chap1-3.html)에 자세히 설명돼 있습니다.

[^unittest]: 이렇게만 놓고 보면 unit test와 비슷한 역할인 거 같은데 확실치 않습니다. 좀 더 공부해보고 다시 정리하겠습니다.

### plus

[[anchor, id=function nat plus]][[/anchor]]

이제 본격적으로 사칙연산을 구현해보겠습니다.

```coq, line_num
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
```

```coq, line_num
plus (S (S (S O))) (S (S (S O)))      (* plus 3 3 *)
= S (plus (S (S (S O))) (S (S O)))    (* S (plus 3 2) *)
= S (S (plus (S (S (S O))) (S O)))    (* S S (plus 3 1) *)
= S (S (S (plus (S (S (S O))) O)))    (* S S S (plus 3 0) *)
= S (S (S (S (S (S O)))))             (* S S S S S S *)
```

`plus` 함수가 어떻게 동작하는지 알기 쉽도록 나타내보았습니다. `m + n`을 하게되면 `n`을 감싸고 있는 `S`를 하나 꺼내서 `plus` 바깥쪽에 씌웁니다. 그럼 전체 `S`의 개수는 보존이 되고, 종국에는 `plus`가 사라지고 `S`와 `O`만 남게 됩니다.

### mult

```coq, line_num
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O                        (* 0 * m = 0 *)
  | S n' => plus m (mult n' m)    (* (n + 1) * m = m + (n * m) *)
  end.
```

인수 목록을 `(m : nat) (n : nat)`으로 쓰지 않고 `(m n : nat)`으로 쓴 걸 보실 수 있습니다. 모든 인수가 동일한 type을 가지면 위와 같이 축약해서 쓸 수 있습니다. [이전](Chap1-1.html#concepttuple)에 tuple에서 봤던 표기와 비슷하죠?

### minus

```coq, line_num
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O      (* 음수는 없습니다. *)
  | _ , O => m
  | S n', S m' => minus n' m'
  end.
```

책에서는 4번 라인을 `| S _ , O => n`라고 했던데 뭐가 다른지 모르겠네요.

### eqb

사칙연산이 그러했듯 등호도 내장함수가 아닌 Coq의 일반적인 문법으로 구현이 돼 있습니다. 그 형태가 아름다우니 보고 지나가겠습니다.

```coq, line_num
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
    | O => true
    | _ => false
    end
  | S n' => match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.
```

책에서는 5번 라인을 `| S m' => false`라고 했던데 뭐가 다른지 모르겠네요.

### leb

마지막으로 less or equal to의 구현을 살펴보겠습니다.

```coq, line_num
Fixpoint leb (m n : nat) : bool :=
  match m with
  | O => true
  | S m' => match n with
    | O => false
    | S n' => leb m' n'
    end
  end.
```

### `Notation`

[[anchor, id=keyword notation2]][[/anchor]]

```coq, line_num
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
```

`Notation` 키워드가 다시 등장했는데, 이번에는 새로운 syntax가 추가되었습니다. Haskell에서도 중위연산자를 정의하고 그 연산자의 우선순위를 지정해줄 수 있듯, Coq에서도 우선순위를 정할 수 있습니다. 위의 예제에서는 곱셈이 덧셈에 우선하고, 덧셈이 비교에 우선하도록 정의하였는데 이는 일상생활에서 쓰이는 연산자의 우선순위와 일치합니다.

[[anchor, id=operator eqb]][[/anchor]][[anchor, id=operator leb]][[/anchor]][[anchor, id=operator geb]][[/anchor]]

이제 저희는 2종류의 등호 연산자를 알게되었습니다. `=`와 `=?`인데, 둘은 성질이 조금 다릅니다. `=?`은 다른 프로그래밍 언어의 `==`와 비슷합니다. Expression, 즉 값입니다. `=`는 명제들 간에 쓰는 연산자로, 저희가 증명하려는 것들에 해당합니다.[^eq] `<=?`와 `>=?`도 비슷한 의미로 쓰입니다.

> coqIDE에서 `=?`를 사용하려고 하니 에러가 납니다. 따로 import를 해주어야 하는 걸까요? jscoq도 마찬가지입니다.

[^eq]: 책에서는 `x = y` *is a logical claim that we can try to prove*라고 언급했습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap1-1. Basic Syntax](Chap1-1.html)

[[/left]]

[[right]]

[Chap1-3. Proofs](Chap1-3.html) >>

[[/right]]