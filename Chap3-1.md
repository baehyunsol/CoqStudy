| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Pairs

3장에서는 자료구조를 다룹니다. 여기서는 그 중 첫번째로 Pair를 다루겠습니다.

```haskell, line_num
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
```

pair는 2원소짜리 tuple입니다. Pairs도 `Notation`을 사용하면 편리하게 사용할 수 있습니다. 아래의 예시를 보겠습니다.

[[anchor, id=keyword notation]][[/anchor]]

```haskell
Notation "( x , y )" := (pair x y).
```

방금 정의한 notation 덕분에 더 편리하게 pairs method를 정의할 수 있습니다. 아래의 예시를 보겠습니다.

```haskell, line_num
Definition fst (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | (x, y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.
```

[[box]]

방금 정의한 pair 문법과 [이전](Chap1-2.html#minus)에 봤던 multiple pattern matching을 헷갈릴 수 있습니다. 잠깐 보고 가겠습니다.

```haskell, line_num
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O
  | _ , O => m
  | S n', S m' => minus n' m'
  end.
```

위와 같이 패턴 2개를 `,`로 붙일 수 있습니다. 이 경우 `match` 옆에도 값이 2개가 옵니다.

```haskell, line_num
Fixpoint minus (n m : nat) : nat :=
  match (n, m) with
  | (O , _) => O
  | (_ , O) => m
  | (S n', S m') => minus n' m'
  end.
```

위의 코드도 유효합니다. pair 안쪽도 pattern matching이 되는게 신기하네요.

```haskell, line_num
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | (O , _) => O
  | (_ , O) => m
  | (S n', S m') => minus n' m'
  end.
```

위의 코드는 유효하지 않습니다. pattern matching을 2개를 한다고 선언했지만 각 가지에는 패턴이 하나씩밖에 없거든요. `(O, _)`는 하나의 패턴입니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap2-3. Binary](Chap2-3.html)

[[/left]]

[[right]]

[Chap3-2. Lists](Chap3-2.html) >>

[[/right]]