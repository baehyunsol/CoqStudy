| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Lists

두번째 자료구조로 List에 대해서 알아보겠습니다. List의 구현은 Haskell 혹은 다른 순수함수형 언어의 list와 아주 비슷합니다. 아래의 정의를 보겠습니다.

```coq, line_num
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

`natlist`라는 자연수의 list를 정의하였습니다. Generic하게 정의할 수도 있습니다. 그 방법은 [나중](Chap4-1.html)에 알아보겠습니다.

```coq, line_num
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
```

Notation도 몇가지 정의했습니다. `::`는 Haskell에서 보던 `:`과 동일하며, list literal은 `[x;..;y]`[^ll]로 정의했습니다.

[^ll]: 이렇게 정의해도 `[1; 2; 3; 4]`같은 문법을 알아듣는다는게 신기하네요.

## Implementation

간단한 함수 몇가지를 정의해보겠습니다.

### Repeat

[[anchor, id = definition repeat]][[/anchor]]

```coq, line_num
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
```

자연수 `n`가 `count`번만큼 반복되는 `natlist`를 반환하는 함수입니다.

### Length

```coq, line_num
Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
```

주어진 list의 길이를 반환합니다.

### Get

```coq, line_num
Fixpoint get (l: natlist) (idx: nat) : nat :=
  match idx with
  | O => match l with
    | nil => O
    | h :: t => h
    end
  | S n' => match l with
    | nil => O
    | h :: t => get t n'
    end
  end.
```

주어진 list의 `n`번째 원소를 찾는 함수입니다. 책에는 없고 제가 짜본 함수입니다. Index error를 나타낼 방법이 없어서 index error가 나면 `O`를 반환하도록 했습니다. Index error와 관련된 부분은 [다음 장](Chap3-3.html)에서 다루겠습니다.

### Append

```coq, line_num
Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (append t l2)
  end.

Notation "x ++ y" := (append x y)
                     (right associativity, at level 60).
```

두 list를 합치는 함수입니다. 연산자도 정의했습니다.

### Reverse

```coq, line_num
Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
```

list를 뒤집는 함수입니다.

### head and tail

```coq, line_num
Definition head (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tail (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
```

head와 tail도 만들었습니다. 특이한 점은, `nil`의 head를 구할 경우를 대비하기 위해 `default`란 인수가 있습니다.

### nonzeros

```coq, line_num
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
    | O => nonzeros t
    | h' => h' :: nonzeros t
    end
  end.
```

list를 받아서 0이 아닌 값들만 남기는 함수입니다. 빨리 filter함수를 배워서 쓰고 싶네요.

### count_odd_numbers

```coq, line_num
Fixpoint count_odd_members (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => if is_odd h
    then S (count_odd_members t)
    else count_odd_members t
  end.
```

책에서는 `Fixpoint`가 아닌 `Definition`을 이용해서 정의하도록 시켰습니다. `odd_members`[^odmb]라는 함수를 만들고 [위](#length)에서 정의한 `length`와 묶어서 쓰라는 의도인 거 같은데, 저는 이 방법이 좀 더 마음에 드네요.

[^odmb]: 주어진 list에서 홀수들만 남기는 함수입니다. Python으로 쓰면 `[n for n in l if n % 2 == 1]` 정도가 되겠군요.

### alternate

```coq, line_num
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | h :: t, _ => h :: (alternate l2 t)
  | nil, h :: t => h :: (alternate t l1)
  | nil, nil => nil
  end.
```

## Reasonings

list를 이용해서 theorem들을 만들고 증명해보겠습니다.

```coq, line_num
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
```

먼저, 수학적 귀납법을 이용해서 `append`의 결합법칙을 증명해보겠습니다.

```coq, line_num
Proof.
  intros l1 l2 l3.
  induction l1 as [ | n l1' IHl1'].
  - (* l1 = [] *)
    reflexivity.
  - (* l1 = n :: l1' *)
    simpl.
    rewrite IHl1'.
    reflexivity.
  Qed.
```

자연수에 귀납법을 쓰던 것과 매우 비슷합니다. `l1`이 `nil`인 경우와 `n :: l1'`인 경우로 나눕니다.

`nil`인 경우, `nil ++ l2`는 아주 간단한 형태로 정리가 되므로 `reflexivity` 한 번으로 증명이 끝납니다.

`l1 = n :: l1'`인 경우, 방금 `IHl1': (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3`를 증명했으므로 저 형태로 만들기만 하면 증명이 끝납니다.

쉽죠?

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap3-1. Pairs](Chap3-1.html)

[[/left]]

[[right]]

[Chap3-3. Options](Chap3-3.html) >>

[[/right]]