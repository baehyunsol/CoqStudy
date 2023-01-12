| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Maps

Rust의 `HashMap`, Python의 `dict`에 대응되는 자료구조입니다. 키와 값을 모두 `nat`을 사용하지만 key는 특별히 `id`라는 wrapper type을 사용하겠습니다. Wrapper type을 사용함으로써 가독성도 좋아지고 나중의 refactoring에도 유리해집니다.

```coq, line_num
Definition id : Type :=
  | Id (n : nat).
```

Partial map의 정의는 아래와 같습니다. 단순하군요.

```coq, line_num
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
```

[이전](Chap3-2.html)에 봤던 list의 정의와 동일한 형태입니다. 기존의 record에 (키, 값) 쌍을 하나씩 cons하는 형태입니다. 기본적인 함수의 구현도 아주 간단합니다. 아래에서 자세히 보겠습니다.

## update

```coq, line_num
Definition update (m : partial_map) (i : id) (v : nat) : partial_map :=
  record i v m.
```

정말 간단합니다. cons와 동일한 형태이군요.

## find

```coq, line_num
Fixpoint find (i : id) (m : partial_map) : natoption :=
  match m with
  | empty => None
  | record i' v m' => if eqb_id i i'
    then Some v
    else find i m'
  end.
```

find의 정의도 간단합니다. 참고로 `eqb_id`는 `id` 값 2개가 동일한 값을 갖는지 비교하는 함수입니다. 간단하니 설명은 생략하겠습니다.

> 다른 언어들과 달리 시간복잡도, 공간복잡도를 고려하지 않는다는게 신기하네요. 애초에 언어의 목적이 실행/계산이 아닌 증명이어서 그런 것 같습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap3-3. Options](Chap3-3.html)

[[/left]]

[[right]]

[Chap4-1. Polymorphism](Chap4-1.html) >>

[[/right]]