| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Partial Maps

이젠 `partial_map`을 구현해보겠습니다. `total_map`은 없는 키를 주면 기본 값을 반환했지만 `partial_map`은 `None`을 반환합니다.

```haskell, line_num
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).
```

구현은 아주 간단합니다. `total_map`에 기본값을 `None`으로 주면 되거든요.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap8-1. Total Maps](Chap8-1.html)

[[/left]]

[[right]]

[Chap9-1. Curry Howard Correspondence](Chap9-1.html) >>

[[/right]]