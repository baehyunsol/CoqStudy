| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Binary

지금까지 배운 내용들을 종합하여 이진법을 구현해보는 챕터입니다.

## 정의

```coq, line_num
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
```

이진법을 위와 같이 정의했습니다. 각 자릿수는 0 혹은 1의 값을 가지며, 다음 자리수와 연결돼 있습니다. 마지막에는 이진법 표기가 끝났다는 뜻의 `Z`를 붙입니다. 아래 표를 보면 예제의 이진법 구현을 더 쉽게 이해할 수 있습니다.

| decimal | binary                | unary                  |
|---------|-----------------------|------------------------|
| 0       | Z                     | O                      |
| 1       | B~1~ Z                | S O                    |
| 2       | B~0~ (B~1~ Z)         | S (S O)                |
| 3       | B~1~ (B~1~ Z)         | S (S (S O))            |
| 4       | B~0~ (B~0~ (B~1~ Z))  | S (S (S (S O)))        |
| 5       | B~1~ (B~0~ (B~1~ Z))  | S (S (S (S (S O))))    |

보통의 이진법표기는 MSB[^sb]가 가장 왼쪽으로 오지만, 여기서는 LSB[^sb]가 가장 왼쪽으로 옵니다. 이는 구현의 편리함을 위함입니다.

[^sb]: 가장 큰 자릿수를 MSB라고 하고, 가장 작은 자릿수를 LSB라고 합니다. 6을 이진법으로 썼을 때 1010이 된다면, MSB는 1이고 LSB는 0입니다.

## incr

`incr`는 이진법을 다루는 가장 간단한 함수로, 주어진 수에 1을 더해서 반환합니다.

```coq, line_num
Fixpoint incr (b: bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 b' => B1 b'
  | B1 b' => B0 (incr b')
  end.
```

구현은 위와 같이 아주 간단합니다. 0에다가 1을 더하면 1이고, LSB가 0일 경우 LSB를 1로 바꿔주며, LSB가 1일 경우 0으로 바꾸고 받아올림[^carry]을 합니다.

[^carry]: Carry가 한국말로 받아올림이 맞나요?

[[anchor, id=keywordexample]][[/anchor]]

```coq, line_num
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  reflexivity.
  Qed.

 Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  reflexivity.
  Qed.

 Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  reflexivity.
  Qed.
```

위와 같은 코드로 간단히 unit test를 할 수 있습니다. 물론 unit test가 코드를 *검증*하는 수단은 아니라는 것을 유념하시기 바랍니다. Coq를 이용한 formal한 검증은 [아래](#검증1)에서 확인할 수 있습니다.

## bin_to_nat

말그대로 `bin` type의 instance를 `nat` type으로 바꿔주는 함수입니다.

```coq, line_num
Fixpoint bin_to_nat (b: bin) : nat :=
  match b with
  | Z => O
  | B0 b' => 2 * (bin_to_nat b')
  | B1 b' => 1 + 2 * (bin_to_nat b')
  end.
```

이진법의 정의를 그대로 코드로 옮겨놨습니다.

## 검증1

```coq, line_num
(*
                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S
*)

Theorem bin_to_nat_incr : forall b: bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
```

위의 theorem을 증명해봅시다. 물론 저 theorem이 맞다고 해서 `incr`과 `bin_to_nat`에 문제가 없다고 완벽히 장담할 순 없지만, [이전](#keywordexample)의 unit test보다는 훨씬 설득력이 있습니다.

```coq, line_num
Theorem bin_to_nat_incr : forall b: bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [ | b0' IHb0'| b1' IHb1'].
  - (* b = Z *)
    reflexivity.
  - (* b = B0 b0' *)
    reflexivity.
  - (* b = B1 b1' *)
    simpl.
    rewrite add_0_r.
    rewrite add_0_r.
    rewrite IHb1'.
    simpl.
    assert (H: forall n m : nat, n + S m = S (n + m)).
    {
      intros m n.
      induction m as [ | m' IHm'].
      - (* m = 0 *)
        reflexivity.
      - (* m = S m' *)
        simpl.
        rewrite <- IHm'.
        reflexivity.
    }
    rewrite H.
    reflexivity.
  Qed.
```

의식의 흐름대로 증명한지라 증명이 좀 더럽습니다.

## nat_to_bin

이번에는 반대로 `nat`을 `bin`으로 바꾸는 함수를 구현해보겠습니다.

```coq, line_num
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.
```

역시 아주 간단하게 구현했습니다. `S`를 하나 벗길 때마다 `incr`를 한번씩 하도록 구현했습니다.

## 검증2

방금 만든 `nat_to_bin`을 검증해봅시다. 어떤 자연수를 `nat_to_bin`과 `bin_to_nat`을 한번씩 거치면 원래의 수로 돌아오는지 확인해보겠습니다.

```coq, line_num
Theorem nat_bin_nat : forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite bin_to_nat_incr.
    simpl.
    rewrite IHn'.
    reflexivity.
  Qed.
```

[위](검증1)에서 증명했던 `bin_to_nat_incr`을 사용했습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap2-2. Proofs within proofs](Chap2-2.html)

[[/left]]

[[right]]

[Chap3-1. Pairs](Chap3-1.html) >>

[[/right]]