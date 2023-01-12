| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Existential Quantification

지금까지는 모든 (forall) x에 대해서만 살펴봤는데 이번에는 어떤 (exists) x에 대해서도 살펴보겠습니다. 어떤 x에 대한 명제를 증명하는 것은 쉽습니다. 그 명제가 참이 되도록 하는 x가 하나 이상 있음을 보이면 되니까요. 아래의 예시를 통해서 자세히 보겠습니다.

```coq, line_num
Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.
```

[[anchor, id = keyword exists]][[/anchor]]

4가 짝수임을 증명하는 아주 간단한 예시입니다. `Even`은 `nat` 하나를 받아서 `Prop` 하나를 내놓습니다. 즉, 자연수 하나를 받아서 그 자연수가 짝수인지 아닌지에 따라 참거짓이 바뀌는 명제를 내놓습니다. `four_is_even`이 증명하려는 것은 4가 짝수라는 사실입니다.

증명을 하다보면 goal이 `exists n, 4 = double n`이라는 형태가 됩니다. 거기서 `exists 2`라는 tactic을 쓰면 goal에 있는 `n`을 전부 2로 바꿉니다. 즉, `exists` tactic은 goal에 있는 '어떤 n'이라는 표현의 n에 실제 값을 대입합니다. `n`에 2를 대입하고 나면 증명이 간단하게 끝납니다.

다른 예시도 보겠습니다.

```coq, line_num
Theorem exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  destruct H as [m Hm].
  exists (2 + m).
  apply Hm.
  Qed.
```

위의 예시도 간단합니다. context의 `H`에 `exists m`이 있는데 `destruct H`를 통해서 `exists m`을 없앱니다. 그리고 `exists (2 + m)`을 통해서 `o`에 `(2 + m)`을 넣으면 증명이 끝납니다.

## 연습

이대로 마무리하긴 아쉬워서 간단한 증명을 하나 더 해보았습니다. Coq를 직접 실행시키면서 따라 해보면 이해하는데 도움이 될 것 같습니다.

```coq, line_num
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - (* (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) *)
    intros H.
    destruct H as [x_ Hpxqx].
    destruct Hpxqx as [Hpx | Hqx].
    * (* P H *)
      left.
      exists x_.
      apply Hpx.
    * (* Q H *)
      right.
      exists x_.
      apply Hqx.
  - (* (exists x, P x \/ Q x) <- (exists x, P x) \/ (exists x, Q x) *)
    intros H.
    destruct H as [H2px | H2qx].
    * (* exists x, P x *)
      destruct H2px as [x_ H2px].
      exists x_.
      left.
      apply H2px.
    * (* exists x, Q x *)
      destruct H2qx as [x_ H2qx].
      exists x_.
      right.
      apply H2qx.
  Qed.
```

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-2. True and False Propositions](Chap6-2.html)

[[/left]]

[[right]]

[Chap6-4. Programming with Propositions](Chap6-4.html) >>

[[/right]]