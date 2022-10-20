| Table of Contents |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Existential Quantification

지금까지는 모든 (forall) x에 대해서만 살펴봤는데 이번에는 어떤 (exists) x에 대해서도 살펴보겠습니다. 어떤 x에 대한 명제를 증명하는 것은 쉽습니다. 그 명제가 참이 되도록 하는 x가 하나 이상 있음을 보이면 되니까요. 아래의 예시를 통해서 자세히 보겠습니다.

```haskell, line_num
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

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap6-2. True and False Propositions](Chap6-2.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]