| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Coq Automation

이번 장에서는 Coq의 증명 노가다를 도와줄 tactic들을 소개합니다. 이번에 소개할 tactic들은 tactic에 쓰는 tactic입니다. 책의 표현을 빌리자면 higher-order tactic이죠.

## try

[[anchor, id = keyword try]][[/anchor]]

원래 Coq에서 tactic이 실패를 하면 (ex. 똑같지 않은데 `reflexivity`를 쓰면) 증명 전체가 실패합니다. 하지만 `try` 뒤에 있는 tactic은 실패를 하더라도 아무 영향이 없습니다. 즉,

- `try` 뒤의 tactic이 성공하면
  - 그 tactic이 context에 반영됩니다.
- `try`뒤의 tactic이 실패하면
  - 그 tactic을 통째로 무시하고 다음으로 넘어갑니다.

얼핏 보면 저런게 왜 필요한가 싶습니다. 실패하는 tactic은 애초에 안 쓸텐데 말이죠... 손으로 증명을 할 때는 그렇습니다. 하지만 증명 자체를 자동화하는 경우에는 다릅니다. 증명을 위한 스크립트를 쓰면 실패하는 tactic이 섞여 있을 수도 있습니다. 이따가 예시와 함께 설명하겠습니다.

## ; tactical

[[anchor, id = keyword semi colon]][[/anchor]]

`destruct`나 `induction` 등등을 사용하면 여러 subgoal이 생깁니다. subgoal의 개수가 많은데 각 subgoal에 동일한 tactic을 적용하고 싶으면 어떻게 할까요? 아래의 예시를 보겠습니다.

```haskell, line_num
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    - (*{- n = 0 -}*)
      simpl.
      reflexivity.
    - (*{- n = S n' -}*)
      simpl.
      reflexivity.
Qed.
```

`simpl`과 `reflexivity`가 2번씩 반복되는게 거슬리죠? `;`를 이용해서 간략하게 해보겠습니다. 아래를 봅시다.

```haskell, line_num
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n;
  simpl;
  reflexivity.
  Qed.
```

`destruct` 뒤에 `;`가 붙어있기 때문에 그 뒤에 오는 `simpl`이 두 subgoal에 각각 적용되고, `simpl` 뒤에 `;`가 있기 때문에 `reflexivity`도 2번 적용됩니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 12-1. Arithmetic and Boolean Expressions](Chap12-1.html)

[[/left]]

[[right]]

[Chapter 12-3. States and Commands](Chap12-3.html) >>

[[/right]]