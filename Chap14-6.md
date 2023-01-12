| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Small-Step Operational Semantics

지금까지 봤던 모든 프로그램 검증은 big-step으로 진행됐습니다. 프로그램을 통째로 던져주고, 시작과 끝 조건만 알려주면 Coq이 한번에 검증을 해주었습니다. 간단한 프로그램에선 아주 좋은 방법이지만, 세상은 그렇게 간단하지 않습니다. 예를 들어서, 명령어 10개로 이뤄진 병렬 프로그램을 생각해봅시다. 만약 이 프로그램이 병렬로 돌아가지 않는다면 명령어 10개가 동시에 실행된다고 생각해도 문제가 없습니다. 중간에 누가 끼어들지 않을테니까요. (끼어들더라도 이 프로그램에 영향을 주지 않을테니까요) 하지만 병렬로, 서로 협력하면서 돌아간다면요? 첫번째 프로그램의 명령어가 3개 실행됐을 때, 두번째 프로그램의 7번째 명령어가 실행되면요? 이런 상황에서도 검증이 유효하려면 big-step말고 다른 전략을 취해야합니다. 그래서 이번 장에서는 small-step을 소개합니다.

TODO: typechecker도 big-step/small-step과 관련된 문제라는데 왜 그런지 모르겠습니다...

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 14-5. Hoare Logic as a Logic](Chap14-5.html)

[[/left]]

[[right]]

[Chapter 15-1. TODO](Chap15-1.html) >>

[[/right]]