Assertions

`state` 받아서 `Prop` 내놓음

- fun st => True: 항상 참인 Assertion
- fun st => st X = 3: `st`의 `X`라는 변수의 값이 3이라는 Assertion

보통은 축약해서 `X = 3`만 씀

---

`P ->> Q`: `P`와 `Q`는 Assertion임. Assertion끼리의 implication

---

Hoare Triple

`{P} c {Q}`: `P`라는 assertion을 만족하는 state에 `c`라는 명령어를 실행하면, 그 결과로 나온 state는 `Q`라는 assertion을 만족

`P`를 precondition, `Q`를 postcondition이라고 부름

`{X = 0} X := X + 1 {X = 1}`은 valid한 Hoare Triple

`forall m, {X = m} X := X + 1 {X = m + 1}`은 valid한 Hoare Triple. 여기서 `forall m`은 precondition에 걸리는게 아니고 Hoare Triple 전체에 걸림!

일단 part1의 summary 다 이해할 수 있게 ㄱㄱ