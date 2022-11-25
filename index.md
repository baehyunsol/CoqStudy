모든 문서는 PC 환경에 최적화 되어 있습니다! 모바일로는 읽기 불편해요... 또한, 이 블로그는 firefox에 가장 최적화돼 있습니다. 브라우저 관련된 내용을 자세히 보려면 [이 문서](https://baehyunsol.github.io/Browser-Compatibility)를 참고해주세요. 오타 혹은 지적사항은 [여기](https://github.com/baehyunsol/CoqStudy/issues)에 이슈를 남겨주세요!

[[right]]

작성자: 배현솔\
최초 작성일: 2022.09.02\
최근 업데이트: 2022.11.15

[[/right]]

# Coq Tutorial

Coq 언어 자습 문서입니다. 원래는 영어로 쓰려고 했는데 한글로된 Coq 문서가 하나도 없는 것 같아 블루오션인 것 같아서 한글로 작성하였습니다.

- Coq를 처음 공부하면서 작성한 문서이기 때문에 틀린 부분이 있을 확률이 매우 높습니다.
- 문서 중간중간에 Rust나 Haskell을 아주 자주 언급합니다. Rust나 Haskell을 몰라도 별 지장이 없기는 하지만 알면 더욱 좋습니다.
- 문서의 모든 내용은 [Software Foundations](https://softwarefoundations.cis.upenn.edu/)의 내용에 기반합니다.
  - 다만, 순수 번역본은 아닙니다. 제가 자습한 내용을 한글로 정리한 정리본에 가깝습니다. 원본과 순서가 다른 내용도 있고, 생략/추가된 내용도 조금씩 있습니다.
  - 이 블로그의 99% 정도의 내용은 Software Foundations에 기반하지만 [Coq 공식 문서](https://coq.inria.fr/refman/index.html)와 [다른 책](http://adam.chlipala.net/cpdt/)에서 참고한 내용도 간혹 있습니다.
- Coq를 웹 상에서 실행시켜보고 싶으면 [jscoq](https://coq.vercel.app/scratchpad.html)를 방문하시면 됩니다.
- 이 책을 쓰는 현재 제가 사용중인 Coq는 CoqIDE, version 8.15.2입니다.

## Index By Chapter

- Chapter 1. Functional Programming
  - [Chapter 1-1: Basic Syntax](Chap1-1.html)
  - [Chapter 1-2: Natural Numbers](Chap1-2.html)
  - [Chapter 1-3: Proofs](Chap1-3.html)
- Chapter 2. Proofs by Induction
  - [Chapter 2-1: Proofs by Induction](Chap2-1.html)
  - [Chapter 2-2: Proofs within proofs](Chap2-2.html)
  - [Chapter 2-3: Binary](Chap2-3.html)
- Chpater 3. Data structures
  - [Chapter 3-1: Pairs](Chap3-1.html)
  - [Chapter 3-2: Lists](Chap3-2.html)
  - [Chapter 3-3: Options](Chap3-3.html)
  - [Chapter 3-4: Maps](Chap3-4.html)
- Chapter 4. More Functional Programming 
  - [Chapter 4-1. Polymorphism](Chap4-1.html)
  - [Chapter 4-2. Higher Order Functions](Chap4-2.html)
- Chapter 5. More Tactics
  - [Chapter 5-1. Apply](Chap5-1.html)
  - [Chapter 5-2. Injective and Disjoint](Chap5-2.html)
  - [Chapter 5-3. More tactics](Chap5-3.html)
- Chapter 6. Logic
  - [Chapter 6-1. Conjunction and Disjunction](Chap6-1.html)
  - [Chapter 6-2. True and False Propositions](Chap6-2.html)
  - [Chapter 6-3. Existential Quantification](Chap6-3.html)
  - [Chapter 6-4. Programming with Propositions](Chap6-4.html)
  - [Chapter 6-5. Axioms](Chap6-5.html)
- Chapter 7. Inductively defined Propositions
  - [Chapter 7-1. Inductively defined Propositions](Chap7-1.html)
  - [Chapter 7-2. Using Evidence in Proofs](Chap7-2.html)
- [Appendix](Appendix.html)

## Index by keyword

[A](#indexa) [C](#indexc) [D](#indexd) [E](#indexe) [F](#indexf) [G](#indexg) [I](#indexi) [L](#indexl) [M](#indexm) [N](#indexn) [R](#indexr) [S](#indexs) [T](#indext) [U](#indexu)

- A[[anchor, id = index a]][[/anchor]]
  - apply: [chap5-1](Chap5-1.html#keywordapply)
  - apply with: [chap5-1](Chap5-1.html#keywordapplywith), [chap6-4](Chap6-4.html#keywordapplywith)
  - arguments: [chap4-1](Chap4-1.html#keywordarguments)
  - assert: [chap2-2](Chap2-2.html#keywordassert)
  - @: [char4-1](Chap4-1.html#keywordat)
  - axiom: [char6-5](Chap6-5.html#keywordaxiom)
- C[[anchor, id = index c]][[/anchor]]
  - check: [chap1-1](Chap1-1.html#keywordcheck)
  - compute: [chap1-1](Chap1-1.html#keywordcompute)
- D[[anchor, id = index d]][[/anchor]]
  - definition: [chap1-1](Chap1-1.html#keyworddefinition)
  - destruct: [chap1-3](Chap1-3.html#keyworddestruct), [chap5-3](Chap5-3.html#keyworddestruct), [chap6-1](Chap6-1.html#keyworddestruct)
  - discriminate: [chap5-2](Chap5-2.html#keyworddiscriminate)
- E[[anchor, id = index e]][[/anchor]]
  - else: [chap1-1](Chap1-1.html#keywordif)
  - = (eq): [chap6-1](Chap6-1.html#notationeq)
  - =? (eqb): [chap1-2](Chap1-2.html#operatoreqb)
  - example: [chap1-3](Chap1-3.html#keywordexample), [chap2-3](Chap2-3.html#keywordexample)
  - exfalso: [chap6-2](Chap6-2.html#keywordexfalso)
  - exists: [chap6-3](Chap6-3.html#keywordexists)
- F[[anchor, id = index f]][[/anchor]]
  - f_equal: [chap5-2](Chap5-2.html#keywordfequal)
  - fixpoint: [chap1-2](Chap1-2.html#keywordfixpoint)
  - fun: [chap4-2](Chap4-2.html#keywordfun)
- G[[anchor, id = index g]][[/anchor]]
  - >=?: [chap1-2](Chap1-2.html#operatorgeb)
  - generalize: [chap5-3](Chap5-3.html#keywordgeneralize)
- I[[anchor, id = index i]][[/anchor]]
  - if: [chap1-1](Chap1-1.html#keywordif)
  - ->: [chap6-1](Chap6-1.html#notationimplies)
  - in: [chap5-3](Chap5-3.html#keywordin)
  - induction: [chap2-1](Chap2-1.html#keywordinduction)
  - inductive: [chap1-1](Chap1-1.html#keywordinductive), [chap7-1](Chap7-1.html#keywordinductive)
  - injection: [chap5-2](Chap5-2.html#keywordinjection)
  - intro: [chap1-3](Chap1-3.html#keywordintro)
  - intros: [chap1-3](Chap1-3.html#keywordintros)
  - inversion: [chap7-2](Chap7-2.html#keywordinversion)
- L[[anchor, id = index l]][[/anchor]]
  - <=?: [chap1-2](Chap1-2.html#operatorleb)
  - left: [chap6-1](Chap6-1.html#keywordleft)
- M[[anchor, id = index m]][[/anchor]]
  - match: [chap1-1](Chap1-1.html#keyworddefinition)
  - module: [chap1-1](Chap1-1.html#keywordmodule)
- N[[anchor, id = index n]][[/anchor]]
  - notation: [chap1-1](Chap1-1.html#keywordnotation), [chap1-2](Chap1-2.html#keywordnotation2), [chap3-1](Chap3-1.html#keywordnotation2)
  - <> (noteq): [chap6-2](Chap6-2.html#operatornoteq)
- R[[anchor, id = index r]][[/anchor]]
  - reflexivity: [chap1-3](Chap1-3.html#keywordreflexivity)
  - rewrite: [chap1-3](Chap1-3.html#keywordrewrite), [chap6-4](Chap6-4.html#keywordrewrite)
  - right: [chap6-1](Chap6-1.html#keywordright)
- S[[anchor, id = index s]][[/anchor]]
  - search: [chap3-3](Chap3-3.html#keywordsearch)
  - simpl: [chap1-3](Chap1-3.html#keywordsimpl)
  - split: [chap6-1](Chap6-1.html#keywordsplit)
  - symmetry: [chap5-1](Chap5-1.html#keywordsymmetry)
- T[[anchor, id = index t]][[/anchor]]
  - then: [chap1-1](Chap1-1.html#keywordif)
  - theorem: [chap1-3](Chap1-3.html#keywordtheorem)
  - transitivity: [chap5-1](Chap5-1.html#keywordtransitivity)
  - tuple: [chap1-1](Chap1-1.html#concepttuple)
- U[[anchor, id = index u]][[/anchor]]
  - unfold: [chap5-3](Chap5-3.html#keywordunfold)