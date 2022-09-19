[[giant]][[red]]모든 문서는 PC 환경에 최적화 되어 있습니다! 모바일로는 읽기 불편해요...[[/red]][[/giant]]

[[right]]

작성자: 배현솔\
최근 업데이트: 2022.09.19

[[/right]]

# Coq Tutorial

Coq 언어 자습 문서입니다. 원래는 영어로 쓰려고 했는데 한글로된 Coq 문서가 하나도 없는 것 같아 블루오션인 것 같아서 한글로 작성하였습니다.

- Coq를 처음 공부하면서 작성한 문서이기 때문에 틀린 부분이 있을 확률이 매우 높습니다.
- 문서 중간중간에 Rust나 Haskell을 아주 자주 언급합니다. Rust나 Haskell을 몰라도 별 지장이 없기는 하지만 알면 더욱 좋습니다.
- 문서의 모든 내용은 [Software Foundations](https://softwarefoundations.cis.upenn.edu/)의 내용에 기반합니다.
  - 다만, 순수 번역본은 아닙니다. 제가 자습한 내용을 한글로 정리한 정리본에 가깝습니다. 원본과 순서가 다른 내용도 있고, 생략/추가된 내용도 조금씩 있습니다.
  - [Coq 공식 문서](https://coq.inria.fr/refman/index.html)와 [다른 책](http://adam.chlipala.net/cpdt/)에서 참고한 내용도 간혹 있습니다.
- Coq를 웹 상에서 실행시켜보고 싶으면 [jscoq](https://coq.vercel.app/scratchpad.html)를 방문하시면 됩니다.

## Index By Chapter

- [Chapter 1-1: Basic Syntax](Chap1-1.html)
- [Chapter 1-2: Natural Numbers](Chap1-2.html)
- [Chapter 1-3: Proofs](Chap1-3.html)
- [Chapter 2-1: Proofs by Induction](Chap2-1.html)
- [Chapter 2-2: Proofs within proofs](Chap2-2.html)
- [Chapter 2-3: Binary](Chap2-3.html)

## Index by keyword

- assert : [chap2-2](Chap2-2.html#keywordassert)
- check : [chap1-1](Chap1-1.html#keywordcheck)
- compute : [chap1-1](Chap1-1.html#keywordcompute)
- definition : [chap1-1](Chap1-1.html#keyworddefinition)
- destruct : [chap1-3](Chap1-3.html#keyworddestruct)
- else : [chap1-1](Chap1-1.html#keywordif)
- =? : [chap1-2](Chap1-2.html#operatoreqb)
- example : [chap1-3](Chap1-3.html#keywordexample), [chap2-3](Chap2-3.html#keywordexample)
- fixpoint: [chap1-2](Chap1-2.html#keywordfixpoint)
- >=? : [chap1-2](Chap1-2.html#operatorgeb)
- if : [chap1-1](Chap1-1.html#keywordif)
- induction : [chap2-1](Chap2-1.html#keywordinduction)
- inductive : [chap1-1](Chap1-1.html#keywordinductive)
- intro : [chap1-3](Chap1-3.html#keywordintro)
- intros : [chap1-3](Chap1-3.html#keywordintros)
- <=? : [chap1-2](Chap1-2.html#operatorleb)
- match : [chap1-1](Chap1-1.html#keyworddefinition)
- module : [chap1-1](Chap1-1.html#keywordmodule)
- notation : [chap1-1](Chap1-1.html#keywordnotation), [chap1-2](Chap1-2.html#keywordnotation2)
- reflexivity : [chap1-3](Chap1-3.html#keywordreflexivity)
- rewrite : [chap1-3](Chap1-3.html#keywordrewrite)
- simpl : [chap1-3](Chap1-3.html#keywordsimpl)
- then : [chap1-1](Chap1-1.html#keywordif)
- theorem : [chap1-3](Chap1-3.html#keywordtheorem)
- tuple : [chap1-1](Chap1-1.html#concepttuple)
