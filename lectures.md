| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# 허충길 교수님 강의

허충길 교수님의 2020학년도 서울대학교 컴퓨터 신기술 특강 강의의 내용을 정리한 단원입니다. 강의는 전체적으로 software foundations 책을 기반으로 하지만 책에 없는 내용들도 포함돼 있고 그 내용들을 여기에 정리해보았습니다. 강의를 전부 다 들은 건 아니어서 빠진 내용이 있을 수도 있습니다.

이 부분을 읽기 전에 9단원까지 먼저 읽고 오시는 것을 추천드립니다.

## 집합

Coq에서 모든 것은 집합 혹은 집합의 원소입니다. 예를 들어서, `nat`은 집합이고 `3`은 `nat`의 원소입니다. 그래서 [9단원](Chap9-1.html)에서 `3 : nat`을 ~_`3`은 `nat`의 원소이다_~라고 읽는다고 설명했었죠. 마찬가지로 `nat : Type`이니까 `nat`은 `Type`이라는 집합의 원소입니다.

이 원칙에 어긋나는 것이 딱 한가지가 있습니다. 바로 `Type`입니다. Coq의 모든 집합은 `Type`을 이용해서 정의되지만 `Type`만은 Coq에 내장(predefined)돼 있습니다. 왜냐면 모든 집합은 `Type`의 원소거든요. 또한, `Type`은 유일하게 원소이면서 동시에 집합입니다. 그래서 `Type : Type`입니다.

단, `Type`이 자기자신을 포함하는 집합이라는 뜻은 아닙니다. Coq이 `Type : Type`이라고 하더라도 앞의 `Type`과 뒤의 `Type`은 다릅니다. 각 `Type`들은 내부적으로 서열이 있고, 큰 `Type`이 작은 `Type`을 포함합니다. 즉, Coq의 내부에서는 `Type_u : Type_v`과 같이 꼬리표를 붙인 후 `u`가 `v`보다 작거나 같다고 어딘가에 기록을 해둡니다. Coq에서 쓰이는 모든 `Type`들은 크기에 대한 꼬리표가 붙어있고 꼬리표의 대소관계가 어긋나는 순간, Coq은 에러를 내뿜습니다.

> 자기자신을 포함하는 집합에 대해서 더 궁금하시면 [러셀의 역설](https://plato.stanford.edu/entries/russell-paradox/)을 읽어보시면 좋습니다.

그럼 `Set`이나 `Prop`은 뭐냐고 궁금해하실 수도 있습니다. `Set`은 사실상 `Type`과 동일합니다. 다만 오래된 코드와의 하위호환을 유지하기 위해서 `Set`도 가끔 쓴다고 하네요. `Prop`은 증명의 집합입니다. 즉, 그 집합에 원소가 하나라도 있으면 `Prop`은 참인 명제가 됩니다. 아래의 예시와 함께 설명해보겠습니다.

```coq, line_num
Definition X : Prop := 1 = 1 \/ 2 = 2.

Check X : Prop.
Check Prop : Type.
Check X : Type.
Check or_introl eq_refl : X.
Check or_intror eq_refl : X.
```

먼저, `X : Prop`인 것은 당연합니다. 그렇게 정의했거든요. `Prop`은 집합이고 `Type`은 모든 집합을 포함하는 집합이니 `Prop : Type`인 것도 당연합니다. 5번줄부터 약간 헷갈립니다. `X`는 `1 = 1 \/ 2 = 2`가 참인 증명들의 집합이죠? `X`가 집합이니까 `X : Type`도 참입니다. 그럼 `X`의 원소로는 무엇이 있을까요? 직관적으로 2가지가 떠오릅니다. `\/`을 왼쪽을 증명할 수도 있고 오른쪽을 증명할 수도 있죠? 각각의 증명은 `X`의 원소입니다. 그 얘기가 6번과 7번 줄에 있습니다.

그럼 `Prop`과 `Type`의 차이가 뭘까요? 위의 예시의 `Prop`들을 전부 `Type`이라고 고쳐도 전혀 문제가 없습니다. 실제로 `Prop`과 `Type`은 99% 정도가 동일하지만 차이점이 하나 있습니다. 바로 `Prop`의 원소는 최대 1개라는 겁니다. 엥? 6번줄과 7번줄에 원소가 2개 있는데 무슨 소리냐고요? Coq에선 둘을 동일하게 취급합니다. 즉, 동일한 `Prop`의 원소들은 전부 같다고 취급합니다.[^idk]

[^idk]: 교수님이 그 이유도 자세하게 설명해주셨는데 이해를 잘 못했습니다...

### 집합의 정의

Coq에서 집합을 정의하는 방법은 딱 두가지입니다. 모든 집합은 아래의 두 방법을 잘 이용해서 정의합니다.

1. `Inductive`
1. `->`

낯이 익은 친구들이죠? 아래에서 하나하나 살펴보겠습니다.

#### `Inductive`

집합을 정의하는 가장 단순하고 직관적인 방법입니다. `Inductive`라고 쓴 뒤, 각 가지마다 그 집합의 constructor를 하나씩 나열하는 방식입니다.

```coq, line_num
Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
```

`red`는 `rgb` 집합의 원소입니다. 그래서 `red : rgb`이죠. 그럼 `primary`의 type은 뭘까요? `primary`는 `rgb` 하나를 받아서 `color`를 내놓는 constructor로, `primary : rgb -> color`입니다. 그럼 `primary red`는요? 이 친구는 `color` 집합의 원소니까 `primary red : color`입니다.

`Inductive`를 다루는 방법은 (원칙적으로는) `match`를 사용하는 것밖에 없습니다. `match c with ...`의 `c`에다가 `color`의 원소를 하나 주고, 뒤에 가지들에 `color`의 모든 constructor를 나열해야합니다. 예시로 `is_red`를 정의해보겠습니다.

```coq, line_num
Definition is_red (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary p => match p with
    | red => true
    | green => false
    | blue => false
    end
  end.
```

`match` 안에 `match`를 중첩시키려니 너무 귀찮습니다. 그래서 Coq은 `match`를 중첩시키지 않고 한번에 적을 수 있게 해줍니다.

```coq, line_num
Definition is_red (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary green => false
  | primary blue => false
  end.
```

여전히 귀찮습니다. `false`로 끝나는 가지들이 중복되는데 더 줄일 수 없을까요? Coq은 남은 가지들을 한번에 묶어버리는 `_`도 지원합니다.

```coq, line_num
Definition is_red (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.
```

훨씬 깔끔하군요. Coq의 `match`에는 이것 말고도 다양한 문법적 설탕 (syntactic sugar)들이 있습니다.

#### `->`

함수를 이용해서 집합을 정의하는 방법입니다. 예를 들어서 `nat -> nat`는 `nat`을 받아서 `nat`을 내놓는 모든 함수들의 집합입니다.

예를 들어서, `fun x => match x with | 0 => 0 | S n => n end`는 `nat -> nat` 집합의 원소입니다.

#### `Definition`

그럼 `Definition`은 뭐냐고 궁금해하실 수도 있습니다. `Definition`은 집합을 정의하는게 아닙니다. `Definition`은 단순히 값에 이름을 붙이기만 합니다. 예를 들어서, `42`란 숫자가 코드에 자주 등장해서 이름을 붙이고 싶다? 그럼 `Definition answer := 42.`라고 쓰는 거죠. 함수의 정의들도 동일합니다. 함수의 정의는 기본적으로 `fun` 키워드를 이용해서 하지만, 함수에 이름을 붙여서 사용하고 싶으니 `Definition` 키워드를 사용하는 거죠.

다만 함수의 정의는 매우 자주 쓰이니 사용자의 편의를 위해서 몇가지 문법을 생략하는 것을 허용합니다. 아래의 예시를 보겠습니다.

```coq, line_num
Definition is_zero : nat -> bool :=
  fun n : nat => match n with
  | O => true
  | S n' => false
  end.

Definition is_zero' (n : nat) : bool :=
  match n with
  | O => true
  | S n' => false
  end.
```

`is_zero`는 아무런 문법도 생략하지 않고 `Definition`의 원래 모양 그대로 쓴 형태입니다. `is_zero`라는 이름을 붙이고 뒤에 `fun`을 그대로 썼죠. `is_zero'`는 몇가지 문법을 축약한 형태입니다. 함수의 인수들이 이름 옆에 붙고, `fun` 키워드가 생략됐죠.

#### `Fixpoint`

그럼 `Fixpoint`는 뭐냐고 궁금해하실 수도 있습니다. `Fixpoint`도 근본적으론 `Definition`과 똑같습니다. 다만 `fun` 대신에 `fix`를 써야하는 상황이고 ([여기](Chap4-2.html#keywordfix) 참고), `Definition` 대신에 `Fixpoint`란 키워드를 쓸 뿐입니다.

### 집합의 포함관계

아까부터 계속 `:`란 기호는 집합의 포함관계를 나타낸다고 설명하고 있습니다. 이 설명은 그럭저럭 들어맞는 것 같아요. 근데 Coq을 보다보면 아리송한 부분들이 생깁니다.

`Theorem plus_0_n : forall n, 0 + n = n.`이란 표현을 봅시다. 여기에 `:`가 나오는데 이게 집합의 포함관계를 나타내...나요? 얼핏 봐서는 어디가 집합인지 알기가 힘듭니다. 여기서는 `forall n, 0 + n = n`이 하나의 집합입니다. 정확히 말하자면 `forall n, 0 + n = n`은 `Prop`이고 `Prop`은 증명들의 집합입니다. 만약 그 집합이 비어있으면 `plus_0_n`은 거짓이고 원소가 있으면 `plus_0_n`은 참입니다. 그 집합의 원소는 아래처럼 정의할 수 있습니다.

```coq, line_num
Definition plus_0_n : forall n, 0 + n = n :=
  fun n => eq_refl.

Definition plus_0_n : forall n, 0 + n = n :=
  fun n => @eq_refl nat n.
```

아까 집합을 정의하는 방법에는 `Inductive`와 `->`의 2가지가 있다고 했죠? `forall n, 0 + n = n`은 둘다 아닌 것처럼 보이지만 `->`입니다. `:=` 뒤에 `fun`이 쓰인 걸 보면 알 수 있습니다. [9장](Chap9-1.html#forallfunc)에서 봤던 것처럼 `forall`은 사실 `->`입니다. 그래서 `plus_0_n`에는 `nat` 하나를 받아서 `0 + n = n` 하나를 반환하는 함수가 옵니다. `0 + n = n`은 왜 집합일까요? `=`의 [정의](Chap9-3.html#equality)를 보면, `Inductive`로 돼 있습니다. 즉, `0 + n = n`은 `0 + n`과 `n`이 같다는 증명들의 집합입니다.

## Currying

[4-2 단원](Chap4-2.html#currying)에서 보았던 currying을 다시 봅시다! `bool` 2개를 받아서 `bool` 하나를 내놓는 `andb`라는 함수를 생각해보겠습니다. 보통 아래처럼 정의하겠죠.

```coq, line_num
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
```

방금 전에 `Definition`이 `fun`을 축약할 수 있다고 했죠? `fun`을 축약하지 않고 정의 그대로 써보면 아래와 같은 모양이 나옵니다.

```coq, line_num
Definition andb : bool -> (bool -> bool) :=
  fun (b1: bool) =>
    fun (b2: bool) =>
      match b1 with
      | true => b2
      | false => false
      end.

Compute andb true.   (* fun x => x *)
Compute andb false.  (* fun _ => false *)
```

Type부터가 신기합니다. `bool`을 받아서 `bool -> bool`을 내놓는 함수입니다. 이게 [4단원](Chap4-2.html#functions-that-return-other-functions)에서 봤던 partial application인데요, Coq에서 모든 함수는 인수를 하나만 받습니다. 인수 2개를 받으려면 첫번째 인수를 받아서 그 인수를 처리하는 함수를 만든 뒤, 그 함수가 두번째 인수를 받습니다.

그래서 Coq에게 `andb true false`를 계산하라고 시키면 Coq은 내부적으로 `andb true : bool -> bool`를 만든 뒤, 그 함수에다가 `false`를 집어넣습니다. 즉, `(andb true) false`를 하는 거죠.

9번째 줄부터가 신기합니다. Coq에게 `andb true`를 시키면 `fun x => match true with | true => x | false => false end.`가 나와야할 것 같습니다. 하지만 Coq은 `match true with`가 의미가 없다는 걸 파악하고 가지치기를 해버립니다. 그래서 항등함수가 나옵니다. `andb false`도 마찬가지 이유로 상수함수가 나옵니다. 최적화라고 해야할지 어쨌든 신기하네요.

## Dependent Types

Dependent types은 다른 언어에서는 거의 찾을 수 없고 Coq에서만 찾을 수 있는 기능입니다. 하지만 Coq에서는 아주 광범위하게 쓰이죠. 방금 전에 보았던 `forall n, 0 + n = n`부터가 dependent type입니다. 한번 자세히 뜯어보죠.

위에서 말했듯이 `0 + n = n`은 `0 + n`과 `n`이 같다는 증명들의 집합입니다. 그래서 `n`이 달라지면 다른 집합이 됩니다. 그럼 그 `n`은 누가 결정하죠? 바로 앞에 있는 `forall n`이 결정합니다. 다른 인수에 의해서 이 함수의 type이 결정되죠? 그래서 depedent type입니다. 다른 예시들도 보겠습니다.

[4장](Chap4-1.html#repeat)에서 보았던 `Fixpoint repeat (X : Type) (x : X) (count : nat) : list X` 같은 모양의 함수도 dependent type을 사용했습니다. `repeat`의 두번째 인수의 type은 `X`죠? 근데 `X`는 `repeat`의 첫번째 인수입니다. 즉, `repeat`의 첫번째 인수의 값이 두번째 인수의 type을 결정하는 형태입니다.

C나 Python만 써오시던 분들은 신기하게 느껴지실 수 있습니다. 저도 그랬어요. 그나마 C스러운 예시를 생각해보자면 다음과 같습니다. ~_자연수 `n`을 인수로 받아서 크기가 `n`인 배열을 반환하는 함수_~를 생각해봅시다. 만약 크기가 다른 배열을 다른 type으로 생각한다면, 저 함수도 dependent type입니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]
