| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Total Maps

[예전](Chap3-4.html)에 map을 구현했습니다. 그때는 아직 Coq을 잘 모를 때라 아주 간단하게 구현하고 넘어갔는데, 이젠 좀 더 제대로 구현해보겠습니다.

이번 단원에선 total map과 partial map을 구현할 건데 그 중 total map을 먼저 구현하겠습니다. 둘의 차이는 map에 없는 원소를 찾으려고 할 때의 결과입니다. total map은 존재하지 않는 원소를 찾으려고 하면 처음에 지정된 기본값을 반환하지만, partial map은 `None`을 반환합니다.

Rust로 비유하자면 `TotalMap::get(k: K) -> V`, `PartialMap::get(k: K) -> Option<V>`입니다.

[[box]]

[[giant]] imports [[/giant]]

책에선 지금까지 Coq Standard Library를 사용하지 않고 설명을 했습니다. 만약 자연수 대소비교가 필요하다면 이전 단원에서 정의했던 함수를 사용하는 방식으로요. 그래서 저도 import와 관련된 언급을 하지 않고 진행했습니다. 하지만 이제부터는 std lib에서 import를 해서 진행을 한다네요. 여기서부터는 이 문서의 코드들을 실행시킬 때 아래의 library들을 import하고 진행하시면 됩니다!

```haskell, line_num
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
```

[[/box]]

[[box]]

[[giant]] Locate [[/giant]]

[[anchor, id = keyword locate]][[/anchor]]

책에서 `Locate`라는 명령어를 소개하던데 저도 언급을 하고 넘어가겠습니다. 만약 Coq를 사용하다가 `+`라는 기호가 어디서 정의됐는지 궁금해지면 아래와 같은 명령어를 쓰면 됩니다.

> `Locate "+"`

그럼 `+`가 포함된 `Notation`들이 전부 나옵니다.

[[/box]]

## string

다시 total map의 구현으로 돌아오겠습니다. 먼저, `string`에 대해서 살펴보겠습니다. 이전에 map을 구현할 때는 자연수를 key로 사용했지만 이젠 `string`을 사용합니다. `string`이 어떻게 정의돼 있는지 궁금해서 공식문서의 일부분을 가져왔습니다.

```haskell, line_num
Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.
```

`string`의 정의는 list와 아주 비슷하게 돼 있습니다. `list ascii`라고 생각하면 되겠군요. `ascii`의 정의도 살펴봤더니 `bool` 8개의 tuple로 돼 있습니다. 1byte를 그대로 표현했더군요.

```haskell
Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
```

위의 정의도 흥미로워서 갖고 왔습니다. `+`는 logical or 연산으로 정의된 거 같은데, 저 정의를 자세히 읽어보면 `s1과 s2는 같거나 다르다`입니다. 즉, 두 문자열이 같은지 다른지 항상 정할 수 있다는 뜻입니다. 영어 주석에도 ~_Equality is decidable_~이라고 돼 있습니다.

```haskell, line_num
Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 &&& eqb s1' s2'
 | _,_ => false
 end.

Infix "=?" := eqb : string_scope.

Notation "a &&& b" := (if a then b else false)
  (at level 40, left associativity) : lazy_bool_scope.
```

문자열 비교 함수 `eqb`의 정의입니다. 다른 type들이랑 이름이 겹치는 거 아닌가 싶을 수도 있지만 Module 안에 있기 때문에 괜찮습니다. `&&&`은 처음 보는 기호라 뭔지 찾아봤더니 lazy andb로 정의돼 있더군요. 아래에 적어놨습니다. 일반 프로그래밍 언어에서 하는 것처럼 `a`가 거짓이면 `b`를 확인하지 않는 연산자입니다.

왜 굳이 lazy하게 썼는지는 모르겠네요. 최적화때문에 그런 걸까요?

[[anchor, id = eqbrefl]][[/anchor]]

```haskell, line_num
Lemma eqb_refl x : (x =? x)%string = true.
Lemma eqb_sym x y : (x =? y)%string = (y =? x)%string.
Lemma eqb_eq n m : (n =? m)%string = true <-> n = m.
Lemma eqb_neq x y : (x =? y)%string = false <-> x <> y. 
```

그 다음은 비교와 관련된 정리 몇가지가 있습니다. 아주 자명한 사실들입니다. 자기자신과의 비교, 교환법칙 등이 설명돼있습니다.

[[box]]

[[anchor, id = keyword ampersand]][[/anchor]]

TODO

`%` 기호가 뭔지 모르겠네요. `=?`가 generic이어서 type을 지정해주는 용도인 거 같기는 한데 정확히는 모르겠습니다.

`x =? x0`라고 쓰니까 Coq가 `x`가 `nat`인 줄 알고 `(x =? x0)%string`이라고 하니까 Coq가 `x`가 `string`인 줄 아는 걸로 봐서 맞는 거 같습니다.

[[/box]]

## 구현

```haskell
Definition total_map (A : Type) := string -> A.
```

`total_map`의 정의는 위와 같습니다. 이전에는 type으로 정의했지만 이번에는 함수로 정의했습니다. 키를 받아서 값을 내놓는 동작을 함수처럼 보겠다는 것이죠. 이러면 `total_map`에서 값을 찾는 함수를 따로 만들 필요가 없다는 장점이 있습니다... 이미 만들었거든요!

[4-2 단원](Chap4-2.html)에서 봤듯이 함수도 일급객체이므로 `total_map`과 관련된 다양한 함수들을 만들 수 있습니다. 아래에서 몇가지 예시를 보겠습니다.

```haskell, line_num
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
```

`t_empty`는 빈 `total_map`을 만드는 함수입니다. 항상 `v`를 반환하는 함수를 반환했습니다. 여기서 `v`는 기본값입니다. 빈 `total_map`은 항상 기본값을 반환하겠죠.

`t_update`의 구현은 흥미롭습니다. 어떤 `total_map`을 받아서 거기에 (키, 값) 쌍을 추가하는 함수인데, 함수를 받아서 함수를 반환하도록 돼 있는 구현이 참신하네요.

```haskell, line_num
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).
```

몇가지 Notation을 정의했습니다. `_ -> v`는 `v`를 기본값으로 하는 빈 `total_map`을 만들고, `x !-> v; m`은 `m`에 (`x`, `v`)를 추가합니다. 저렇게만 보면 어떻게 쓰는지 모를 것 같아서 용례를 몇가지 갖고 왔습니다.

```haskell, line_num
Example example_empty := (_ !-> false).

Definition examplemap :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
```

아래의 예시를 보면 감이 잘 옵니다. 가장 아랫줄에 기본값을 `false`로 하는 빈 `total_map`을 만들고, 거기에 (`"foo"`, `true`)와 (`"bar"`, `true`)를 추가했습니다. 즉, `examplemap`은 `"foo"`와 `"bar"`에 대해서만 `true`를 반환하고 나머지는 전부 `false`를 반환합니다.

```haskell, line_num
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite eqb_refl.
  reflexivity.
  Qed.
```

그냥 지나가면 섭섭하니까 증명을 하나 하고 지나가겠습니다. 어떤 `total_map`에 (`x`, `v`)를 추가하고 `x`를 요청하면 `v`를 반환합니다. 아주 당연한 얘기죠? `unfold t_update`를 하면 `if (x =? x) then v else m x`만 남습니다. `x =? x = true`임이 [아까](#eqbrefl) 봤던 `eqb_refl`에 증명돼 있으므로 그걸 사용하면 증명이 끝납니다.

```haskell, line_num
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x.
  unfold t_update.
  apply functional_extensionality.
  intros x0.
  destruct (x =? x0)%string eqn: E.
  rewrite eqb_eq in E.
  - (*{- x = x0 -}*)
    rewrite E.
    reflexivity.
  - (*{- x != x0 -}*)
    reflexivity.
  Qed.
```

아직도 섭섭해서 증명 하나를 더 했습니다. [옛날](Chap6-5.html#funcext)에 봤던 `functional_extensionality`를 갖고 왔습니다.

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap7-3. Regular Expressions](Chap7-3.html)

[[/left]]

[[right]]

[Chap8-2. Partial Maps](Chap8-2.html) >>

[[/right]]