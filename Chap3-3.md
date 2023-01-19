| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Options

Haskell 혹은 Rust를 사용해본 적이 있는 분들은 Rust의 `Option` 타입과 Haskell의 `Maybe` 타입에 익숙하실 겁니다. 저 두 언어가 아니더라도 대부분의 최신언어들은 nullable 타입을 지원합니다. Coq도 비슷한 개념을 지원합니다. 아래의 예시를 보겠습니다.

```coq, line_num
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

`natoption`은 `Some nat` 혹은 `None`의 값을 갖는 타입입니다. 이 역시 generic한 표현이 가능한데, 그 부분은 [나중](Chap4-1.html)에 다시 보겠습니다. 이 타입을 이용해서 get 함수를 다시 정의해보겠습니다.

```coq, line_num
Fixpoint get (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
    | O => Some a
    | S n' => get l' n'
    end
  end.
```

비슷한 방식으로 head 함수도 다시 정의해보겠습니다.

```coq, line_num
Definition head (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.
```

[[box]]

#### Search

[[anchor, id = keyword search]][[/anchor]]

Coq를 쓰다보면 이전에 증명한 theorem들을 다시 사용할 일이 정말 많습니다. 이전에 증명한 theorem의 개수가 아주 많을텐데 그 이름들을 다 외우고 있기란 쉽지 않죠. 그래서 Coq에는 `Search`라는 키워드가 있습니다. Theorem의 이름을 검색하는데 쓰죠. 아래의 예시들을 보겠습니다.

- `Search rev.`
  - `rev`를 포함하는 모든 theorem을 검색합니다.
  - `rev`는 타입이름일 수도 있고 함수이름일 수도 있습니다.
  - 다만, 이름에 `rev`이란 문자열을 포함하는 theorem을 검색하지는 않습니다.
- `Search (_ + _ = _ + _).`
  - 주어진 패턴을 포함하는 theorem을 검색합니다.
  - CoqIDE에서 아무것도 include하지 않고 위와 같이 검색하면 아래와 같은 결과가 나옵니다.
    - f_equal2_plus: forall x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2
- `Search (_ + _ = _ + _) inside Induction.`
  - 모듈을 특정할 수도 있습니다. SQL을 쓰는 기분이네요.
- `Search (?x + ?y = ?y + ?x).`
  - 위와 같이 패턴매칭을 할 수도 있습니다.
  - 패턴 안의 `x`, `y`는 실제 이름이 아니고 패턴에 불과합니다. [[br]]즉, `Search (?y + ?x = ?x + ?y).`라고 검색해도 동일한 결과가 나옵니다.
  - add_comm: forall x y : nat, x + y = y + x
    - CoqIDE에는 기본으로 포함돼 있지 않습니다. 만약 이런 theorem을 미리 정의한 적이 있다면 위와 같은 query로 검색 가능하다는 얘기입니다.

[[/box]]

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chap3-2. Lists](Chap3-2.html)

[[/left]]

[[right]]

[Chap3-4. Maps](Chap3-4.html) >>

[[/right]]