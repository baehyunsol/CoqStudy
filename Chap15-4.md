| 목차 |
|-------------------|
|!![[collapsible, default=hidden]]  |
|[[toc]]|

# Subtyping

이번 장에서는 subtyping에 대해서 공부해보겠습니다. 아래의 stlc 코드를 살펴봅시다.

```line_num
Person  = {name:String, age:Nat}
Student = {name:String, age:Nat, gpa:Nat}

(\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}
```

4번 줄의 람다함수는 `Person` 하나를 인수로 받아서 그 `Person`의 `age`에 1을 더해서 반환합니다. 그리고 그 함수에 `Person`이 아닌 `Student`를 인수로 줬어요. 저렇게 주면 우리의 stlc 언어는 타입이 맞지 않는다면서 실행을 거부합니다. 근데 직관적으로 생각해보면 저 코드에는 문제가 없어요. 어차피 `age`라는 항목만 있으면 상관없는데 그럼 `Person`이 들어오든 `Student`가 들어오든 상관없는 거 아닌가요?

이건 모든 프로그래밍 언어에서 아주 중요하게 다루는 문제입니다. `Duck`이라는 타입과 `Goose`라는 타입을 만든다고 치면, 둘은 차이점보다 공통점이 더 많습니다. 둘다 수영도 하고 울음소리도 내는데, 둘을 위해서 동일한 함수를 두번씩 정의하면 너무 귀찮겠죠? 그걸 해결하기 위해 프로그래밍 언어들은 다양한 방법을 제시합니다.

예를 들어서, 자바/C++등의 객체지향 언어들은 [상속](https://en.wikipedia.org/wiki/Inheritance_(object-oriented_programming))이란 방법을 사용합니다. `Bird`라는 클래스를 정의해서 새들의 특징을 저 클래스 안에 서술한 뒤, 오리만의 특징은 `Duck`에 서술하고 거위만의 특징은 `Goose`에 서술합니다. 그 뒤, `Duck`이 `Bird`를 상속하고 `Goose`도 `Bird`를 상속하게 함으로써 문제를 해결합니다.

파이썬/루비처럼 [duck-typing](https://en.wikipedia.org/wiki/Duck_typing)을 사용할 수도 있습니다. duck-typing은 인수의 타입을 전혀 신경쓰지 않습니다. 위에서 본 코드의 4번 줄의 함수를 예로 들면, 인수가 `age`라는 멤버를 가지는지만 확인을 하고 코드를 실행시킵니다.

Rust처럼 [composition](https://en.wikipedia.org/wiki/Object_composition)을 사용할 수도 있습니다. 오리의 특징은 여러가지가 있습니다. 날 수 있다는 점을 `Fly`라는 trait에 서술하고, 물에 산다는 점을 `Aqua`라는 trait에 따로 서술합니다. 또, 꽥꽥거린다는 특징은 `Quack`에 서술하고요. `Duck`을 만들 때는 오리가 갖는 특징들을 조합해서 만듭니다. `Fly`, `Aqua`, `Quack`을 조합해서 `Duck`이란 타입을 만들고 `Swim`, `Aqua`를 조합해서 `Fish`를 만드는 식으로요. 상속은 위에서 아래로 내려온다면 composition은 아래에서 위로 올라간다고 볼 수 있습니다.

저희가 이번 단원에서 배울 subtyping은 상속에 가장 가까운 개념입니다.

## 정의

`S`가 `T`의 subtype일 때, 아래와 같은 표기를 사용하겠습니다.

> `S <: T`

이 경우, `T`를 써야하는 자리에 `S`를 써도 됩니다. [맨 위](#subtyping)의 예시에서, `Person` 자리에 `Student`를 써도 되는 것처럼요. 그 성질을 subsumption이라고 부르고 아래와 같이 표기합니다.

```
     Gamma ⊢ t1 ∈ T1     T1 <: T2
     -------------------------------            (T_Sub)
           Gamma ⊢ t1 ∈ T2
```

한국말로 풀어보면, ~_Gamma라는 상황에서 `t1`의 타입이 `T1`이고, `T1`이 `T2`의 subtype일 때, `t1`의 타입은 `T2`이다._~ 정도가 되겠네요.

예시를 들어보면 `Goose <: Animal` 정도로 들 수 있습니다. `Animal`을 필요로하는 함수가 있으면 걔한테 `Goose`를 줘도 됩니다. `Animal`이 갖는 정보들은 `Goose`도 전부 갖거든요. 이때 `Goose`를 `Animal`의 subtype이라고 합니다.

## 성질

subtype의 성질들을 설명하겠습니다.

```
    S <: U    U <: T
    ----------------               (S_Trans)
         S <: T

         ------                    (S_Refl)
         T <: T
```

가장 당연한 성질 2개를 먼저 설명하겠습니다. `S`가 `U`의 subtype이고 `U`가 `T`의 subtype이면 `S`는 `T`의 subtype입니다. 또한, 모든 타입은 자기자신의 subtype입니다.

```
    S1 <: T1    S2 <: T2
    --------------------            (S_Prod)
     S1 * S2 <: T1 * T2
```

그다음은 product에 관한 성질입니다. `Student` 2개로 이뤄진 tuple은 `Person` 2개로 이뤄진 tuple의 subtype입니다.

```
    T1 <: S1    S2 <: T2
    --------------------            (S_Arrow)
    S1 -> S2 <: T1 -> T2
```

마지막으로 함수의 인수/반환값에 관련된 성질입니다. `S`와 `T`는 추상적이라 조금 머리가 안 돌아가니 구체적으로 예시를 들겠습니다.

```
Goose <: Animal    Apple <: Food
--------------------------------
Animal -> Apple <: Goose -> Food
```

`Goose -> Food`의 함수를 `f`라고 하고, `Animal -> Apple`의 함수를 `g`라고 하겠습니다. `f`의 자리에 `g`를 넣어도 됩니다. `f`의 인수로 `Goose`가 들어올텐데, `g`는 `Animal`을 기대합니다. `Goose`는 `Animal`이니까 `g`는 정상적으로 동작할 수 있습니다. `f`의 반환값을 사용하는 코드들은 `Food`를 기대할텐데, `g`는 `Apple`을 내놓습니다. `Food`로 할 수 있는 건 `Apple`로도 전부 할 수 있으므로 문제가 없습니다.

### Records

그렇다면 record 타입[^rcd]에서는 subtype을 어떻게 정의할까요? 아래의 subtype들은 전부 타당해보입니다.

[^rcd]: Rust/C의 struct, Python/JAVA/C++의 class, Javascript의 object에 대응됩니다.

```
{name: String, age: Nat, gpa: Nat} <: {name: String, age: Nat}
{name: String, age: Nat} <: {name: String}
```

정보가 추가되는 건 상관이 없거든요. 아래의 subtype도 타당해보입니다.

```
{name: String, pet: Cat} <: {name: String, pet: Animal}
```

멤버의 일부만 subtype으로 바꿨으니 전체도 subtype이 성립합니다. 마지막으로 아래의 경우도 subtype이 성립합니다.

```
{name: String, age: Nat} <: {age: Nat, name: String}
```

어차피 record의 값을 사용할 때는 멤버의 이름만 중요하지, 순서는 중요하지 않습니다. 그래서 순서를 바꿔도 됩니다.

저 규칙들을 모두 포괄해서 정리해보면 아래와 같습니다.

```
          forall jk in j1..jn,
      exists ip in i1..im, such that
            jk=ip and Sp <: Tk
    ----------------------------------             (S_Rcd)
    {i1:S1...im:Sm} <: {j1:T1...jn:Tn}
```

아주 강력한 규칙이긴 하지만 너무 장황합니다. 그래서 보통은 3개를 쪼개서 각각의 규칙을 씁니다. 아래처럼요.

```
                           n > m
             ---------------------------------                 (S_RcdWidth)
             {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                  S1 <: T1  ...  Sn <: Tn
             ----------------------------------                (S_RcdDepth)
             {i1:S1...in:Sn} <: {i1:T1...in:Tn}

    {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
    ---------------------------------------------------        (S_RcdPerm)
             {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
```

교과서에선 subtyping을 이렇게 배우지만 실제 언어에서는 저 subtyping이 모두 구현되지 않는 경우들도 많습니다. 예를 들어서, record의 각 멤버의 순서가 달라도 상관없다고 했지만, 실제로는 안 그럴 때도 많습니다. 컴파일러가 클래스를 만들 때 각 멤버의 순서별로 인덱스를 주는 경우가 대부분이거든요.

### Top

```

    --------         (S_Top)
    S <: Top
```

`Top`이라는 타입을 정의한 뒤, 모든 타입은 `Top`의 subtype이라고 정의했습니다. 이런 타입을 정의해두면 때때로 유용합니다. 이는 실제 프로그래밍 언어에서도 자주 쓰이는데, 예를 들면 Java에는 `Object`라는 타입이 있고 모든 타입은 `Object`로부터 상속을 받습니다. 

---

[[center]]

[메인으로 돌아가기](index.html)

[[/center]]

[[left]]

<< [Chapter 15-3. ??](Chap15-3.html)

[[/left]]

[[right]]

다음 글이 없습니다.

[[/right]]