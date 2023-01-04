Mathematics is 'reasoning about sets', and
Programming is 'computing about data'.

We find a similarity here: 'reasoning = computing' and 'sets = data'.

---

There are 2 ways to define data, and each way has 2 rules.

- Way 1: `Inductive`
- Way 2: Function sets
  - `nat -> nat` is a set.
  - `(nat -> nat) : Type` is a set of all functions from `nat` to `nat`.
  - a function is an element of a function set
    - ex: `fun x : nat => match x with | O => 1 | S n => n + 1 end : nat -> nat`
  - In Coq, a function definition using the keyword `Definition` is just a syntactic sugar.

```
Definition andb1 : bool -> (bool -> bool) :=
  fun (b1: bool) =>
    fun (b2: bool) =>
      match b1 with
      | true => b2
      | false => false
      end.

Definition andb2 (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
```

`andb2` is a syntactic sugar for `andb1`. That's the beauty of the functional programming. `Compute andb1 true.` will give you an identity function with a type `bool -> bool`. Give it a try! In the same sense, `andb1 false` is a constant function always returning `false` regardless of the input.

Internally, `andb1 true false` is evaluated to `(andb1 true) false`, because function application is left-associative. `(andb1 true)` is a function with a type `bool -> bool`, and it gets `false` as an input.

---

In Coq, `:` means a membership (ex: `n : nat` means `n` is a member of `nat`). In Coq, everything has a membership: everything is inside another set.
- Is `n` a set? No, because nothing is a member of `n`.
- In Coq, one can be set only if it's declared as a `Type`.
- eg: `Inductive day : Type := | monday | tuesday | wednesday.`
  - `day` and `Type` are sets.
  - `day` is an element of `Type`.
  - `monday` is an element of `day`.

In Coq, `Type` and `Set` are the same. `Set`s are just for backward compatibility.

`Type` is the only predefined set in Coq.
- Coq says `Type` is an element of `Type`, but that doesn't mean it's a self-containing set. `Type`s have hierarchies. `Type` is an element of another, greater type, but Coq doesn't give different names to different `Type`s. But internally, Coq keeps track of index of each `Type`. That means Coq distinguishes between different `Type`s.

---

`Definition` doesn't define a set. It defines a value. And the value may have a type `Type`.

Defining a function using the `Definition` keyword can be understood in the same way.

```
(fun (b1 b2 : bool) => match b1 with
| true => b2
| false => false
end) true false.
```

The above code works fine, but it's too clumsy. That's why we define a function (which is a value) using the keyword and give it a name.