---
title: Category-theoretic abstractions with OCaml
---

Software engineering with imperative and object-oriented programming languages often utilizes certain _design patterns_: [templates so abstract that they can't be encoded as a library](https://www.quora.com/What-are-some-functional-programming-design-patterns/answer/Tikhon-Jelvis?srid=TnTB). Functional programming, on the other hand, is famous for translating concepts in category theory to concrete programmatic abstractions that scale well for a lot of problems. In my opinion, the most basic "pattern" is `Functor-Applicative-Monad`, a hierarchy for generalizing function application and composition. While that sounds quite abstract, this hierarchy allows us to encode such concepts as error handling and stateful computation. Personally, I've used some combination of `Functor-Applicative-Monad` in _every_ Haskell project I've worked on.

But this post isn't about Haskell; in fact, we'll start with a discussion of the category theory behind `Functor-Applicative-Monad`, their respective implementations in OCaml, and the practicality of these abstractions. Why OCaml? Such abstractions aren't typically used in favor of more _ad hoc_ ones and using the module system as opposed to Haskell's open typeclasses pose an interesting challenge. In an effort to be as self-contained as possible, this post only assumes knowledge of set theory and basic OCaml.

So let's dive in. Abstract algebra deals with such structures as groups, rings, and fields that are, in general terms, sets endowed with operations between their elements. Category theory generalizes this notion with the _category_. We'll use Spivak's definition from [_Category Theory for Scientists_](http://math.mit.edu/~dspivak/teaching/sp13/CT4S.pdf).

A _category_ _C_ consists of:

1. A set of _objects_ Ob(_C_)

2. A collection Hom<sub>_C_</sub>: ∀_X_, _Y_ ∈ Ob(_C_), Hom<sub>_C_</sub>(_X_, _Y_) is the set of all _morphisms_ _f :_ _X_ → _Y_.

3. An _associative_ function ∘ : Hom<sub>_C_</sub>(_Y_, _Z_) × Hom<sub>_C_</sub>(_X_, _Y_) → Hom<sub>_C_</sub>(_X_, _Z_) that obeys the following _identity law_: ∀_X_, _Y_ ∈ Ob(_C_), ∀_f_ ∈ Hom<sub>_C_</sub>(_X_, _Y_), ∃_id_<sub>_X_</sub> ∈ Hom<sub>_C_</sub>(_X_, _X_), _id_<sub>_Y_</sub> ∈ Hom<sub>_C_</sub>(_Y_, _Y_): _id_<sub>_Y_</sub> ∘ _f_ = _f_ ∘ _id_<sub>_X_</sub> = _f_ where _id_<sub>_X_</sub> and _id_<sub>_Y_</sub> are _identity morphisms_.

The conditions for ∘ in (3) are known as the _coherence conditions_ for categories.

Categories are so primitive that morphisms have no concept of functions or function application---only specific categories do. For example, **Set** is the category where objects are sets, morphisms are functions (on sets), and ∘ is standard function composition. However, [here's](http://mathoverflow.net/a/119925) a category where morphisms are _not_ functions.

In OCaml, we work in the [_syntactic category_](https://ncatlab.org/nlab/show/syntactic+category) **OCat** of OCaml types and the functions between them. 

1. Ob(**OCat**) = all OCaml types _of kind_ `*`

2. ∀`'a`, `'b` ∈ Ob(**OCat**), Hom<sub>**OCat**</sub>(`'a`, `'b`) = all `f: 'a -> 'b`

3. `let id x = x` is the identity morphism for all types because it is polytypic i.e. since its type is `'a -> 'a`, it will take on the type of the value it's called on.

4. `let (%) f g x = f (g x)` is ∘ i.e. function composition

The proofs of satisfying the coherence conditions for categories are trivial. The last part of (1) is important if you do not know about type kinds---just like values have types, types have "types" called _kinds_. Types of kind `*` refer to concrete types like `int`, type variables like `'a` and `'b`, or an arbitrary function type `'a -> 'b`. On the other hand, there are complex types i.e. _type constructors_ like `option` and `list` which have kind `* -> *` because they will return a type of kind `*` upon being applied to a type of kind `*` e.g. `'a option : *` and `int list : *`. In that sense, type constructors act as functions at the type level. We will exploit this difference later on.

Back to theory. The idea of structure-preserving maps is prevalent in algebra through the homomorphism, so the corresponding idea in category theory is the _functor_: a map _F_ that assigns objects and morphisms from a category _C_ to those in _D_ while preserving identity morphisms and composition. In mathematical terms, it consists of two functions whose signatures are defined in terms of arbitrary objects _X_ and _Y_ in _C_:

1. Ob(_F_): Ob(_C_) → Ob(_D_)
2. Hom<sub>_F_</sub>(_X_, _Y_): Hom<sub>_C_</sub>(_X_, _Y_) → Hom<sub>_D_</sub>(_F_(_X_), _F_(_Y_))

The aforementioned coherence conditions for functors are as follows with respect to arbitrary morphisms _f_: _Y_ → _Z_ and _g_: _X_ → _Y_ in _C_. For simplicity, we denote both functions by _F_.

1. _F_(_id_<sub>_X_</sub>) = _id_<sub>_F_(_X_)</sub>
2. _F_(_f_ ∘ _g_) = _F_(_f_) ∘ _F_(_g_)

Since **OCat** is the "universal" category in OCaml, we can only write functors from **OCat** to **OCat**. One example is the _identity functor_ that assigns all types (objects) and functions (morphisms) to themselves, so it trivially preserves identities and composition. However, we can get more interesting functors if we look at _subcategories_ of **OCat**, categories whose objects and morphisms are subsets of those in **OCat** and are closed under composition and identity. Consider the following module type `AT`.

```ocaml
module type AT = sig
  type 'a t
end
```

Turns out that defining a module `M : AT` induces a subcategory of **OCat**, **M**, such that:

1. Ob(**M**) = {`'a M.t` | `'a` ∈ Ob(**OCat**)}

2. Hom<sub>**M**</sub>(`'a M.t`, `'b M.t`) = all `f: 'a M.t -> 'b M.t`

3. `id` and `(%)` remain as they are polytypic.

We can then define functors from **OCat** to **M** that intuitively "promote" vanilla types and functions into their equivalent "specialized" ones while remaining in (a subcategory of) **OCat**. To induce such functors in OCaml, we have to split their signature into two function signatures mapping types and functions, respectively. Remember how we said type constructors were kind of like functions on types? Turns out the first function's signature will be the _type_ of the type constructor `M.t`, namely the _kind_ `* -> *`. The signature of the second function follows directly from specializing the general signature to OCaml types, since _F_(`'a`) = `'a t`, Hom<sub>**OCat**</sub>(`'a`, `'b`) = `'a -> 'b`, and Hom<sub>**M**</sub>(_F_(`'a`), _F_(`'b`)) = `'a t -> 'b t`.

1. Ob(_F_): `* -> *`

2. Hom<sub>_F_</sub>(`'a`, `'b`): `('a -> 'b) -> ('a t -> 'b t)`

Since we're dealing with function signatures, we can package both into a module type `FUNCTOR` representing modules that induce category-theoretic functors. The first function is actually the abstract type declaration `type 'a t` from `AT`, and we'll call the second function `fmap` for "function map."

```ocaml
module type FUNCTOR = sig
  include AT
  val fmap : ('a -> 'b) -> ('a t -> 'b t)
end
```

Thus, for some module `M : FUNCTOR`, `M.fmap` must satisfy the following specialization of functor coherence conditions; for `f: 'b -> 'c` and `g: 'a -> 'b`:

1. `M.fmap id = id`
2. `M.fmap (f % g) = M.fmap f % M.fmap g`

The usefulness of `FUNCTOR` derives from our original intuition of induced functors promoting vanilla types and functions---in fact, `'a M.t` gives _computational context_ to values in `'a`. Then, `fmap` allows us to, in effect, apply vanilla functions to values within said context.

Let's look at an example---while programming, it is often useful to construct errors and regular values in a symmetric way to make throwing errors as non-intrusive as possible. So, we'll define a type constructor `either` that partitions errors into one variant and values into another. In other words, the `('a, 'b) either` type lends vanilla values a computational context where error values are also possible.

```ocaml
type ('a, 'b) either = Left of 'a | Right of 'b
```

By convention, `Left` values are errors, so creating a module `Either : AT` given a user-defined type for `Left` values would parameterize over the type of `Right` values and induce a subcategory **Either** where functions operate on values of `(L.t, 'a) either`. Notice that we exposed the implementation of the type `'a Either(L).t` using a `with` clause so that we can work with concrete values of `(L.t, 'a) either`.

```ocaml
module type T = sig
  type t
end

module Either (L : T) : AT
  with type 'a t = (L.t, 'a) either = struct
  
  type 'a t = (L.t, 'a) either
end
```

The reason we parameterized over the type of `Right` values was so we can define a functor from **OCat** to **Either** whose `fmap` component will, upon being applied to a vanilla function, return a promoted function that returns errors as-is or applies the vanilla function to the internal value held by `Right`. Let's make an OCaml functor `EitherFunctor : FUNCTOR` to get this definition of `fmap`. Again, since we're parameterizing over the type of `Right` values, we have to leave the type of `Left` values defined by user-created modules.

```ocaml
module EitherFunctor (L : T) : FUNCTOR
  with type 'a t = 'a Either (L).t = struct
  
  include Either (L)
  
  let fmap f = function
      Left x as e -> e
    | Right v     -> Right (f v)
end
```

The proofs that this definition of `fmap` satisfies the coherence conditions for functors is a straightforward exercise of case analysis. For convenience, we'll define a module that deals with string errors.

```ocaml
module String = struct
  type t = string
end

module EitherString = EitherFunctor (String)
```

Let's try using `EitherString` in `utop`.

```
# open EitherString;;
# let divide x = function
    0 -> Left "You tried dividing by zero!"
  | y -> Right (x / y)
- : val divide : int -> int -> (string, int) either = <fun>
# let succ_e = fmap ((+) 1);;
- : val succ_e : int EitherString.t -> int EitherString.t
# succ_e (divide 6 2);;
- : int EitherString.t = Right 4
# succ_e (divide 1 0);;
- : int EitherString.t = Left "You tried dividing by zero!"
```

Neat, the attempted application of `((+) 1)` failed and propagated the error from dividing by zero.

The practicality of functors lies in the ability of `fmap` to map over structured values in a desirable yet predictable way. This behavior is so ubiquitous that it has been [proven](http://thread.gmane.org/gmane.comp.lang.haskell.libraries/15382/focus=15384) only one definition of `fmap` is possible for any type. This has led the developers of GHC to write an extension `DeriveFunctor` to automatically derive `fmap` definitions for Haskell types.

You might be thinking---why don't we just use exceptions for dealing with one-time errors like these? The power of this hierarchy lies in using _applicative functors_, which allow us to elegantly sequence computations so that, in the case of `either`, computations succeed along the way or errors just get propagated up the call stack. However, in order to implement them, we need to go back to theory again.

Remember the theme in category theory of generalizing concepts from algebra? Just like the Cartesian product in set theory, a _product category_ _C_ × _D_ is a category where objects and morphisms are pairs of their respective components from _C_ and _D_ and composition is defined pairwise on the components of morphisms.

1. Ob(_C_ × _D_) = {(_X_, _Y_) | _X_ ∈ Ob(_C_) ∧ _Y_ ∈ Ob(_D_)}

2. Hom<sub>_C_ × _D_</sub>((_X_<sub>1</sub>, _Y_<sub>1</sub>), (_X_<sub>2</sub>, _Y_<sub>2</sub>)) = all (_f_: _X_<sub>1</sub> → _X_<sub>2</sub>, _g_:_Y_<sub>1</sub> → _Y_<sub>2</sub>)

3. (_f_<sub>2</sub>: _Y_<sub>_f_</sub> → _Z_<sub>_f_</sub>, _g_<sub>2</sub>: _Y_<sub>_g_</sub> → _Z_<sub>_g_</sub>) ∘ (_f_<sub>1</sub>: _X_<sub>_f_</sub> → _Y_<sub>_f_</sub>, _g_<sub>1</sub>: _X_<sub>_g_</sub> → _Y_<sub>_g_</sub>) = (_f_<sub>2</sub> ∘ _f_<sub>1</sub>, _g_<sub>2</sub> ∘ _g_<sub>1</sub>) so _id_<sub>(_X_, _Y_)</sub> = (_id_<sub>_X_</sub>, _id_<sub>_Y_</sub>)

This allows us to define a _bifunctor_: a functor whose domain is a product category, which means it can act on pairs of objects and morphisms.

Plus, just like monoids in group theory, a _monoidal category_ is a category _C_ endowed with a bifunctor ⊗ : _C_ × _C_ → _C_ and an _identity object_ _I_ subject to the following coherence conditions; for objects _X_, _Y_, and _Z_ in _C_:

1. _I_ ⊗ _X_ ≅ X
2. _X_ ⊗ _I_ ≅ X
3. _X_ ⊗ (_Y_ ⊗ _Z_) ≅ (_X_ ⊗ _Y_) ⊗ _Z_

_A_ ≅ _B_ means there exists a [_natural isomorphism_](https://ncatlab.org/nlab/show/natural+isomorphism) between these objects, i.e. maintains some loose notion of equivalent structure. [Some monoidal categories preserve structure exactly](http://www.staff.city.ac.uk/~ross/papers/Constructors.pdf), though.

Notice that **OCat** is a monoidal category with `'a` ⊗ `'b` = `'a * 'b` and _I_ = `unit`. Let's check that the coherence conditions hold.

1. `unit * 'a` ≅ `'a` and `'a * unit` ≅ `'a` because values `((), a) ~ a ~ (a, ())` i.e. pairing with `unit` does not impose any additional structure onto the underlying value `a`.

2. `'a * ('b * 'c)` ≅ `('a * 'b) * 'c` because values `(a, (b, c)) ~ ((a, b), c)` i.e. grouping does not change the underlying triplet `(a, b, c)`.

It naturally follows that the aforementioned **M** is a monoidal category as well with `'a M.t` ⊗ `'b M.t` = `'a M.t * 'b M.t` and _I_ = `unit M.t`. This is going to be important in implementing the following definition.

Now, we'll look at functors on monoidal categories. A _strong monoidal functor_ is a functor _F_ between monoidal categories (_C_, ⊗, _I_) and (_D_, ⊗', _J_) that preserves monoidal structure.


1. _J_ ≅ _F_(_I_)
2. _F_(_X_) ⊗' _F_(_Y_) ≅ _F_(_X_ ⊗ _Y_)
3. 

We call such functors strong because we require isomorphisms to exist 

To write lax monoidal functors from **OCat** to **M**, we include signatures for the induced functor _F_ and we specialize the signatures for _i_ and \*\*. To clarify the following definitions, remember ⊗ is the bifunctor defined for **OCat** and ⊗' is the one for **M** so _F_(`'a`) ⊗' _F_(`'b`) = `'a t` ⊗' `'b t` = `'a t * 'b t` while _F_(`'a` ⊗ `'b`) = _F_(`'a * 'b`) = `('a * 'b) t`.

However, to simplify function application, _i_'s signature will be contracted to `unit t` since in **OCat**, _J_ = _F_(_I_). Furthermore, we'll change `'a t * 'b t` to `'a t -> 'b t`.

1. _i_: `unit t`
2. \*\*: `'a t -> 'b t -> ('a * 'b) t`

Let's package this into a module type called `MONOIDAL`.

```ocaml
module type MONOIDAL = sig
  include FUNCTOR
  val i      : unit t
  val ( ** ) : 'a t -> 'b t -> ('a * 'b) t
end
```

Let's create an OCaml functor to induce a lax monoidal functor from **OCat** to **Either**. _i_ is `Right ()` and \*\* must essentially combine the results of `fmap` over both inputs, short-circuiting if the first value was an error.

```ocaml
module EitherMonoidal (L : T) : MONOIDAL
  with type 'a t = EitherFunctor (L).t = struct
  
  include EitherFunctor (L).t
  
  let i = Right ()
  
  let ( ** ) x y =
    match fmap (fun a b -> (a, b)) x with
      Left _ as e -> e
    | Right f     -> fmap f y
end
```

Just like we did for `EitherFunctor`, we'll create a convenience module on string errors.

```ocaml
module EitherStringMonoidal = EitherMonoidal (String)
```

Now, lax monoidal functors induced by modules of type `MONOIDAL` aren't very useful on their own. However, with this structure in place, we can now define an _applicative functor_, which are simply two functions defined on lax monoidal functors: _pure_, which promotes values in **OCat** (values of type `'a`) to those in **M** (values of type `'a M.t`), and `(<*>)`, which is almost an extension of `fmap`; since functions are also values in `M.t`,  A common idiom then is to promote a function, apply it to a value, then rinse and repeat, getting the "sequencing" behavior we wanted earlier.

We can generate definitions for _pure_ and \<*\> using an OCaml functor `ApplicativeFn` (unfortunately, we can't define these as general functions using first-class modules due to OCaml's [lack of higher-kinded type polymorphism](http://stackoverflow.com/a/35180899)).

```ocaml
module ApplicativeFn (M : MONOIDAL) : sig
  val pure  : 'a -> 'a M.t
  val (<*>) : ('a -> 'b) M.t -> ('a M.t -> 'b M.t)
end = struct
  open M
  
  let pure x = (fun _ -> x) <$> i
  
  let (<*>) f m = (fun (f, x) -> f x) <$> (f ** m)
end
```

The definition for `pure` exploits the fact that `i` is sort of the "trivial value" of `M.t` which can be used to inject arbitrary values from **OCat**. `(<*>)` then, in effect, simultaneously checks whether the function `f` and the value `m` are errors, unboxes them, then evaluates the function application.

We can now create a module that 

_P.S. Purists might complain over these definitions because I  purposefully avoided explaining the concept of natural transformations and isomorphisms in favor of a more intuitive approach._