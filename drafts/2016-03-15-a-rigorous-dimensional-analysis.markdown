---
title: Rigorous dimensional analysis
---

Dimensional analysis gives us a language to discuss physical quantities, but it would be useful (and fun) to develop a rigorous, mathematical framework that characterizes such concepts as the definition of a dimension and conversion between units based on our previous intuition. As a proof that our formulation is "rigorous enough," we'll implement this system in Haskell, and a subset of the SI and Imperial.

Intuitively, _physical quantities_ are measureable properties, like area and length. A _dimension_ represents a physical quantity in this formal system. Specifically, given a finite set _B_ that contains dimensions for _base quantities_, we construct the set _D_ of all dimensions that also includes _derived quantities_ by finite applications of the following rules.

1. 1 ∈ _D_
2. _x_ ∈ _B_ ⇒ _x_ ∈ _D_
3. _x_, _y_ ∈ _D_ ⇒ _x • y_ ∈ _D_
4. _x_ ∈ _D_ ⇒ _x_<sup>-1</sup> ∈ _D_

Additionally, elements of _D_ satisfy the following properties.

1. 1 • _x_ = _x_ • 1 = _x_
2. (_x_ • _y_) • _z_ = _x_ • (_y_ • _z_)
3. _x_ • _y_ = _y_ • _x_
4. _x_ • _x_<sup>-1</sup> = _x_<sup>-1</sup> • _x_ = 1

In other words, _D_ is a _free abelian group_ with basis _B_ and group operation •. Thus, to be as general as possible, we can write a data structure `FreeAb` whose value constructors correspond to the above rules and whose instance of `Eq` satisfy the above properties.

```haskell

```

Let's also define exponentiation for notational convenience.

```haskell

```

Since the set of dimensions is just a free abelian group, we'll give it a type synonym.

```haskell

```

Let's briefly switch over to `Dimensional.Quantity` and write out the dimensions for some base and derived quantities.

```haskell

```

Now let's switch back to `Dimensional.Core`: we need to define a system for representing _values_ of physical quantities. A _unit_ is a standard value of a physical quantity; intuitively, the set of units is a free abelian group over a basis of _elementary units_: a base scalar and dimension. We can define this structure as a `FreeAb` over a tuple.

```haskell

```

We can define all the SI base units in `Dimensional.SI`. Conveniently, all of the standard values are 1, except for the kilogram.

```haskell

```

Let's go a step further and define some _derived units_ in the SI module.

```haskell

```

All of the imperial units can be defined in terms of SI units.

```haskell

```

TODO unit conversion

To be able to represent _measurements_ in an arbitrary unit system, we need to define a data structure in `Dimensional.Core` that associates a scalar with a unit.

```haskell

```

This structure wouldn't be useful unless it works with existing arithmetic operators, so let's make it an instance of `Num`.

```haskell

```

--TODO metric prefixes

Now let's test it in the `cabal repl`.

