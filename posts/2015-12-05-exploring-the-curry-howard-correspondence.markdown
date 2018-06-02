---
title: Exploring the Curry-Howard correspondence
---

This topic has been treated by many great sources such as [this](https://www.seas.upenn.edu/~cis194/hw/10-gadts.pdf) and [that](http://www.seas.harvard.edu/courses/cs152/2015sp/lectures/lec15-curryhoward.pdf), but I'd like to give my take on it. The Curry-Howard correspondence is a powerful idea that states that there exists an equivalence between programs and proofs. In other words, there is an isomorphism mapping programs to proofs, allowing us to find programs that represent proofs and vice versa by definition. This raises the question: how do we go about proving theorems with programs? We can start by finding the connection between propositional logic and functions. 

_Types are formulas and programs are proofs_.

Therefore, _a formula is valid iff there exists a function (program) with the corresponding type_.

So how do we construct the correspondence between formulas and types? It's not immediately apparent, but the big idea is that there exists a connection between validity and the [inhabitants](https://codewords.recurse.com/issues/three/algebra-and-calculus-of-algebraic-data-types) of a type: the values it describes. Thus, we can use the following rule to define the relationship.

A type _p_ represents a valid formula iff it refers to an inhabitable type <code>p</code>.

We can then define the correspondence between formulas constructed with logical connectives and types.

1. _Falsities are_ ⊥, corresponding to the uninhabited type.
2. _Negation is a function p →_ ⊥ _on any input._ This allows us to take any valid formula (inhabitable type) and produce its negation: a falsity, or ⊥.
3. _Disjunctions are sum types/tagged unions._ _p_ ∨ _q_ can be represented by <code>Either p q</code>, which can take on values/inhabitants of either <code>Left p</code> or <code>Right q</code>, capturing the behavior of disjunctions.
4. _Conjunctions are product types._ Since the tuple <code>(p, q)</code> requires the presence of values from both types <code>p</code> and <code>q</code>, they describe conjunctions.
5. _Implications are abstractions._ A function _p → q_ requires the presence of _p_ for the presence of _q_, adequately describing conditionals.

Note that some semantics of natural deduction, namely the rules of introduction that allow us to derive valid formulas, are encoded in the construction of these types. For example, introducing a conjunction between _p_ and _q_ requires both formulas to be valid. This is evident in the construction of <code>(p, q)</code>, which requires the presence of both types _p_ and _q_. However, we would still need to manually prove rules of elimination, but those are trivial. For example, we can perform left and right elimination on a conjunction by extracting either element of the tuple and noting that they are present. Now, we can go straight to writing proofs of basic and derived argument forms. But first, let's define some useful type synonyms corresponding to the above five rules.
```haskell
{-# LANGUAGE TypeOperators #-}
module NaturalDeduction where

data (⊥) -- no possible inhabitants
type (¬)p = p -> (⊥)
type (∧) = (,)
type (∨) = Either
type (→) = (->)
```
Let's prove a few theorems. Consider the trivial _modus tollens_, which states that (_p_ → _q_) ∧ ¬_q_ → ¬_p_. The corresponding program in Haskell is the following.
```haskell
modusTollens :: (p → q) ∧ (¬)q → (¬)p
modusTollens (φ, ψ) = ψ . φ
```
This reads a bit weird, but we're essentially saying that given an inhabitant of <code>p</code>, we can derive a contradiction by producing an inhabitant of <code>q</code> by function application and stating not <code>q</code> at the same time. Since this is a well-typed and proper function, we have proven _modus tollens_.

But what about something more fundamental, like the _law of the excluded middle_? Turns out, it is impossible to prove _axioms_, because they are, by definition, assumed to be true. To get around this, we can define an infinitely recursive function <code>true</code> such that we can assign any type to it. As a result, we can define laws and axioms as <code>true</code> so that their type signatures are proper, and therefore the formulas to which they correspond are valid.
```haskell
true :: truth
true = true

exclMid :: p ∨ (¬)p
exclMid = true
```
This is of course not a carte blanche to mark theorems you are too lazy to prove as true, but a nice way of introducing axioms into the system.

So let's try something harder, like the _transposition theorem_: (_p_ → _q_) ↔ (¬_q_ → ¬_p_). Since this involves a biconditional, we can introduce this as a type synonym. Furthermore, the proof requires applications of _modus tollens_ and _double negation_, allowing us to compose proofs based on previous proofs of theorems.
```haskell
type p ↔ q = (p → q) ∧ (q → p)

dblNeg :: p ↔ (¬)((¬) p)
dblNeg = (flip ($), true) -- ($) is actually modus ponens

transposition :: (p → q) ↔ ((¬)q → (¬)p)
transposition =
    (curry modusTollens, \c p -> -- c = contrapositive
        undoDblNegate $ curry modusTollens c $ dblNegate p)
            where (dblNegate, undoDblNegate) = dblNeg
```
Proving double negation works in the forward direction by applying negation then later undoing it by function application, but this cannot be done in the backwards direction since we can't "undo" lambda abstraction. As a result, we have to let it be accepted as true. To prove transposition in the forward direction, we simply apply _modus tollens_. In the backwards direction, we must apply _modus tollens_ to (¬_q_ → ¬_p_) and the double negative of _p_, then undo the double negation to get the correct result.

In short, we've effectively created a system to prove theorems (automated theorem provers, anyone?) by exploiting the Curry-Howard correspondence. The big takeaway is that we can prove theorems by encoding their logic in the type signatures of functions and can actually go about proving them by manipulating inhabitants. A gist of the source code can be found [here](https://gist.github.com/sivawashere/dabeff9fed2ac8b68cc2).

P.S. _A great exercise would be to extend this system to accommodate universal quantification._
