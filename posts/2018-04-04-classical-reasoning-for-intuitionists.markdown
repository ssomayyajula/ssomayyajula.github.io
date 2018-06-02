---
title: Classical reasoning for intuitionists
---

<blockquote style="text-align:right;">
  <p>By ratiocination, I mean computation.</p>
  <footer>---Thomas Hobbes</footer>
</blockquote>

## Introduction

Realizability captures the computational flavor of intuitionistic logic by defining what the proof/realizer of a proposition ought to be in terms of computable objects i.e. terms of the lambda calculus. Here's a quick, and I hope, intuitive summary of a realizability interpretation for higher-order logic.

<center>
|                   | **is proven by** |                   | **if** |
|:-----------------:|:----------------:|:-----------------:|:------:|:---
| $P\land Q$        |                  | $(p, q)$          |        | $p$ proves $P$ and $q$ proves $Q$
| $P\lor Q$         |                  | $\textsf{inl}(p)$ |        | $p$ proves $P$
| $P\lor Q$         |                  | $\textsf{inr}(q)$ |        | $q$ proves $Q$
| $P\Rightarrow Q$  |                  | $\lambda p.~f(p)$ |        | for all proofs $p$ of $P$, $f(p)$ proves $Q$
| $\forall x, P(x)$ |                  | $\lambda x.~p(x)$ |        | for all $x$, $p(x)$ proves $P(x)$
| $\exists x, P(x)$ |                  | $(x, px)$         |        | $px$ proves $P(x)$
| $x = y$           |                  | $\textsf{refl}$   |        | $x$ is semantically identical to $y$
</center>

Furthermore, let $\top$ be always proven by $()$ and $\bot$ be proven by nothing at all. Then, define $\lnot P\triangleq P\Rightarrow\bot$. In other words, we know $P$ doesn't hold when it implies a contradiction. 

As a result, a proof of the law of excluded middle (LEM) $P\lor\lnot P$---the single axiom rejected by intuitionists---would be an algorithm that can compute evidence in support of or contrary to $P$ for _any_ $P$. This is absurd, what if $P$ is uncomputable or your logic is incomplete? **The rejection of LEM is a statement that the only knowledge obtainable is that which is computable modulo completeness.**

However, LEM is admissible with certain caveats. First, you can do the obvious thing and include LEM _without a realizer_. Of course, any canonicity result you have proven about your theory is now utterly destroyed. Furthermore, any theory with a constructive proof of decidability $\textsf{decide}(P)$, which computes evidence for or against $P$, may include LEM with $\textsf{decide}$ as its realizer. However, when working in an undecidable theory like higher-order logic, there are different methods of recovering classical reasoning. Here's a summary of all of the ones I've seen during my studies.

## Double-negation translation

We may embed classical logic into intuitionistic logic via a syntactic transformation called the _double-negation translation_. For the moment, let's restrict our attention to propositional logic.

<dl>
<dt><b>Double-negation translation</b>
  <dd>Double negate any atomic subformula and disjunction in a formula.</dd>
</dt>
</dl>

Then, we get the following result.

<dl>
  <dt><b>Corollary of Glivenko's theorem</b></dt>
  <dd>$\phi$ is a classical tautology if and only if the double-negation translation of $\phi$ is an intuitionistic tautology.</dd>
</dl>

Essentially, whenever we can't prove a classical tautology intuitionistically, we may obtain a result that is equal in _truth_ (in terms of truth-value semantics), since double-negation is eliminable in classical logic, but not in _evidence_ (in terms of realizability). For example, the version of De Morgan's law $\lnot(P\land Q)\Rightarrow\lnot P\lor\lnot Q$ is classically but not intuitionistically valid. However, we can prove the following analogue (in Lean).

```lean
example {P Q : Prop} : ¬(¬¬P ∧ ¬¬Q) → ¬¬(¬¬¬P ∨ ¬¬¬Q) :=
λ h c, h ⟨λ np, c (or.inl (λ nnp, nnp np)), λ nq, c (or.inr (λ nnq, nnq nq))⟩
```

And of course, we can prove something equivalent to LEM.

```lean
example {P : Prop} : ¬¬(¬¬P ∨ ¬¬¬P) :=
λ h, h (or.inr (λ nnp, h (or.inl nnp)))
```

When quantifiers enter the mix, the translation becomes a bit more complicated, see the [here](https://ncatlab.org/nlab/show/double+negation+translation#firstorder_case) for more details.

While this method technically works, it's a little unsatisfying, because we end up having to prove a different theorem altogether. So, maybe we can do better.

_Reference: [Double-negation translation](https://ncatlab.org/nlab/show/double+negation+translation) at the nLab_

## Proof erasure

Let's further investigate the possiblity of admitting LEM without a realizer. In general, we are interested in proving propositions of the form $\forall x, (P(x)\Rightarrow\exists y, Q(y))$. Computationally, it is a statement that objects with some property can be transformed into other objects with some other property, so its realizer is of the form $f\triangleq\lambda x.~\lambda px.~(f(x), g(f(x), px))$. Now, assume that the realizers of our knowledgebase are extracted to a codebase to be run as a complete program. By virtue of our proofs, $Q(y)$ holds for all outputs $y$ and that all callers of $f$ are guaranteed to pass inputs $x$ satisfying $P(x)$, so the interactions in our codebase are totally safe. As a result, at runtime, we only care about the _computational content_---$x$ and $y$---and not the proofs witnessing their adherence to certain specifications. Thus, we can erase them from the realizer to obtain the term $\lambda x.~f(x)$, which is equally safe but dramatically more efficient in the best case.

There are many ways to codify erasure into a proof system, so here's one way: Lean has a special universe `Prop` for propositions which is distinct from the universe `Type` for proper types with computational content. However, the terms of types in `Prop` can be safely erased if and only if they are not involved in the computation of an object whose type is in `Type`. Consider the following example.

```lean
example : Π (x y : ℕ), x ≤ y → ℕ
| x _ (nat.less_than_or_equal.refl _) := x
| _ y _                               := y
```

This term returns $x$ if $x = y$ or $y$ if $x < y$. However, it will not typecheck in Lean, since a term from the $\leq$ proposition is being used to compute the output. If it were erased, then the realizer would not know whether to return $x$ or $y$!

With erasure, noncomputable definitions like LEM are safely included into Lean's [standard library](https://github.com/leanprover/lean/blob/master/library/init/classical.lean#L69) without breaking canonicity. This is useful in reasoning about algorithms; for example, it is easier to prove that a greedy algorithm returns only optimal outputs by contradiction (i.e. double-negation elimination, which is equivalent to LEM)---by showing they are _not suboptimal_. The algorithm itself is constructive by virtue of being an algorithm, but the specificational proof---of optimality---need not be constructive, since it is erased at runtime.

```lean
def greedy_is_optimal (x : input) : {y // is_optimal y} :=
begin
  existsi ...,
  by_contradiction,
  ...
end
```

To recover classical reasoning completely, `Prop` is also _proof irrelevant_ i.e. it denies that multiple proofs of the same proposition are distinguishable up to propositional equality (in the case of Lean; some systems have this hold judgmentally). After all, if certain data are to be erased anyway, why should the proof system distinguish between them? For example, if we have a type of nonzero natural numbers consisting of pairs $(n, pn)$ where $pn$ is a proof that $n\neq0$, then we would like $(n,pn)=(n,pn')$ if and only if $n=n'$ i.e. we don't want to have to prove that $pn=pn'$. Users of systems without proof irrelevance do not have this luxury, and would have to manually prove $pn=pn'$, which is a pain and even more painful if it is outright false by design. We can summarize this section with the following mantra.

<center>
**Classical reasoning is admissible when it's not leveraged computationally**
</center>

To see how other systems do it, check out the reference below as well as Constable's paper on [virtual evidence](https://arxiv.org/pdf/1409.0266.pdf).

_Reference: [Erasure](https://github.com/sweirich/pi-forall/blob/2014/notes4.md#erasure-aka-forall-types) by Stephanie Weirich_

## First-class continuations

Lastly, it turns out that we can embed LEM directly (kind of) in a language with _first-class continuations_, like Standard ML. For the moment, forget about everything you know about continuations, and assume that SML defines `type 'a cont = 'a -> 'b` but abstracted, `callcc : ('a cont -> 'a) -> 'a`, and `throw : 'a cont -> 'a -> 'b`. Expanding the type of `callcc` shows that it realizes Peirce's law, which is equivalent to LEM! In fact, here's a proof that Peirce's law implies LEM, with some definitions first ($\bot$ and disjunction).

```ml
datatype void = void

fun absurd (v : void) : 'a =
  absurd v

type 'a not = 'a -> void

datatype ('p, 'q) or = L of 'p | R of 'q

open SMLofNJ.Cont

fun lem (_ : unit) : ('p, 'p not) or =
  callcc (fn k => R (throw k o L))
```

This seems too good to be true, does SML have a magic oracle that can decide any proposition? No! To understand why, we need to figure out how continuations, the terms inhabiting `'a cont`, work. In reality, a continuation is not a function, but a function-like object that intuitively represents the current evaluation context when acquired through `callcc`. `throw`ing a value to the current continuation (from `callcc`) resumes execution of the term in that context but with the new value, implementing some sort of non-local control flow.

Thus, looking at how LEM is implemented, **it is not a realizer in our interpretation**---it will immediately return $\lnot P$ unless it is thrown a proof of $P$ later in time. To see this in action, consider the following query of whether or not an integer exists.

```ml
- case lem () of
    L i  => print (Int.toString i ^ "\n")
  | R ni => print "integers don't exist!\n"

integers don't exist!
```

That's debatable...in fact, if we refute this by constructing a witness, we get some sensible output, namely our proof: `0`.

```ml
- case lem () of
    L i  => i
  | R ni => absurd (ni 0)
- val it = 0 : int
```

Nevertheless, we get to do classical reasoning, so here's double-negation elimination i.e. proof by contradiction.

```ml
fun dne (h : 'p not not) : 'p =
  case lem () of
    L a  => a
  | R na => absurd (h na)
```

Finally, we can prove the above variant of De Morgan's law directly, following the proof [here](https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Disjunction_of_Negations/Formulation_1/Reverse_Implication).

```ml
fun de_morgan (h : ('p * 'q) not) : ('p not, 'q not) or =
  dne (fn f => h (dne (f o L), dne (f o R)))
```

Recall that `unit` is $\top$. If we run `de_morgan` on some examples, we get straight up counterintuitive results.

```ml
- case de_morgan (fn ((x, y) : unit * void) => y) of
    L np => print "true is false!\n"
  | R nq => print "false is false!\n"
```
`true is false!`
```ml
- case de_morgan (fn ((x, y) : unit * void) => y) of
    L np => absurd (np ())
  | R nq => print "false is false!\n"
```
`false is false!`

Stay away from `callcc`, kids.

_Reference: [Continuations and Logic](https://www.cs.cmu.edu/~rwh/courses/typesys/hws/hw5/hw5-handout.pdf) by Evan Cavallo_

_P.S. Any double-negation translation with respect to proof terms is a transformation into continuation-passing style, where the current evaluation context is an explicit parameter of every term to be called at every computation step._

## Conclusion

Classical reasoning in intuitionistic logic is attainable using different techniques with different implications. For something more like the last section, which dealt with realizing LEM directly, check Alexandre Miquel's _[A Survey of Classical Realizability](https://link.springer.com/chapter/10.1007/978-3-642-21691-6_1)_ to learn about such advanced topics as forcing and the model theory behind the madness.

