---
title: Constructivism, automated deduction, and you
---

Finally back at it again after a long while. In this post, we'll briefly discuss constructive mathematics and how its application to automated deduction allows us to develop fast and correct programs in Idris, a dependently-typed language inspired by Haskell. This will be the first in a series of posts that'll help me get my obsession with logic out of my system. First, some theory.

## Constructivism

Constructivism is a school of mathematical thought that says that proofs of claims asserting the existence of a mathematical object must explicitly construct it. While many proofs do exactly this, constructivism automatically discounts large classes of proofs that rely on reasoning like "inexistence is invalid implies existence." While this seems inherently limiting, it turns out that constructive logic is as powerful and even subsumes classical logic. However, the killer application of constructive proofs is that we can extract "computational content" from them (read: algorithms and programs). This of course excites many computer scientists, like me and hopefully you.

To figure out how to do that, we have to get a little less abstract. The logic we will be dealing with is Heyting arithmetic (HA): constructive first-order logic with equality over the natural numbers. This means we have the usual logical connectives like conjunction, implication, etc. but we also have propositional equality and universal/existential quantification over the natural numbers. Furthermore, Kleene's axiomatization of HA characterizes operations like addition and multiplication, which we will discuss later on. We will also assume some a priori choice of proof system for HA---it doesn't matter which one, since we're studying its metatheory.

To capture the constructive and computational character of HA, Kleene introduced a notion of _realizability_ in which logical formulae may be _realized_ by mathematical objects. We'll look at a modified version of his original definition below and see how that relates to constructive thought. In terms of nomenclature, $e_1$, $e_2$, etc. are _terms_ in HA (that is, expressions that resolve to natural numbers), and $n$, $m$, etc. are natural numbers.

* $n$ realizes $e_1 = e_2\iff\vDash e_1 = e_2$. False equalities are not realizable.
* $(n, m)$ realizes $P\land Q\iff n$ realizes $P$ and $m$ realizes $Q$
* $(n, t)$ realizes $P\lor Q\iff t = 0\implies n$ realizes $P$ else $n$ realizes $Q$
* $f:\mathbb{N}\to\mathbb{N}$ realizes $P\implies Q\iff f$ accepts realizers for $P$ and returns a realizer for $Q$
* $(n, m)$ realizes $\exists x.~P(x)\iff m$ realizes $P(n)$
* $f: \mathbb{N}\to\mathbb{N}$ realizes $\forall x.~P(x)\iff\forall x\in\mathbb{N},~f(x)$ realizes $P(x)$

So, how is this constructive? Consider that $(2, 1)$ realizes $\exists x. 2 \cdot x = 4$. To prove the existence of such an $x$, we had to explicitly give $x = 2$, which is precisely what constructivism is all about. The computational content is a bit more subtle---it'll only show up in more complicated examples. The main thing to understand is that **realizers are algorithms**, at least in the mathematical sense, because they demonstrate how to compute evidence for the truth of a formula.

Regardless, there seems to be a fundamental disconnect between propositions and proofs here: it seems like we can only realize valid formulae, so what happens to proofs? Since HA is sound---that is, all provable proposition are valid---and only valid propositions are realizable, only provable propositions are realizable! This means that, in your proof system of choice, you may identify proofs of propositions with their realizers. Now, we can make the transition from mathematical realizability to the computational kind.

## Programming Logic

In a [previous post](http://ssomayyajula.github.io/posts/2015-12-05-exploring-the-curry-howard-correspondence.html), I explained the duality between programming languages and logics, but you don't have to read it to understand the rest of this post. The gist is **propositions are types and proofs are programs**. We can go a step further and extend our identification of proofs and realizers to programs. In other words, programs are simultaneously proofs of propositions and realizers that compute evidence for the truth of said propositions. This allows us to encode any HA proposition as an Idris type and prove it by giving a program (function) of that type. That program will then allows us to compute some interesting stuff. Let's figure out the specific type encoding.

First, fix a set of base types $B$ such that every atomic proposition is identified with a type in $B$. Assume there also exists an empty type `Void` which has no inhabitants. Then, the following function translates propositions constructed by logical connectives into types.

\begin{align*}
[\![P\land Q]\!]&\triangleq ([\![P]\!], [\![Q]\!])\\
[\![P\lor Q]\!]&\triangleq \texttt{Either}~[\![P]\!]~[\![Q]\!]\\
[\![P\implies Q]\!]&\triangleq [\![P]\!]~\texttt{->}~[\![Q]\!]\\
[\![\lnot P]\!]&\triangleq [\![P]\!]~\texttt{-> Void}
\end{align*}

Propositional equality and quantification are a bit more difficult since they introduce terms (values) into types and thus require _dependent types_. Equality is encoded as an \emph{equality} type on values/types whose canonical inhabitant is the proof of reflexivity. Furthermore, universal quantification is encoded as the dependent function type whose codomain varies with the type of the input, since $P(x)$ varies with $x$. Secondly, existential quantification is encoded as the dependent pair type whose second component type varies with the type of the first component, since $P(x)$ varies with the specific choice of $x$. That leads us to the following translation.

\begin{align*}
[\![e_1 = e_2]\!]&\triangleq e_1~\texttt{=}~e_2\\
[\![\forall x.~P(x)]\!]&\triangleq \texttt{(x : Nat) ->}~[\![P(x)]\!]\\
[\![\exists x.~P(x)]\!]&\triangleq \texttt{(x : Nat ** }~[\![P(x)]\!]\texttt{)}
\end{align*}

Notice that Kleene's interpretation of realizability is implictly given by this encoding at the value/term level; for example, the fact that `Refl` (the compiler-understandable proof of reflexivity) inhabits `1 = 1` is dual to 1 realizing $1 = 1$, and the fact that `\(x, y) => x` inhabits `(a, b) -> a` is dual to $(n, m)$ realizing $P\land Q\implies P$. In fact, we can give a direct correspondence between realizers for HA and Idris terms.

<style>
td{
 text-align:center;
 vertical-align:middle;
}
</style>

<table align="center" border="1">
<tr>
<th>Formula</th>
<th>Realizer</th>
<th>Idris Term</th>
</tr>
<tr>
<td>$e_1 = e_2$</td>
<td>$n$</td>
<td>`Refl`</td>
</tr>
<tr>
<td>$P\land Q$</td>
<td>$(n, m)$</td>
<td>`(n, m)`</td>
</tr>
<tr>
<td>$P\lor Q$</td>
<td>$(n, 0)$ or $(n, \_)$</td>
<td>`Left n` or `Right n`</td>
</tr>
<tr>
<td>$P\implies Q$</td>
<td>$f:\mathbb{N}\to\mathbb{N}$</td>
<td>`f : Nat -> Nat`</td>
</tr>
<tr>
<td>$\exists x.~P(x)$</td>
<td>$(n, m)$</td>
<td>`(n ** m)`</td>
</tr>
<tr>
<td>$\forall x.~P(x)$</td>
<td>$f:\mathbb{N}\to\mathbb{N}$</td>
<td>`f : (x : Nat) -> P(x)`</td>
</tr>
</table>

The big takeaway from this section is that the idea of extracting algorithms from proofs is implicit in our computational system, since proofs are programs. The above might also seem like abstract nonsense, so let's see how this works out in practice by encoding HA in Idris.

## Encoding Heyting Arithmetic

Let's try out Kleene's axiomatization; Idris actually provides proofs for the more trivial ones, with the following signatures.

1. Injectivity of successor: $\forall x, y.~S(x) = S(y)\implies x = y$
```idris
succInjective : (x, y : Nat) -> S x = S y -> x = y
```

2. Equality is extensional: $\forall x, y.~x = y\implies S(x) = S(y)$
```idris
succEq : (x, y : Nat) -> x = y -> S x = S y
```

3. Zero is the additive identity: $\forall x.~x + 0 = x$
```idris
plusZeroRightNeutral : (x : Nat) -> x + Z = x
```

4. Zero is the multiplicative annihilator: $\forall x.~x \cdot 0 = 0$
```idris
multZeroRightZero : (x : Nat) -> x * Z = Z
```

5. Zero is never a successor: $\forall x.~\lnot(S(x) = 0)$
```idris
SIsNotZ : {x : Nat} -> S x = Z -> Void
```
The curly braces around `x : Nat` still denotes the dependent function type, but it simply allows `x` to be inferred from context as opposed to being explicitly passed in.

Let's do one ourselves.

6. "Transitivity" of equality: $\forall x, y, z.~x = y\implies x = z\implies y = z$
```idris
natEq : (x, y, z : Nat) -> x = y -> x = z -> y = z
natEq _ _ _ Refl Refl = Refl
```
Since this is our first sighting of `Refl` in the wild, let me explain how it works: the assumptions allows the typechecker to infer that `x ~ y` and `x ~ z`---that is, they are _exactly_ the same, so one can sort of rewrite the conclusion as `x = x`, whose proof is simply reflexivity.

Now, for the most profound axiom: the principle of mathematical induction.

7. Second-order axiom of induction: $\forall P.~P(0)\implies(\forall x.~P(x)\implies P(S(x)))\implies\forall n.~P(n)$.
```idris
induction : (P : Nat -> Type)
         -> P Z
         -> ((x : Nat) -> P x -> P (S x))
         -> (n : Nat) -> P n
induction P pz ps n = case n of
  Z    => pz
  S n' => ps n' (induction P pz ps n')
```
This is _ridiculously_ insightful: it shows that **induction is dual to recursion** since proving the inductive case requires proofs for all lesser $n$. We can now use this to prove the last two axioms.

First, we're going to have to learn how to manipulate propositional type equalities. Idris gives a syntax `rewrite [eq : x = y] in [expr]` which substitutes the first instance of `x` with `y` in the type of `expr`.

8. Successor of the sum: $\forall x, y.~x + S(y) = S(x + y)$. Since Idris defines addition by recursion on the first argument, we'll proceed by induction on $x$.

```idris
succPlusSucc : (x, y : Nat) -> x + S y = S (x + y)
succPlusSucc x y =
  {- Proceed by induction on x -}
  induction
    (\x => x + S y = S (x + y))
    {- Typechecker can infer Z + S y = S (Z + y) => S y = S y -}
    Refl
    {- Assuming x + S y = S (x + y), show S x + S y = S (S x + y).
       Typechecker infers that S x + S y = S (S x + y) ~ S (x + S y) = S (S (x + y))
       Proof:
         We have
           px   : x + S y = S (x + y),
           Refl : S (S (x + y)) = S (S (x + y)),
         Given that sym px : S (x + y) = x + S y,
         `rewrite sym px in Refl` replaces the first instance of
         S (x + y) with x + S y in S (S (x + y)) = S (S (x + y))
         to yield Refl : S (x + S y) = S (S (x + y)), as desired. -}
    (\x => \px => rewrite sym px in Refl)
    x
```

9. Multiplying the successor: $\forall x, y.~x \cdot S(y) = x \cdot y + x$. This one is a bit tricky; we have to use the above theorem plus a proof of the associativity of addition.

```idris
multPlusSucc : (x, y : Nat) -> x * S y = x * y + x
multPlusSucc x y =
  induction
    {- Proof by induction on x. -}
    (\x => x * S y = x * y + x)
    {- Typechecker can infer Z * S y = Z * y + Z => Z = Z -}
    Refl
    {- Assuming x * S y = x * y + x, show S x * S y = S x * y + S x.
       Typechecker rewrites goal as S (y + x * S y) = (y + x * y) + S x,
       and infers that Refl :
         (y + x * y) + S x = (y + x * y) + S x
       Transform the goal by the inductive hypothesis:
         => S (y + (x * y + x)) = (y + x * y) + S x
       Use the theorem S (y + (x * y + x)) = y + S (x * y + x)
         => y + S (x * y + x) = (y + x * y) + S x
       Use the theorem S (x * y + x) = x * y + S x
         => y + (x * y + S x) = (y + x * y) + S x
       Use the theorem y + (x * y + S x) = (y + x * y) + S x
         => (y + x * y) + S x = (y + x * y) + S x
       Since they're now the same type, their proof is reflexivity.
     -}
    (\x, px =>
       rewrite px in
       rewrite sym (succPlusSucc y (x * y + x)) in
       rewrite sym (succPlusSucc (x * y) x)     in
       rewrite plusAssociative y (x * y) (S x)  in
       Refl)
    x
```

That finishes it; unsurprisingly, Idris' encoding of the natural numbers is powerful enough to simulate HA.

## Case Study

So now that we've flexed our induction skills, let's do something that's actually useful: develop a fast and correct program in Idris using our encoding for HA. Inspired by NuPRL, an automated proof assistant developed at Cornell (Go Red!), we'll derive a linear algorithm that computes the square root of a natural number, called "fast integer square root." I encourage you to read the original [paper](http://www.cs.cornell.edu/courses/cs5860/2014fa/documents/Kreitz-%20Derivation%20of%20a%20Fast%20Integer%20Square%20Root%20Algorithm.pdf) by Christoph Kreitz which details several different methods, including the derivation of a logarithmic algorithm.

Anyways, here's the proposition: $\forall n.~\exists r.~r\cdot r\leq n\land n<(r + 1)\cdot(r + 1)$. $r$ is called the _square root_ of $n$.

To encode the relation $\leq$, Idris provides the following inductive type.

```idris
data LTE  : (n, m : Nat) -> Type where
  LTEZero : LTE Z    right
  LTESucc : LTE left right -> LTE (S left) (S right)
```

In other words, the base case is $\forall n.~0\leq n$. The inductive case is, if $n\leq m$, then $S(n)\leq S(m)$. We'll also use some functions in the standard library for manipulating inequalities. In particular, note that $n < m\iff n + 1\leq m$, so `LT n m = LTE (S n) m`.

We will also need the following lemma, $\forall x, y.~\lnot(x\leq y)\implies y < x$.

```idris
notLteLt : {x, y : Nat} -> Not (x `LTE` y) -> y `LT` x
notLteLt {x} {y} =
  induction
    {- Proof by induction on x. -}
    (\x => Not (x `LTE` y) -> y `LT` x)
    {- Assume ~(0 <= y), but evidence for 0 <= y is given by LTEZero
       Therefore by ex falso quodlibet (void), y `LT` x -}
    (\nlte => void (nlte LTEZero))
    {- Given
         px : ~(x <= y) => y < x i.e. y + 1 <= x
         nlte : ~(x + 1 <= y)
       Show y < x + 1 i.e. y + 1 <= x + 1 i.e. y <= x.
       Proof. Case analysis.
         if ~(x <= y), apply the IH.
         if y <= x => y < x + 1. -}
    (\x, px, nlte =>
       case (isLTE x y, isLTE y x) of
         (No nlte', _) => lteSuccRight $ px nlte'
         (_,  Yes lte) => LTESucc lte
         {- It's impossible for x <= y when the
            assumption is ~(x <= y). -}
         (Yes _,    _)    impossible)
    x
```

Now for the proof, with the informal version written in the comments.

```idris
{- forall n. exists r. r * r <= n < (r + 1) * (r + 1) -}
intSqrtPf : (n : Nat) -> (r : Nat ** ((r * r) `LTE` n, n `LT` (S r * S r)))
intSqrtPf n =
  induction
    {- Proof by induction on n. -}
    (\n => (r : Nat ** ((r * r) `LTE` n, n `LT` (S r * S r))))
    {- Base case: n = Z. Choose r = Z.
       Z * Z <= Z and Z < 1 * 1, trivially.
       Typechecker infers:
         Z * Z <= Z => Z <= Z,
           whose proof is LTEZero : Z `LTE` Z
         Z < 1 * 1 => Z < 1,
           whose proof is LTESucc LTEZero : 1 `LTE` 1 ~ Z `LT` 1 -}
    (Z ** (LTEZero, LTESucc LTEZero))
    {- Given
         lte : r * r <= n
         lt  : n < (r + 1) * (r + 1) i.e. n + 1 <= r^2 + 2r + 1, show
         exists r'. r' * r' <= n + 1 < (r' + 1) * (r' + 1)
       Proof. By case analysis.
         if (r + 1) * (r + 1) <= n + 1, then
            r' = r + 1.
            We get (r + 1) * (r + 1) <= n + 1 by the conditional.
            If we add 1 to the LHS and 2r + 3 to the RHS of lt,
            we get n + 1 < (r + 2) * (r + 2).
         else
           r' = r.
           We get r * r <= n => r * r <= n + 1.
           Since we know ~((r + 1) * (r + 1) <= n + 1), 
             we get n + 1 < (r + 1) * (r + 1). -}
    (\n, (r ** (lte, lt)) =>
      case isLTE (S r * S r) (S n) of
        Yes lte' => (S r ** (lte',
          let lt' =
            LTESucc (lteTransitive lt (lteAddRight (S r * S r) {m = r + r})) in
          let lt'' = lteSuccRight (lteSuccRight lt') in
          {- Rewrite lt'' to match the goal type. -}
          let lt1 = replace {P = \x => LTE (S (S n)) (S (S (S (S x))))}
            (plusAssociative (r + r * S r) r r) lt'' in
          let lt2 = replace {P = \x => LTE (S (S n)) (S (S (S (S (x + r + r)))))}
            (sym (multRightSuccPlus r (S r))) lt1 in
          let lt3 = replace {P = \x => LTE (S (S n)) (S (S (S (S (x + r)))))}
            (plusCommutative (r * S (S r)) r) lt2 in
          let lt4 = replace {P = \x => LTE (S (S n)) (S (S (S (S x))))}
            (plusCommutative (r + r * S (S r)) r) lt3 in
          let lt5 = replace {P = \x => LTE (S (S n)) (S (S (S x)))}
            (plusSuccRightSucc r (r + r * S (S r))) lt4 in
          let lt6 = replace {P = \x => LTE (S (S n)) (S (S x))}
            (plusSuccRightSucc r (S (r + r * S (S r)))) lt5 in
            lt6))
        No nlte => (r ** (lteSuccRight lte, notLteLt nlte)))
    n
```

If you look closely, the constructive proof for the existence of an integer square root encodes a recursive algorithm to find it! However, now that the proof is done, we don't really care for it. In other words, we'll define a function that projects out $r$ and throws out the proof term for ease of use.

```idris
intSqrt : Nat -> Nat
intSqrt n = fst (intSqrtPf n)
```

Now let's test this in the Idris REPL.

```
*HA> intSqrt 49
7 : Nat
*HA> intSqrt 200
14 : Nat
```

It works! We just extracted an algorithm for finding the square root of an integer that's pretty decent in terms of speed. But most importantly, we know with 100% certainty that it's correct up-to specification.

Out of curiosity, what does a proof term look like for `intSqrtPf`? Let's try it on $n = 4$.

```
*HA> intSqrtPf 4
(2 **
 (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))),
  LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))) :
    (r : Nat ** ((r * r) `LTE` 4, 4 `LT` (S r * S r)))
```

The proof of existence yields $r = 2$, as expected. In order to understand the proof terms, you need to read them as series of implications. Given `LTEZero : LTE 0 0`, we know `LTESucc : LTE n m -> LTE (S n) (S m)`. As a result, the repeated applications of `LTESucc` give the cascade $0\leq 0\implies 1\leq 1\implies 2\leq 2\implies 3\leq 3\implies 4\leq 4$ in the proof for $r\cdot r\leq 4$. The goal for the second part is $4 < 9$ i.e. $5\leq 9$. Given `LTEZero : LTE 0 4`, we get $0\leq 4\implies 1\leq 5\implies 2\leq 6\implies 3\leq 7\implies 4\leq 8\implies 5\leq 9\iff 4 < 9$, as desired.

## Future Work

So now that we've proven to ourselves (pun intended) that constructive proofs are very useful for software development, how can we make this process less painful? In particular, having to manually show to the typechecker that certain terms are equal is _really_ annoying. To answer that, many languages like Idris offer an interactive interface for proofs using _tactics_, functions that automate certain parts of the proof process like demonstrating equality.

And, if you're curious about my previous claim that constructive logic subsumes classical logic, read Cornell professor Robert Constable's [paper](https://arxiv.org/abs/1409.0266) on encoding classical logic using "virtual evidence."

The source code for this post is [here](https://gist.github.com/ssomayyajula/2b3c60ad4c671b2f8989d2c59a2a67fe).
