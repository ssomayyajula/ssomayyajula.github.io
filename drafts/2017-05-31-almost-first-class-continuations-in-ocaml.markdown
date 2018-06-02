---
title: Continuations from scratch
---

If you lurk in functional programming circles you may have seen Lispers rave about `call/cc` or Haskellers claim that "[the continuation monad is in some sense the mother of all monads](http://blog.sigfpe.com/2008/12/mother-of-all-monads.html)." If you'd like to learn what continuations are all about and see if they live up to the hype, stay tuned.

Abstractly speaking, having _first-class continuations_ in a programming language allows the programmer to arbitrarily change the control flow of a program at runtime. As a result, all of your favorite control flow constructs like exceptions, cooperative multitasking, etc. can all be implemented using continuations.

The journey to (almost) first-class continuations in OCaml starts with some theory---specifically, writing programs in _continuation-passing style_.

As a result, we will implement (almost) first-class continuations in OCaml and then try our hand at a mini Concurrent ML-style cooperative multitasking library. Then, we'll finish up with multithreaded quicksort.

## Continuation-passing style

Writing programs in the _continuation-passing style_ is intuitively characterized in two ways.
1. The control flow of t
2. 

If we consider the core language of OCaml---that is, only constants, variables, functions, and function application (i.e. the applied lambda calculus), then we can define a CPS translation.

Translating constants and variables are fairly straightforward---instead of returning them directly, we pass them onto the continuation $k$.

\begin{align*}
[\![n]\!]~k&\triangleq k~n\\
[\![x]\!]~k&\triangleq k~x
\end{align*}

Function application is a bit more involved but the principle is the same. We need to explicitly demarcate the control flow of the expression and then pass the overall result to the continuation.

$$[\![e_0~e_1]\!]~k\triangleq[\![e_0]\!]~\texttt{(fun f -> }[\![e_1]\!]\texttt{(fun v -> f v }k\texttt{))}$$

Under OCaml's operational semantics, `e_0` is evaluated first, whose value is then passed to a continuation that takes the resultant function and evaluates `e_1`, which passes that value to another continuation which performs the actual application with the original continuation $k$.

Functions

$$[\![\texttt{fun }x\texttt{ -> }e]\!]~k\triangleq k~(\texttt{fun }x\texttt{ -> }[\![e]\!])$$

Notice that if the continuation $k$ has the type `'a -> 'r`, then 

Ideally, we'd be able to implement the following signature.

```ocaml
(** The type of continuations accepting arguments of type 'a *)
type 'a cont

(** `callcc f` applies `f` to the "current continuation" *)
val callcc : ('a cont -> 'a) -> 'a

(** `throw k a` invokes the continuation `k` with argument `a` *)
val throw : 'a cont -> 'a -> 'b
```

However, knowing what the "current continuation" requires an ambient context specifying the state of the runtime. Indeed, SML/NJ's implementation of this signature uses some built-in magic to achieve this. As a result, we need to create and manipulate a context of our own using a _monad_. We will adapt Haskell's continuation monad for 

## Deriving the continuation monad

```ocaml
open Core.Std

(** The continuation monad *)
type ('a, 'r) t

(** Construct a CPS computation from a continuation-accepting function *)
val cont : (('a -> 'r) -> 'r) -> ('a, 'r) t

(** Run a CPS computation on a continuation *)
val run : ('a, 'r) t -> ('a -> 'r) -> 'r

(** Calls a function on the "current" continuation *)
val callcc : (('a, 'b, 'r) cont -> ('a, 'r) t) -> ('a, 'r) t

include Monad.S2 with type ('a, 'r) t := ('a, 'r) t
```

## Case study: Cooperative multitasking

