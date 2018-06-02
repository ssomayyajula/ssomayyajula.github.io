---
title: Discrete dynamical systems with Haskell
---

A discrete dynamical system is given by <b>x</b><i>ₖ</i>₊₁ = <i>A</i><b>x</b><i>ₖ</i> for <i>k</i> = 0, 1, 2, ... with a matrix <i>A</i> and an initial state vector <b>x</b>₀. Often times it's useful to observe the long-term behavior of a system by finding its steady state vector---that is, a vector <b>q</b> for which <b>q</b> = <i>A</i><b>q</b>. We can do this in Haskell by declaring a linear transformation <b>x</b> ↦ <i>A</i><b>x</b> and finding its fixed point given the initial state. In other words, we will repeatedly apply the linear transformation, starting with the initial state, until we converge to a single vector (conventionally, one would just solve the equation <b>q</b> = <i>A</i><b>q</b>). Conveniently enough, Haskell defines some data structures and functions for computing fixed points, and I'll cheat a bit by using <a href="https://hackage.haskell.org/package/linear">a linear algebra library</a>, although implementing one from scratch might be left to a future post.

For simplicity, we'll work with 3 × 3 matrices and 3-vectors. First, we must define a data structure for state vectors and systems.

```haskell
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.Ratio
import Linear.Matrix
import Linear.V3
import Linear.Epsilon
import Control.Monad.Fix

type State = V3 Double

data System = System {
    x0 :: State,
    a :: M33 Double
}
```

Now for a brief interlude on fixed points. The module <code>Control.Monad.Fix</code> defines a function <code>fix</code> that infinitely applies a function with a starting parameter, like so: f(f(...f(x)...)).

```haskell
fix :: (a -> a) -> a
fix f = let x = f x in x
```
We can "fix" recursive functions by redefining them with an auxiliary parameter <code>rec</code> that is used for the recursive call instead of the function itself. For example, the factorial function is normally defined as the following.

```haskell
f n = if n == 0 then 1 else n * f $ n - 1
```
Our "fixed" version is:

```haskell
f rec n = if n == 0 then 1 else n * rec $ n - 1
```

This essentially converts a recursive function to a non-recursive one, because <code>fix</code> will keep passing said function as <code>rec</code>. As a result, <code>fix</code> enables support for recursion in primitive languages like the lambda calculus. Furthermore, notice that we always need to have a base case/terminating condition, so that <code>fix</code> doesn't recur forever.

So how do we get from <code>fix</code> to a system's steady state vector? First, we need to define a terminating condition: we want our linear transformation <code>t</code> to terminate when <b>q</b> = <i>A</i><b>q</b>. However, we can't check for strict equality because (1) we're dealing with floating-point numbers and (2) we're checking for <i>convergence</i> with this method, and not actual equality. With that in mind, let's define an operator <code>===</code> that returns whether or not two vectors are close enough to each other to be considered equal.

```haskell
(===) :: State -> State -> Bool
a === b = nearZero $ a - b
```

Now we're ready to define a function <code>steadyState</code> that takes a system and returns its steady state vector. Thus, we will pass <code>fix</code> a function <code>t</code> that will return the result of computing <i>A</i><b>x</b> if it <code>===</code> <b>x</b>, otherwise it will recur on <i>A</i><b>x</b>. Once we pass <code>fix</code> the initial state vector as well, it will magically converge to the steady state of the system. 

```haskell
steadyState :: System -> State
steadyState System{..} = fix t x0 where
    t rec xk = let xk1 = a !* xk in
        if xk1 === xk then
            xk1 -- We found it, so terminate
        else
            rec xk1 -- Keep going
```

Now that we've defined everything, let's test it on a discrete-time Markov chain, with an initial probability vector and stochastic matrix.

```haskell
dtmc = System {
    x0 = V3 1 0 0,
    a = V3 (V3 0.5 0.2 0.3) -- Row-major representation
           (V3 0.3 0.8 0.3)
           (V3 0.2 0.0 0.4)
}
```

Let's load up all of this code in <code>ghci</code> and run it.

```
$ ghci steadystate.hs
...
*Main> steadyState dtmc
V3 0.30000038146975283 0.5999988555908204 0.10000076293942693
```

That's reasonably close to the vector (.3, .6, .1), which is the right answer according to my textbook. The source for this project is on <a href="https://gist.github.com/sivawashere/f4bd3a0ed4f2832264ae">github</a>.