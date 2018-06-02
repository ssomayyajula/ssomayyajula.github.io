---
title: Proofs of functor laws in Haskell
---

Haskell defines a typeclass <a href="https://wiki.haskell.org/Functor"><code>Functor</code></a> containing a function <code>fmap</code> which allows developers to apply a function over the contents of an instance without changing the actual structure of the data (note that this is roughly equivalent to the formal definition of a functor). To achieve this guarantee, instances of <code>Functor</code> must obey the following two laws where <code>fmap :: (a -> b) -> f a -> f b</code>, <code>id :: a -> a</code>, <code>f :: b -> c</code>, and <code>g :: a -> b</code>:

1. <code>fmap id      == id</code>
2. <code>fmap (f . g) == (fmap f . fmap g)</code>

Proving these laws on different instances is a useful exercise, especially when you come up with your own instance for an arbitrary data structure and you need to verify that it is correct, so let's prove them on two instances of <code>Functor</code>: <code>Maybe a</code> and <code>[a]</code>. For all the non-Haskellers out there, the former is a data structure that implements nullable values of <code>a</code>, and the latter is a list of <code>a</code>'s.

## Nullable values: The <code>Maybe a</code> functor

A value of <code>Maybe a</code> is either <code>Just a</code> or <code>Nothing</code>; the instance should allow us to apply a function on either <code>a</code> in <code>Just a</code> or fail silently on <code>Nothing</code> without changing anything else. Therefore, <code>fmap</code> is defined as the following.

```haskell
instance  Functor Maybe  where
    fmap _ Nothing       = Nothing       (1)
    fmap f (Just a)      = Just (f a)    (2)
```

These proofs are fairly straightforward and follow the common theme of considering either case of <code>Maybe a</code>.

### Proof of the first law

**Claim**: _On_ <code>m</code> _of_ <code>Maybe a</code>, <code>fmap id m == id m</code>.

_Proof_. On cases of <code>m</code>.

_**Case 1**_: <code>m == Nothing</code>.

```haskell
fmap id m == fmap id Nothing {- by expansion of m -}
          == Nothing         {- by fmap (1) -}
          == id m            {- by definition of id, m -}
```

_**Case 2**_: <code>m == Just a</code>.

```haskell
fmap id m == fmap id (Just a) {- by expansion of m -}
          == Just (id a)      {- by fmap (2) -}
          == Just a           {- by expansion of id -}
          == m                {- by definition of m -}
          == id m             {- by definition of id -} ∎
```

### Proof of the second law

**Claim**: _On_ <code>m</code> _of_ <code>Maybe a</code>, <code>fmap (f . g) m == (fmap f . fmap g) m</code>.

_Proof_. On cases of <code>m</code>.

_**Case 1**_: <code>m == Nothing</code>.

```haskell
fmap (f . g) m == fmap (f . g) Nothing
                      {- by expansion of m -}
               == Nothing
                      {- by fmap (1) -}
```

```haskell
(fmap f . fmap g) m == fmap f (fmap g Nothing)
                           {- by expansion of (.) and m -}
                    == fmap f Nothing
                           {- by fmap (1) -}
                    == Nothing
                           {- by fmap (1) -}
```

_**Case 2**_: <code>m == Just a</code>.

```haskell
fmap (f . g) m == fmap (f . g) (Just a)
                      {- by expansion of m -}
               == Just ((f . g) a)
                      {- by fmap (2) -}
```

```haskell
(fmap f . fmap g) m == fmap f (fmap g (Just a))
                           {- by expansion of (.), m -}
                    == fmap f (Just (g a))
                           {- by fmap (2) -}
                    == Just (f (g a))
                           {- by fmap (2) -}
                    == Just ((f . g) a)
                           {- by definition of (.) -}
```

Therefore, <code>fmap (f . g) m == (fmap f . fmap g) m</code> in all cases. ∎

## Lists: The <code>[a]</code> functor

The <code>[a]</code> functor should allow us to apply a function to every element of a list without changing anything else. Thus, <code>fmap = map</code>, which is defined as the following.

```haskell
map :: (a -> b) -> [a] -> [b]
map _ []     = []                (1)
map f (x:xs) = f x : map f xs    (2)
```

The proofs here are a bit harder since lists have infinitely many cases to consider, so we must turn to induction.

### Proof of the first law

**Claim**: _On a list_ <code>l</code>, <code>fmap id l == id l</code>.

_Proof_. By induction on the length of <code>l</code>.

_**Base case**_: On a list where <code>length l == 0</code>, i.e. <code>l = []</code>.

```haskell
fmap id l == map id [] {- by expansion of fmap, l -}
          == []        {- by map (1) -}
          == id []     {- by definition of id -}
```

_**Inductive hypothesis**_: Assume that <code>fmap id l' == id l'</code> where <code>length l' < length l</code>. Since <code>l = x:xs</code> where <code>x</code> and <code>xs</code> are the head and tail of <code>l</code>, respectively, <code>fmap id xs == id xs</code> as <code>length xs < length l</code>.

_**Inductive step**_:

```haskell
fmap id l == map id (x:xs)     {- by expansion of fmap, l -}
          == id x : fmap id xs {- by map (2), defn. of fmap -}
          == id x : id xs      {- by inductive hypothesis -}
          == x:xs              {- by expansion of id -}
          == id l              {- by definition of id, l -} ∎
```

### Proof of the second law

**Claim**: _On a list_ <code>l</code>, <code>fmap (f . g) l == (fmap f . fmap g) l</code>.

_Proof_. By induction on the length of <code>l</code>.

_**Base case**_: On a list where <code>length l == 0</code> i.e. <code>l = []</code>.

```haskell
fmap (f . g) l == map (f . g) []
                      {- by expansion of fmap, l -}
               == []
                      {- by map (1) -}
```

```haskell
(fmap f . fmap g) l == map f (map g [])
                           {- by expansion of (.), fmap, l -}
                    == map f []
                           {- by map (1) -}
                    == []
                           {- by map (1) -}
```

_**Inductive hypothesis**_: Assume that <code>fmap (f . g) l' == (fmap f . fmap g) l'</code> where <code>length l' < length l</code>. Since <code>l = x:xs</code> where <code>x</code> and <code>xs</code> are the head and tail of <code>l</code>, respectively, <code>fmap (f . g) xs == (fmap f . fmap g) xs</code> as <code>length xs < length l</code>.

_**Inductive step**_:

```haskell
fmap (f . g) l == map (f . g) (x:xs)
                      {- by expansion of fmap, l -}
               == (f . g) x : fmap (f . g) xs
                      {- by map (2), definition of fmap -}
```

```haskell
(fmap f . fmap g) l == map f (map g (x:xs))
                           {- by expansion of (.), fmap, l -}
                    == map f (g x : map g xs)
                           {- by map (2) -}
                    == f (g x) : map f (map g xs)
                           {- by map (2) -}
                    == (f . g) x : fmap f (fmap g xs)
                           {- by definition of (.), fmap -}
                    == (f . g) x : (fmap f . fmap g) xs
                           {- by definition of (.) -}
                    == (f . g) x : fmap (f . g) xs
                           {- by inductive hypothesis -}
```

Therefore, <code>fmap (f . g) l == (fmap f . fmap g) l</code> in all cases. ∎

### Was it all for naught?

Turns out these instances of <code>Functor</code> implement <code>fmap</code> correctly. However, turns out proving the second law in any case is redundant due to the <a href="https://www.fpcomplete.com/user/edwardk/snippets/fmap">free theorem of <code>fmap</code></a>, but it was fun anyways.