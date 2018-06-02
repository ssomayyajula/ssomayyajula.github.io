----
title: Axiomatic semantics for stack effects
----

The Wikipedia page on [stack-oriented programming languages](https://en.wikipedia.org/wiki/Stack-oriented_programming_language) suggests an interesting challenge: formulating their axiomatic semantics.

For the uninitiated, such languages operate, in a semantic sense, on a stack to perform computations. As a result, one can vi

First, fix a set $E$ such that a stack consisting of elements $e\in E$ is inductively defined as follows.

$$\sigma ::= \emptyset\,\mid\,\sigma :: e$$

$::$ is left associative; for example, the stack $\emptyset :: 1 :: 2 :: 3$ over $\mathbb{N}$ is read $((\emptyset :: 1) :: 2) :: 3$. As a result, the constructor $::$ is identifiable with the push operation, so how does pop look? It simply deconstructs $::$---that is, $pop: (\sigma::h)\mapsto\sigma$ and is undefined on $\emptyset$, the _empty stack_. In fact, let's give a denotational semantics for the core of Forth.

\begin{align*}
[\![dup]\!]~\sigma::h &\triangleq \sigma::h::h\\
[\![drop]\!]~\sigma::h &\triangleq \sigma\\
[\![swap]\!]~\sigma::a::b &\triangleq \sigma::b::a\\
[\![over]\!]~\sigma::a::b &\triangleq \sigma::a::b::a\\
[\![rot]\!]~\sigma::a::b::c &\triangleq \sigma::b::c::a\\
[\![c_1~c_2]\!]~\sigma &\triangleq [\![c_2]\!]\left([\![c_1]\!]~\sigma\right)
\end{align*}

The denotational semantics exemplifies the concatenative nature of Forth because every command can be seen as a transformation of the stack. Furthermore, command juxtaposition is function composition, which is the crux of the argument.

Fix a set of _stack variables_ $a\in\mathbf{Var}$ such that the set of _assertions_ $\mathbf{Assn}$ is defined as the Kleene closure of the disjoint union of $\mathbf{Var}$ and $E$. Then, let an interpretation $I$ be a partial function from $\mathbf{Var}$ to $E$. We can then define the relation $\sigma\vDash_I P$ read "$\sigma$ satisfies the assertion $P$ under the interpretation $I$".

\begin{align*}
\sigma &\vDash_I \epsilon\\
\sigma::h &\vDash_I P\cdot e&&\text{if}~h = e\land\sigma\vDash_I P\\
\sigma::h &\vDash_I P\cdot a&&\begin{cases} 
    \sigma\vDash_{I[a \mapsto h]} P & I(a)~\text{is undefined}\\
    \sigma\vDash_I P & h=I(a)
  \end{cases}
\end{align*}

We say $\sigma\not{\vDash_I} P$ if and only if $\sigma\vDash_I P$ is undefined.

$$\sigma\vDash_I\{P\}~c~\{Q\}\iff\sigma\vDash_I P\land[\![c]\!]~\sigma=\sigma'\implies\sigma'\vDash_I Q$$

$$\vDash\{P\}~c~\{Q\}\iff\forall\sigma.~\sigma\vDash_\emptyset\{P\}~c~\{Q\}$$

