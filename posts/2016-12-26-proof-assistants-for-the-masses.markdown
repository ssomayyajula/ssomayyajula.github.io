---
title: Proof assistants for the masses
---

[Chirag Bharadwaj](http://www.chiragbharadwaj.com/) and I are announcing the availibility of [`refined logic`](https://github.com/ssomayyajula/refined-logic), a framework for implementing proof assistants for refinement logics. If you're unclear on what any of these words mean, read the [paper](/files/impl_constr_logic_final_paper.pdf) that we wrote as a part of our final project for [CS 4860](http://www.cs.cornell.edu/courses/CS4860). It details the implementation of this framework as well as the general implementation of constructive logics in OCaml.

Our intention is to provide a plug-and-play solution for students---instead of having to build a proof assistant from scratch, they may simply provide the rules of their proof calculus and compile directly to an executable. This of course allows them to focus on the educational content of their work rather than the code boilerplate. We provide an implementation of the propositional refinement calculus as an example and demonstrate program extraction in OCaml.