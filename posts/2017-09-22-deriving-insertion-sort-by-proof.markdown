---
title: Deriving insertion sort by proof
---

If you've taken an introduction to computer science course, you've probably seen all of the major sorting algorithms, including insertion sort. You've also probably seen its proof of correctness which goes into loop invariants and all that.

However, I was always confused by their presenting the algorithm first and then the proof of correctness, because it seems like the intuition behind the algorithm is inseparable with the reason why it's correct. To a constructivist like me, they should literally be the same object. That is, we find a proof that for any list, there exists a sorted one, and the computational content of that proof is precisely insertion sort. For more information on this identification of proofs as programs, check out my older post [here](http://ssomayyajula.github.io/posts/2016-12-25-constructivism-automated-deduction-and-you.html).

That's why in this post, we're going to go through a purely proof-based presentation of lists and their properties with [Lean](http://leanprover.github.io/), Microsoft Research's new theorem prover. This will lead to a formally verified implementation of insertion sort. This post assumes the reader has _some_ experience with functional programming, automated proofs, and their interactions (propositions-as-types/proofs-as-programs, proof tactics, etc.).

Before we dive head first into Lean, let's take a step back and figure out what we need to specify "for any list, there exists a sorted one." At first glance, it seems like we only need a way of asserting that a list is sorted. However, that's not strong enough---what if our algorithm returns any old sorted list, that may or may not have the same elements as the original? That's why we also need a way of saying "the sorted list has the same elements as the original." Let's go ahead and specify that first.

We drop into Lean's namespace for lists and fix ourselves a universe and type for elements.

```lean
namespace list

universe u
variable {α : Type u}
```

Since the Lean standard library has a subset relation over lists, we can just say two lists have the same elements iff they're subsets (sublists?) of each other.

```lean
protected def equiv (l₁ l₂ : list α) := l₁ ⊆ l₂ ∧ l₂ ⊆ l₁
infix ` ≃ `:50 := list.equiv
```

Naturally, "having the same elements" is an equivalence relation, whose proof we derive from the fact that the subset relation is a partial order.

```lean
@[refl, simp] lemma equiv.refl (l : list α) : l ≃ l :=
⟨by simp, by simp⟩

@[symm] lemma equiv.symm {l₁ l₂ : list α} : l₁ ≃ l₂ → l₂ ≃ l₁ :=
and.symm

@[trans] lemma equiv.trans {l₁ l₂ l₃ : list α} : l₁ ≃ l₂ → l₂ ≃ l₃ → l₁ ≃ l₃
| ⟨x, y⟩ ⟨z, w⟩ := ⟨subset.trans x z, subset.trans w y⟩
```

Tagging each lemma with attributes will help the simplify tactic and us when we do proofs by equational reasoning later on. Now, we're ready to define what it means for a list to be sorted---it is simply a proposition saying that given $[x_1,\ldots,x_n]$, $x_1\leq x_2\leq\ldots\leq x_n$. We proceed by induction on a list, with `nil` and singletons being trivially sorted.

```lean
def sorted [has_le α] : list α → Prop
| (a :: b :: t) := a ≤ b ∧ sorted (b :: t)
| _             := true
```

Now let's see if we can prove our original claim by induction given a decidable linear order i.e. a comparator, using subtypes to represent existentials.

```lean
def insertion_sort [decidable_linear_order α] (l₁ : list α) :
  {l₂ // l₁ ≃ l₂ ∧ sorted l₂} :=
begin
  induction l₁ with h t₁ ih,
    existsi nil, simp,
    cases ih with t₂ ih, cases ih with e s,
    ...
```

Producing a sorted version of `nil` is trivial, as the simplifier fills in the obligations for equivalence and sortedness. However, we get stuck on the inductive step. Given a sorted version of the tail $t_1$ called $t_2$, how can we produce a sorted version of the entire list, that is, including the head $h$? We can't just `cons` it on, after all. Different proofs---and therefore algorithms---can do different things, but this is where we specialize to insertion sort. We just need to find a way of inserting the head into the tail while preserving sortedness and all the old elements. Formally, we express this as follows.

```lean
def insert_le [decidable_linear_order α] (a : α) (l₁) :
  sorted l₁ → {l₂ // a :: l₁ ≃ l₂ ∧ sorted l₂} :=
begin
  intro s₁,
  induction l₁ with h t₁ ih,
    existsi ([a]), simp,
    ...
```

Here, $a$ is the element to be inserted. Note that the proposition $a :: l_1\simeq l_2$ is a compact way of saying "the output is equivalent to the input, but it includes `a`," as desired. Now, onto the proof---the base case, inserting $a$ into `nil`, is trivial due to the simplify tactic. The hard part again is the inductive step. However, since we have a decidable linear order, we can decide whether $a\leq h$ or $h\leq a$.
```lean
    ...
    by_cases a ≤ h with hleq,
      existsi a :: h :: t₁, exact ⟨by refl, hleq, s₁⟩,
      ...
```

If the former holds, then the proof becomes quite easy: we can just cons the element onto the head $h$ and tail $t_1$ and we immediately have $a::h::t_1\simeq a::h::t_1$ and $a\leq h\leq^* t_1$. The hard (and recursive) part is when the latter is true. We appeal to the inductive hypothesis $ih$ to insert $a$ somewhere in $t_1$ along with evidence that the result is in fact sorted and that all the old elements are still in place. However, $ih$ naturally expects $t_1$ to be sorted, so we somehow have to extract this information from the fact that $h::t_1$ is sorted.

```lean
lemma sorted_tl [has_le α] {h : α} {t} : sorted (h :: t) → sorted t :=
λ s, by {cases t, trivial, exact s.right}
```

Now we may continue.

```lean
      ...
      cases ih (sorted_tl s₁) with t₂ p, cases p with e s₂,
      existsi h :: t₂, apply and.intro,
      ...
```

Essentially, we insert $a$ somewhere in the tail and return it with the head stuck back on. Sounds a bit gruesome, but computer science was never easy. Now, we have two proof obligations: $a :: h :: t₁\simeq h :: t₂$ and that $h::t_2$ is sorted. The latter makes sense to prove, but the former is a bit weird: since $a\in t_2$, we are expressing the fact that $t_1$ and $t_2$ have the same elements modulo $a$. We can largely "ignore" $h$ since it appears on both sides of the equation. To attack the first, we need three lemmas.

```lean
lemma cons_equiv_cons {l₁ l₂} (a : α) : l₁ ≃ l₂ → a :: l₁ ≃ a :: l₂
| ⟨x, y⟩ := ⟨cons_subset_cons a x, cons_subset_cons a y⟩

lemma cons_subset_comm {a b : α} {l₁ l₂} :
  l₁ ⊆ l₂ → a :: b :: l₁ ⊆ b :: a :: l₂ :=
λ h _ m, match m with
| or.inl is_a           := or.inr (or.inl is_a)
| or.inr (or.inl is_b)  := or.inl is_b
| or.inr (or.inr in_l₁) := or.inr (or.inr (h in_l₁))
end

lemma cons_equiv_comm {a b : α} {l₁ l₂} :
  l₁ ≃ l₂ → a :: b :: l₁ ≃ b :: a :: l₂
| ⟨x, y⟩ := ⟨cons_subset_comm x, cons_subset_comm y⟩
```

These each capture the behavior of "having the same elements;" in particular, the relation is invariant under `cons`ing arbitrary elements and permutation. Now, we can proceed by a _calculational proof_ i.e. equational reasoning.

```lean
      ...
      calc
        a :: h :: t₁ ≃ h :: a :: t₁ : cons_equiv_comm (by refl)
                 ... ≃ h :: t₂      : cons_equiv_cons h e,
      ...
```

$ih$ actually tells us that $a::t_1\simeq t_2$ since it took care of insertion, so it is up to us to permute the elements $a$ and $h$ and reduce it to its component witnessing that fact, called $e$. Now, we can attack the latter obligation, which took me a while to think about. The difficulty is: we do not have a direct way of expressing $h::t_1$ is sorted, since the definition of $sorted$ pattern matches on at least two `cons`ed elements. Intuitively though, we know $h::t$ is sorted if $t$ is sorted and $h$ is the least element of $h::t$, so let's go ahead and prove that.

```lean
lemma sorted_cons [has_le α] {h : α} {t} :
  sorted t → (∀ {a}, a ∈ t → h ≤ a) → sorted (h :: t) :=
begin
  intros _ f,
  cases t,
    trivial,
    apply and.intro,
    exact f (or.inl (by refl)),
    assumption
end
```

I like how simple this proof turned out: if the tail is `nil`, then it's trivially sorted, or else $t\equiv h'::t'$ and we have to show $h\leq h'$ and that $t$ is sorted. The latter we know by assumption, and the former we know from the fact that $h$ is the least element of $h::t$. We have one last lemma to prove, which is almost the converse of the above; that is, if $h::t$ is sorted, then $h$ is its least element.

```lean
lemma sorted_least_elem [weak_order α] {h : α} {t} :
  sorted (h :: t) → ∀ {a}, a ∈ t → h ≤ a :=
begin
  intros s _ m,
  induction t with h' t' ih generalizing h,
    exact absurd m (not_mem_nil a),
    cases m with is_h' in_t',
      rw is_h', exact s.left,
      exact le_trans s.left (ih in_t' s.right)
end
```

This directly follows from the transitivity of a weak order (whose existence is implied by a decidable linear order). Now, we're ready to finish `insert_le.`

```lean
      ...
      exact sorted_cons s₂ (λ _ m,
      match e.right m with
      | or.inl is_a  := by {rw is_a, exact le_of_not_le hleq}
      | or.inr in_t₁ := sorted_least_elem s₁ in_t₁
      end)
end
```

There's a lot to unpack here; recall we're in the $\lnot(a\leq h)$ branch of the proof. In order to show that $h::t_2$ is sorted, we had to show that $t_2$ is sorted and that $h$ is its least element. The former we know by $ih$, the latter took some work: we have to show for any $x\in t_2$, $h\leq x$. However, notice that we know $a::t_1\simeq t_2$. Thus, it is sufficient to show $h\leq^*a :: t_1$, which is not hard! If $x=a$, then we have $h\leq x$, since $\lnot(a\leq h)\implies h\leq a$. Otherwise $x\in t_1$; we know $h::t_1$ by assumption, so we take advantage of the fact that $h$ is the least element of $t_1$, so clearly $h\leq x$. Now let's finally finish insertion sort!

```lean
    ...
    cases (insert_le h t₂ s) with l₂ pf, cases pf with _ _,
    existsi l₂, apply and.intro,
    calc
      h :: t₁ ≃ h :: t₂ : cons_equiv_cons h e
          ... ≃ l₂      : by assumption,
    assumption
end

end list
```

As we figured out a few paragraphs ago, we just insert the head somewhere in the sorted tail, and we automatically get the sortedness guarantee. However, we also had to do a little calculational proof showing that `insert_le` didn't drop or add any extraneous elements except for $h$. Let's go ahead and run this proof! Or program, because they're one and the same.

```lean
#eval list.insertion_sort [91, 60, 41, 65, 66, 84, 85, 82, 95, 83,
                           38,  4, 65, 34, 36, 89, 42, 86,  9, 25]
```

Running Lean in VS Code will give the following message as output, and quite quickly too! The best part though, is that we know for sure that the output is correct.

```
[4, 9, 25, 34, 36, 38, 41, 42, 60, 65, 65, 66, 82, 83, 84, 85, 86, 89, 91, 95]
```

To close, verified software engineering is the _future_™ (if my last three posts didn't make that clear), and the breadth of sophisticated tools like Lean has been crucial in making this new workflow a lot less painful.

The source code for this post is available [here](https://gist.github.com/ssomayyajula/dae03a58842c92ac0173702a5d1efad4).

_P.S.: After hopping between Coq & Agda, Lean has been really fun to use. Plus, I'd be remiss if I didn't mention the fantastic folks over at the [Lean user group](https://groups.google.com/forum/#!forum/lean-user) who helped me out with this post!_
