/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe Homework 11 (10 points + 2 bonus points): Denotational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (7 points): Denotational Semantics of DOWHILE -/

namespace DOWHILE

/- Consider the following DOWHILE language: -/

inductive Stmt : Type
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : Stmt → (State → Prop) → Stmt
  | whileDo  : (State → Prop) → Stmt → Stmt
  | doWhile  : Stmt → (State → Prop) → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, `seq`, and `while`–`do` constructs are as for the
WHILE language.

`unless S do B` executes `S` if `B` is false in the current state; otherwise, it
does nothing. This statement is inspired by Perl's `unless` conditional.

`do S while B` first executes `S`. Then, if `B` is true in the resulting state,
it re-enters the loop and executes `S` again, and continues executing `S` until
`B` becomes false. The semantics is almost the same as `while B S`, except that
`S` is always executed at least once, even if the condition is not true
initially. This statement is inspired by C's and Java's `do { … } while (…)`
statement.

1.1 (2 points). Give a denotational semantics of DOWHILE.

Hint: Your definition should make it easy to prove the theorem `doWhile_whileDo`
in question 1.2. -/

def denote : Stmt → Set (State × State)
  | Stmt.skip         => Id
-- enter the missing cases here

notation (priority := high) "⟦" S "⟧" => denote S

/- 1.2 (1 point). Prove the following correspondence between the two types of
loops. -/

theorem doWhile_whileDo (S : Stmt) (B : State → Prop) :
    ⟦Stmt.doWhile S B⟧ = ⟦S⟧ ◯ ⟦Stmt.whileDo B S⟧ :=
  sorry

/- 1.3 (4 points). Prove the following theorems.

Hint: For all of these, short proofs are possible. It may help, however, to
know what basic expressions such as `P ⇃ (fun x ↦ False)` and
`P ⇃ (fun x ↦ True)` mean. Make sure to simplify the expressions involving
`⇃` before trying to figure out what to do about `lfp`. -/

theorem lfp_const {α : Type} [CompleteLattice α] (a : α) :
    lfp (fun X ↦ a) = a :=
  sorry

theorem whileDo_False (S : Stmt) :
    ⟦Stmt.whileDo (fun _ ↦ False) S⟧ = Id :=
  sorry

theorem comp_Id {α : Type} (r : Set (α × α)) :
    r ◯ Id = r :=
  sorry

theorem DoWhile_False (S : Stmt) :
    ⟦Stmt.doWhile S (fun _ ↦ False)⟧ = ⟦S⟧ :=
  sorry

end DOWHILE


/- ## Question 2 (3 points + 2 bonus points): Kleene's Theorem

We can compute the fixpoint by iteration by taking the union of all finite
iterations of `f`:

    `lfp f = ⋃i, (f ^^ i) ∅`

where

    `f ^^ i = f ∘ ⋯ ∘ f`

iterates the function `f` `i` times. However, the above characterization of
`lfp` only holds for continuous functions, a concept we will introduce below. -/

def iter {α : Type} (f : α → α) : ℕ → α → α
  | 0,     a => a
  | n + 1, a => f (iter f n a)

notation f "^^" n => iter f n

/- 2.1 (3 points). Fill in the missing proofs below.

Hint: Bear in mind that `≤` works on lattices in general, including sets. On
sets, it can be unfolded to `⊆` using `simp [LE.le]`. Moreover, when you see
`h : A ⊆ B` in a goal, you can imagine that you have `?a ∈ A → ?a ∈ B` by
definition, or unfold the definition using
`simp [HasSubset.Subset, Set.Subset]`. -/

def Union {α : Type} (s : ℕ → Set α) : Set α :=
  {a | ∃n, a ∈ s n}

theorem Union_le {α : Type} {s : ℕ → Set α} (A : Set α) (h : ∀i, s i ≤ A) :
    Union s ≤ A :=
  by
    simp [LE.le]
    simp [HasSubset.Subset, Set.Subset]
    sorry

/- A continuous function `f` is a function that commutes with the union of any
monotone sequence `s`: -/

def Continuous {α : Type} (f : Set α → Set α) : Prop :=
  ∀s : ℕ → Set α, Monotone s → f (Union s) = Union (fun i ↦ f (s i))

/- We need to prove that each continuous function is monotone. To achieve this,
we will need the following sequence: -/

def biSeq {α : Type} (A B : Set α) : ℕ → Set α
  | 0     => A
  | n + 1 => B

/- For example, `biSeq A B` is the sequence A, B, B, B, …. -/

theorem Monotone_biSeq {α : Type} (A B : Set α) (h : A ≤ B) :
    Monotone (biSeq A B) :=
  by
    simp [Monotone]
    intro i j hle a ha
    cases i with
    | zero =>
      cases j with
      | zero =>
        simp [biSeq] at *
        assumption
      | succ j' =>
        simp [biSeq] at *
        apply h
        assumption
    | succ i' =>
      cases j with
      | zero    => simp [biSeq] at *
      | succ j' =>
        simp [biSeq] at *
        assumption

theorem Union_biSeq {α : Type} (A B : Set α) (ha : A ≤ B) :
    Union (biSeq A B) = B :=
  by
    apply le_antisymm
    { sorry }
    { sorry }

theorem Monotone_of_Continuous {α : Type} (f : Set α → Set α)
      (hf : Continuous f) :
    Monotone f :=
  by
    intro A B ha
    rw [← Union_biSeq A B ha]
    rw [hf _ (Monotone_biSeq A B ha)]
    sorry

/- 2.2 (1 bonus point). Provide the following proof, using a similar case
distinction as for `Monotone_biSeq` above. -/

theorem Monotone_iterate {α : Type} (f : Set α → Set α) (hf : Monotone f) :
    Monotone (fun i ↦ (f ^^ i) ∅) :=
  sorry

/- 2.3 (1 bonus point). Prove the main theorem. A proof sketch is given below.

You can use the theorem `le_antisymm` to break the proof into two proofs of
inclusion.

Case 1. `lfp f ≤ Union (fun i ↦ (f ^^ i) ∅)`: The key is to use the theorem
`lfp_le` together with continuity of `f`.

Case 2. `Union (fun i ↦ (f ^^ i) ∅) ≤ lfp f`: The theorem `Union_le` gives a
natural number `i` on which you can perform induction. You also need the theorem
`lfp_eq` to unfold one iteration of `lfp f`. -/

theorem lfp_Kleene {α : Type} (f : Set α → Set α) (hf : Continuous f) :
    lfp f = Union (fun i ↦ (f ^^ i) ∅) :=
  sorry

end LoVe
