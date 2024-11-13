/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6 (20 points): Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): A Type of Terms

Recall the type of terms from question 3 of exercise 5: -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1 (2 points). Define an inductive predicate `IsApp` that returns `True` if
its argument is of the form `Term.app …` and that returns `False` otherwise. -/

-- enter your definition here

/- 1.2 (2 points). Define an inductive predicate `IsLamFree` that is true if
and only if its argument is a term that contains no λ-expressions. -/

-- enter your definition here


/- ## Question 2 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `Even`,
and should not rely on `Even`. -/

inductive Odd : ℕ → Prop
-- supply the missing cases here

/- 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

theorem Odd_3 :
    Odd 3 :=
  sorry

theorem Odd_5 :
    Odd 5 :=
  sorry

/- 2.3 (1 point). Prove the following theorem by rule induction: -/

theorem Even_Odd {n : ℕ} (heven : Even n) :
    Odd (n + 1) :=
  sorry

/- 2.4 (2 points). Prove the same theorem again, this time as a "paper" proof.
This is a good exercise to develop a deeper understanding of how rule induction
works.

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the induction hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key theorems they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

-- enter your paper proof here

/- 2.5 (1 point). Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → false`. -/

theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
    ¬ Odd n :=
  sorry

/- ## Question 3 (4 points): Reflexive Transitive Closure^2 -/

/- Consider the following inductive definition of the
   reflexive transitive closure of a relation `R`,
   modeled as a binary predicate `Star R`. -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | base (a : α)    : Star R a a
  | ind (a b c : α) : R a b → Star R b c → Star R a c

/- We proved the following two properties in the lecture: -/

lemma Star.closure {α : Type} (R : α → α → Prop) (a b : α) :
    R a b → Star R a b :=
    by intro hab
       apply Star.ind a b b
       { exact hab }
       { exact Star.base b}

lemma Star.transitive {α : Type} (R : α → α → Prop) (a b c : α) :
    Star R a b → Star R b c → Star R a c :=
  by intros hab
     revert c
     induction hab with
       | base a =>
         intro c hac
         exact hac
       | ind a b c hab hbc ih_hbc =>
         intro d hcd
         apply Star.ind a b d
         { exact hab }
         { apply ih_hbc d
           exact hcd }

/- Prove that `Star (Star R)` is the same relation as `Star R`.
   You may use the above two lemmas. -/

lemma Star.Star_Iff_Star {α : Type} (R : α → α → Prop) (a b : α) :
    Star (Star R) a b ↔ Star R a b :=
  sorry

/- ## Question 3 (6 points): Sets -/

/- One approach to implementing sets that are extensional
   (that is, two sets are equal iff they have the same elements)
   in proof assistants is to maintain a strict order on the elements. -/

inductive Comparison : Type
  | lt : Comparison
  | eq : Comparison
  | gt : Comparison

open Comparison

/- We will be working with sets of natural numbers. -/

def compare_ℕ : ℕ → ℕ → Comparison
  | Nat.zero, Nat.zero => eq
  | Nat.zero, Nat.succ _ => lt
  | Nat.succ _, Nat.zero => gt
  | Nat.succ a, Nat.succ b => compare_ℕ a b

/- An `Option α` type has either the form `some a` for a value of type α or
   it has the form `none`. -/

def compare : Option ℕ → Option ℕ → Comparison
  | none, none => eq
  | none, some _ => gt
  | some _, none => lt
  | some a, some b => compare_ℕ a b

/- A term of type `SetAbove (some a)` type is a set whose smallest element is `a`;
   a term of type `SetAbove none` is the empty set. -/

inductive SetAbove : Option ℕ → Type
  | none : SetAbove none
  | some (a : ℕ) (k : Option ℕ) :
      compare (some a) k = lt → SetAbove k → SetAbove (some a)

/- Complete the definition of an empty set. -/
def empty : SetAbove none :=
  sorry

/- Complete the definition of a singleton set. -/
def singleton (a : ℕ) : SetAbove (some a) :=
  sorry

/- Complete the definition of a membership predicate. -/
def mem (a : ℕ) (k : Option ℕ) : SetAbove k → Bool :=
  sorry

/- An element smaller than the smallest element of the set
   can (unsurprisingly) never belong to the set. -/
lemma mem_lt_key_false (a : Nat) (k : Option Nat) (m : SetAbove k) :
  compare (some a) k = lt →
  mem a k m = false :=
  sorry

end LoVe
