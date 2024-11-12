/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6 (10 points): Inductive Predicates

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

end LoVe
