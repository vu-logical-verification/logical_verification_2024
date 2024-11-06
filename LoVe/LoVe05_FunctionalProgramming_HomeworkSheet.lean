/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Homework 5 (10 points + 2 bonus points): Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Reverse of a List

Recall the `reverse` operation from lecture 2 and the `reverse_append` and
`reverse_reverse` theorems from the demo of lecture 4. -/

#check reverse
#check reverse_append
#check reverse_append_tactical
#check reverse_reverse

/- 1.1 (3 points). Prove `reverse_append` again, this time using the
calculational style for the induction step. -/

theorem reverse_append_calc {α : Type} :
    ∀xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys =>
    sorry

/- 1.2 (3 points). Prove the induction step in the proof below using the
calculational style, following this proof sketch:

      reverse (reverse (x :: xs))
    =     { by definition of `reverse` }
      reverse (reverse xs ++ [x])
    =     { using the theorem `reverse_append` }
      reverse [x] ++ reverse (reverse xs)
    =     { by the induction hypothesis }
      reverse [x] ++ xs
    =     { by definition of `++` and `reverse` }
      [x] ++ xs
    =     { by computation }
      x :: xs -/

theorem reverse_reverse_calc {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    sorry


/- ## Question 2 (4 points + 2 bonus points): Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 2.1 (2 points). Prove the following theorem, discovered by Carl Friedrich
Gauss as a pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic introduced in lecture 6 might be useful to reason about
  addition. -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1) :=
  sorry

/- 2.2 (2 points). Prove the following property of `sumUpToOfFun`. -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n :=
  sorry

/- 2.3 (2 bonus points). Prove `sumUpToOfFun_mul` again as a "paper" proof.
Follow the guidelines given in question 1.4 of the exercise. -/

-- enter your paper proof here

end LoVe
