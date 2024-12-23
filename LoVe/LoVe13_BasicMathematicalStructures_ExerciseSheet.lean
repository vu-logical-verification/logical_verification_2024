/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe Exercise 13: Basic Mathematical Structures

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Type Classes

Recall the inductive type `Tree` we introduced in lecture 5: -/

#check Tree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def Tree.graft {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u =>
    Tree.node a (Tree.graft l u) (Tree.graft r u)

#reduce Tree.graft (Tree.node 1 Tree.nil Tree.nil)
  (Tree.node 2 Tree.nil Tree.nil)

/- 1.1. Prove the following two theorems by structural induction on `t`. -/

theorem Tree.graft_assoc {α : Type} (t u v : Tree α) :
    Tree.graft (Tree.graft t u) v = Tree.graft t (Tree.graft u v) :=
  sorry

theorem Tree.graft_nil {α : Type} (t : Tree α) :
    Tree.graft t Tree.nil = t :=
  sorry

/- 1.2. Declare `Tree` an instance of `AddMonoid` using `graft` as the
addition operator. -/

#print AddMonoid

instance Tree.Add {α} : Add (Tree α) where
  add := sorry

instance Tree.Zero {α} : Zero (Tree α) where
  zero := sorry

instance Tree.AddMonoid {α : Type} : AddMonoid (Tree α) :=
  {
    add_assoc :=
      sorry
    add_zero  :=
      sorry
    zero_add  :=
      sorry
    nsmul := nsmulRec
  }

/- 1.3 (**optional**). Explain why `Tree` with `graft` as addition cannot be
declared an instance of `AddGroup`. -/

#print AddGroup

-- enter your explanation here

/- 1.4 (**optional**). Prove the following theorem illustrating why `Tree`
with `graft` as addition does not constitute an `AddGroup`. -/

theorem Tree.add_left_neg_counterexample :
    ∃x : Tree ℕ, ∀y : Tree ℕ, Tree.graft y x ≠ Tree.nil :=
  sorry

end LoVe
