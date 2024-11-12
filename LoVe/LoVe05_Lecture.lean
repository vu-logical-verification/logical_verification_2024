- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 5: Functional Programming

We take a closer look at the basics of typed functional programming: inductive
types, proofs by induction, recursive functions, pattern matching. -/


set_option autoImplicit false

namespace LoVe


/- ## Inductive Types -/

#print Nat

/- Mottos:

* **No junk**: The type contains no terms beyond those expressible using the
  constructors.

* **No confusion**: Terms built in a different way are different.

For `Nat`:

* "No junk" means that there are no special values, say, `–1` or `ε`, that
  cannot be expressed using a finite combination of `Nat.zero` and `Nat.succ`.

* "No confusion" is what ensures that `Nat.zero` ≠ `Nat.succ n`.

In addition, values of inductive types are always finite.
`Nat.succ (Nat.succ …)` is not a value. -/

inductive RGB : Type
  | red   : RGB
  | green : RGB
  | blue  : RGB

#print RGB

-- no confusion
lemma RGB.green_neq_blue :
  ¬(green = blue) :=
  by intro hgb
     injection hgb

-- no junk
lemma RGB.red_or_green_or_blue :
  ∀ (x : RGB), x = red ∨ x = green ∨ x = blue :=
  by intro x
     induction x with
       | red   => apply Or.inl
                  rfl
       | green => apply Or.inr
                  apply Or.inl
                  rfl
       | blue  => apply Or.inr
                  apply Or.inr
                  rfl

#print RGB.red_or_green_or_blue
#check RGB.rec
#check @RGB.rec (fun x => x = RGB.red ∨ x = RGB.green ∨ x = RGB.blue)

def RGB.swap_green_blue : RGB → RGB
      | red => red
      | green => blue
      | blue => green

#check @RGB.rec (fun _ => RGB) RGB.red RGB.blue RGB.green
#check @RGB.rec (fun _ => RGB) RGB.green RGB.green RGB.green

def RGB.all_green : RGB → RGB
      | red => green
      | green => green
      | blue => green

#print Nat

lemma Nat.succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
    by intro hsn
       induction n with
         | zero => injection hsn
         | succ n' ih_n' =>
           injection hsn with hsn
           exact (ih_n' hsn)

#check Nat.rec
#print Nat.succ_neq_self

#print List

def map {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

lemma map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  by induction xs with
    | nil => rfl
    | cons x xs' ih_xs' => rw [map, ih_xs']

#check List.rec
#print map_ident

lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    map g (map f xs) = map (fun x ↦ g (f x)) xs :=
   sorry

#print List.rec

#print Tree

def mirror {α : Type} : Tree α → Tree α
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node a (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
    by induction t with
         | nil  => rfl
         | node a l r ih_l ih_r => simp [mirror, ih_l, ih_r]

#print mirror_mirror
#check Tree.rec

def fold_left {α : Type} (f : α → α → α) (i : α) : List α → α :=
  sorry

def fold_right {α : Type} (f : α → α → α) : List α → α → α :=
  sorry

#eval fold_left Int.add 0 [1, 2, 3]
#eval fold_right Int.add [1, 2, 3] 0

#eval fold_left Int.sub 0 [1, 2, 3]
#eval fold_right Int.sub [1, 2, 3] 0

def Commutative {α : Type} (f : α → α → α) : Prop :=
  forall x y, f x y = f y x

def Associative {α : Type} (f : α → α → α) : Prop :=
  forall x y z, f x (f y z) = f (f x y) z

lemma fold_left_right_eq {α : Type} (f : α → α → α) :
  Commutative f → Associative f →
  ∀ (i : α) (xs : List α),
    fold_left f i xs = fold_right f xs i :=
  sorry

end LoVe
