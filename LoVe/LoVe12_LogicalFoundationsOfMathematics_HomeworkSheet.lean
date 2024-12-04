/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 12 (10 points):
# Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (10 points): Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `List α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `List.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `BEq` (Boolean equality) type class. For this reason, the definitions and
theorems below all take `[BEq α]` as type class argument.

1.1 (2 points). Provide the missing proof below. -/

instance Multiset.Setoid (α : Type) [BEq α] : Setoid (List α) :=
{ r     := fun as bs ↦ ∀x, List.count x as = List.count x bs
  iseqv :=
    { refl  :=
        sorry
      symm  :=
        sorry
      trans :=
        sorry
    } }

/- 1.2 (1 point). Define the type of multisets as the quotient over the
relation `Multiset.Setoid`. -/

def Multiset (α : Type) [BEq α] : Type :=
  sorry

/- 1.3 (3 points). Now we have a type `Multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the multiplicities
of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def Multiset.mk {α : Type} [BEq α] : List α → Multiset α :=
  Quotient.mk (Multiset.Setoid α)

def Multiset.empty {α : Type} [BEq α] : Multiset α :=
  sorry

def Multiset.singleton {α : Type} [BEq α] (a : α) : Multiset α :=
  sorry

def Multiset.union {α : Type} [BEq α] : Multiset α → Multiset α → Multiset α :=
  Quotient.lift₂
  sorry
  sorry

/- 1.4 (4 points). Prove that `Multiset.union` is commutative and associative
and has `Multiset.empty` as identity element. -/

theorem Multiset.union_comm {α : Type} [BEq α] (A B : Multiset α) :
    Multiset.union A B = Multiset.union B A :=
  sorry

theorem Multiset.union_assoc {α : Type} [BEq α] (A B C : Multiset α) :
    Multiset.union (Multiset.union A B) C =
    Multiset.union A (Multiset.union B C) :=
  sorry

theorem Multiset.union_iden_left {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union Multiset.empty A = A :=
  sorry

theorem Multiset.union_iden_right {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union A Multiset.empty = A :=
  sorry

end LoVe
