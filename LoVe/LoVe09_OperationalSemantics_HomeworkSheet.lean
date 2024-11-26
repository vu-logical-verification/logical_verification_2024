/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 9 (10 points + 1 bonus point): Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (7 points + 1 bonus point): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive Stmt : Type
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`.

1.1 (2 points). Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop
  | skip (s) :
    BigStep (Stmt.skip, s) s
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- 1.2 (2 points). Complete the following definition of a small-step
semantics: -/

inductive SmallStep : Stmt × State → Stmt × State → Prop
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
-- enter the missing cases here

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

/- 1.3 (3 points). We will now attempt to prove termination of the REPEAT
language. More precisely, we will show that there cannot be infinite chains of
the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : Stmt → ℕ
  | Stmt.skip         => 0
-- enter the missing cases here

/- You can validate your answer as follows. Consider the following program
`S₀`: -/

def incr (x : String) : Stmt :=
  Stmt.assign x (fun s ↦ s x + 1)

def S₀ : Stmt :=
  Stmt.repeat 1 (incr "m"; incr "n")

/- Check that `mess` strictly decreases with each step of its small-step
evaluation: -/

def S₁ : Stmt :=
  (incr "m"; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₂ : Stmt :=
  (Stmt.skip; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₃ : Stmt :=
  incr "n"; Stmt.repeat 0 (incr "m"; incr "n")

def S₄ : Stmt :=
  Stmt.skip; Stmt.repeat 0 (incr "m"; incr "n")

def S₅ : Stmt :=
  Stmt.repeat 0 (incr "m"; incr "n")

def S₆ : Stmt :=
  Stmt.skip

#eval mess S₀   -- result: e.g., 6
#eval mess S₁   -- result: e.g., 5
#eval mess S₂   -- result: e.g., 4
#eval mess S₃   -- result: e.g., 3
#eval mess S₄   -- result: e.g., 2
#eval mess S₅   -- result: e.g., 1
#eval mess S₆   -- result: e.g., 0

/- 1.4 (1 bonus point). Prove that the measure decreases with each small-step
transition. If necessary, revise your answer to question 1.3. -/

theorem SmallStep_mess_decreases {Ss Tt : Stmt × State} (h : Ss ⇒ Tt) :
    mess (Prod.fst Ss) > mess (Prod.fst Tt) :=
  sorry


/- ## Question 2 (3 points): Inversion Rules

2.1 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

theorem BigStep_ite_iff {B S s t} :
    (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) :=
  sorry

/- 2.2 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

theorem BigStep_repeat_iff {n S s u} :
    (Stmt.repeat n S, s) ⟹ u ↔
    (n = 0 ∧ u = s)
    ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) :=
  sorry

end LoVe
