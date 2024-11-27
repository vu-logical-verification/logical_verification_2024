/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Homework 10 (10 points + 1 bonus point): Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Program Verification

The following WHILE program is intended to compute 2 to the power of `N`,
leaving the result in `r`. -/

def POWER_OF_TWO (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 1);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "r" (fun s ↦ s "r" * 2);
     Stmt.assign "n" (fun s ↦ s "n" + 1))

/- 1.1 (1 point). Define a recursive function that computes 2 to the power of
`n`. -/

def twoToTheNth : ℕ → ℕ :=
  sorry

/- Remember to test your function. Otherwise, you will have big difficulties
answering question 2.2 below. -/

#eval twoToTheNth 0   -- expected: 1
#eval twoToTheNth 1   -- expected: 2
#eval twoToTheNth 2   -- expected: 4
#eval twoToTheNth 3   -- expected: 8
#eval twoToTheNth 8   -- expected: 256

/- Let us register `twoToTheNth`'s recursive equations as simplification rules
to strengthen the simplifier and `aesop`, using some new Lean syntax: -/

attribute [simp] twoToTheNth

/- 1.2 (5 points). Prove the correctness of `POWER_OF_TWO` using `vcg`. -/

theorem POWER_OF_TWO_correct (N : ℕ) :
    {* fun s ↦ True *}
    (POWER_OF_TWO N)
    {* fun s ↦ s "r" = twoToTheNth N *} :=
  sorry


/- ## Question 2 (4 points + 1 bonus point): Hoare Logic for LOOP

We introduce the LOOP language: -/

namespace LOOP

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ifThen : (State → Prop) → Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The language is similar to WHILE. There are three differences:

* There is no `skip` statement.

* The `ifThen` statement is an `if`–`then` construct with no `else` branch.

* The `loop` construct corresponds to a randomized `while` loop. It executes the
  body an unspecified (possibly infinite) number of times.

The big-step semantics for LOOP is defined below. -/

inductive BigStep : Stmt × State → State → Prop
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hs : BigStep (S, s) t) (ht : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S s t) (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThen B S, s) t
  | if_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.ifThen B S, s) s
  | loop_continue (S s t u) (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.loop S, t) u) :
    BigStep (Stmt.loop S, s) u
  | loop_exit (S s) :
    BigStep (Stmt.loop S, s) s

infix:110 " ⟹ " => BigStep

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro (priority := high) "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" :
  term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

/- 2.1 (1 point). Prove the consequence rule. -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
      (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  sorry

/- 2.2 (1 point). Prove the rule for `assign`. -/

theorem assign_intro {P x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  sorry

/- 2.3 (1 point). Prove the rule for `seq`. -/

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
      (hT : {* Q *} (T) {* R *}) :
    {* P *} (Stmt.seq S T) {* R *} :=
  sorry

/- 2.4 (1 point). Prove the rule for `if`–`then`. -/

theorem if_intro {b P Q S}
      (htrue : {* fun s ↦ P s ∧ b s *} (S) {* Q *})
      (hfalse : ∀s, P s ∧ ¬ b s → Q s) :
    {* P *} (Stmt.ifThen b S) {* Q *} :=
  sorry

/- 2.5 (1 bonus point). Prove the rule for `loop`. Notice the similarity with
the rule for `while` in the WHILE language. -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
    {* P *} (Stmt.loop S) {* P *} :=
  sorry

end PartialHoare

end LOOP

end LoVe
