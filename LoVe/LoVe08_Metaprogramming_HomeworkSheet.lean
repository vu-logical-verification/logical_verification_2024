/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo


/- # LoVe Homework 8 (10 points + 2 bonus points): Metaprogramming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1 (10 points): A `mindless` Tactic

We develop a tactic that automates some of the mindless `intro`/`apply`
proofs that formed the core of lecture 3.

We proceed in three steps.

1.1 (5 points). Develop a `mindless_safe` tactic that repeatedly tries to invoke
`hypothesis`, invoke `intro _` for `→`/`∀`, and apply the introduction rules
for `∧` and `↔`. The tactic generalizes `intro_and` from the exercise. -/

macro "mindless_safe" : tactic =>
  sorry

theorem abcd (a b c d : Prop) (hc : c) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    mindless_safe
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        hc : c
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        abcd : Prop
        hc : c
        a_1 : a
        a_2 : c
        ⊢ d -/
    repeat sorry

/- 1.2 (5 points). Develop a `mindless_unsafe` tactic that works on the current
goal. For each hypothesis in turn, try the following in a `try`–`catch` block:

1. Apply the hypothesis using `applyTerm`, provided below.

2. Invoke some `followUp` tactic, which is passed as argument.

3. Invoke `done`, which succeeds only if there are no goals left.

4. Return.

If an exception is caught, continue with the next hypothesis.

Once a hypothesis has been found for which steps 1 to 3 succeed,
`mindless_unsafe` succeeds.

Hint: See `prove_direct` in the demo file for an example of a `try`–`catch`
block. -/

def applyTerm (t : Expr) : TacticM Unit :=
  liftMetaTactic (fun goal ↦ MVarId.apply goal t)

def mindlessUnsafe (followUp : TacticM Unit) : TacticM Unit :=
  sorry

/- A few tests follow, using `followUp := hypothesis`. -/

elab "mindless_unsafe_with_hypothesis" : tactic =>
  mindlessUnsafe hypothesis

theorem modus_ponens (a b : Prop) (ha : a) (hab : a → b) :
    b :=
  by mindless_unsafe_with_hypothesis

theorem junky_modus_ponens (a b c d : Prop) (ha : a) (hcb : c → b) (hab : a → b)
    (hdb : d → b) :
    b :=
  by mindless_unsafe_with_hypothesis

/- Finally, everything comes together with the `mindless` tactic below. The
tactic performs a depth-bounded search for a proof, applying `mindless_safe`
and `mindless_unsafe` on all goals in alternation. The bound is necessary to
eventually backtrack. -/

def mindless : ℕ → TacticM Unit
  | 0         =>
    do
      let mindlessSafe ← `(tactic| mindless_safe)
      evalTactic mindlessSafe
  | depth + 1 =>
    do
      let mindlessSafe ← `(tactic| mindless_safe)
      evalTactic mindlessSafe
      let subgoals ← getUnsolvedGoals
      for subgoal in subgoals do
        let assigned ← MVarId.isAssigned subgoal
        if ! assigned then
          setGoals [subgoal]
          try
            mindlessUnsafe (mindless depth)
          catch _ =>
            continue
      pure ()

elab "mindless5" : tactic =>
  mindless 5

/- Some tests are provided below. All should succeed. -/

theorem I (a : Prop) :
    a → a :=
  by mindless5

theorem K (a b : Prop) :
    a → b → b :=
  by mindless5

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by mindless5

theorem proj_1st (a : Prop) :
    a → a → a :=
  by mindless5

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by mindless5

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by mindless5

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b :=
  by mindless5

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  by mindless5

theorem more_nonsense (a b c : Prop) :
    (c → (a → b) → a) → c → b → a :=
  by mindless5

theorem even_more_nonsense (a b c : Prop) :
    (a → a → b) → (b → c) → a → b → c :=
  by mindless5

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b :=
  by mindless5

theorem weak_peirce_on_steroids (a b : Prop) :
    ((((((((a → b) → a) → a) → b) → b) → a) → a) → b) → b :=
  by mindless5

theorem one_for_the_road (a c : Prop) (ha : a) (hccc : c → c → c)
      (hac : a → c) :
    c :=
  by mindless5


/- ## Question 2 (2 bonus points): An `aesop`-Like Tactic

2.1 (1 bonus point). Develop a simple `aesop`-like tactic.

This tactic should apply all safe introduction and elimination rules. In
addition, it should try potentially unsafe rules (such as `Or.inl` and
`False.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also try to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

Hint: The `MonadBacktrack` monad class might be useful.

2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise and
homework 3. Please include these below. -/

end LoVe
