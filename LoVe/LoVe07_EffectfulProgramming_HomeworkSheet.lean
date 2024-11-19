/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe Homework 7 (10 points + 1 bonus point): Monads

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Better Exceptions

The __error monad__ stores either a value of type `α` or an error of type `ε`.
This corresponds to the following type: -/

inductive Error (ε α : Type) : Type
  | good : α → Error ε α
  | bad  : ε → Error ε α

/- The error monad generalizes the option monad seen in the lecture. The
`Error.good` constructor, corresponding to `Option.some`, stores the current
result of the computation. But instead of having a single bad state
`Option.none`, the error monad has many bad states of the form `Error.bad e`,
where `e` is an "exception" of type `ε`.

1.1 (1 point). Complete the definitions of the `pure` and `bind` operations on
the error monad: -/

def Error.pure {ε α : Type} : α → Error ε α :=
  sorry

def Error.bind {ε α β : Type} : Error ε α → (α → Error ε β) → Error ε β :=
  sorry

/- The following type class instance makes it possible to use `pure`, `>>=`,
and `do` notations in conjunction with error monads: -/

instance Error.Pure {ε : Type} : Pure (Error ε) :=
  { pure := Error.pure }

instance Error.Bind {ε : Type} : Bind (Error ε) :=
  { bind := Error.bind }

/- 1.2 (3 points). Prove the three laws for the error monad. -/

theorem Error.pure_bind {ε α β : Type} (a : α) (f : α → Error ε β) :
    (pure a >>= f) = f a :=
  sorry

theorem Error.bind_pure {ε α : Type} (ma : Error ε α) :
    (ma >>= pure) = ma :=
  sorry

theorem Error.bind_assoc {ε α β γ : Type} (f : α → Error ε β)
      (g : β → Error ε γ) (ma : Error ε α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g)) :=
  sorry

/- 1.3 (2 points). Define the following two operations on the error monad.

* The `throw` operation raises an exception `e`, leaving the monad in a bad
  state storing `e`.

* The `catch` operation can be used to recover from an earlier exception. If the
  monad is currently in a bad state storing `e`, `catch` invokes some
  exception-handling code (the second argument of `catch`), passing `e` as
  argument; this code might in turn raise a new exception. If `catch` is applied
  to a good state, the monad remains in the good state. -/

def Error.throw {ε α : Type} : ε → Error ε α :=
  sorry

def Error.catch {ε α : Type} : Error ε α → (ε → Error ε α) → Error ε α :=
  sorry


/- ## Question 2 (4 points + 1 bonus point): Properties of `mmap`

We will prove some properties of the `mmap` function introduced in the
lecture's demo. -/

#check mmap

/- 2.1 (2 points). Prove the following identity law about `mmap` for an
arbitrary monad `m`.

Hint: You will need the theorem `LawfulMonad.pure_bind` in the induction step. -/

theorem mmap_pure {m : Type → Type} [LawfulMonad m] {α : Type} (as : List α) :
    mmap (pure : α → m α) as = pure as :=
  sorry

/- Commutative monads are monads for which we can reorder actions that do not
depend on each other. Formally: -/

class CommLawfulMonad (m : Type → Type)
  extends LawfulMonad m :=
  bind_comm {α β γ δ : Type} (ma : m α) (f : α → m β) (g : α → m γ)
      (h : α → β → γ → m δ) :
    (ma >>= (fun a ↦ f a >>= (fun b ↦ g a >>= (fun c ↦ h a b c)))) =
    (ma >>= (fun a ↦ g a >>= (fun c ↦ f a >>= (fun b ↦ h a b c))))

/- 2.2 (1 point). Complete the proof that `Option` is a commutative monad. -/

theorem Option.bind_comm {α β γ δ : Type} (ma : Option α) (f : α → Option β)
      (g : α → Option γ) (h : α → β → γ → Option δ) :
    (ma >>= (fun a ↦ f a >>= (fun b ↦ g a >>= (fun c ↦ h a b c)))) =
    (ma >>= (fun a ↦ g a >>= (fun c ↦ f a >>= (fun b ↦ h a b c)))) :=
  by
    simp [Bind.bind, Option.bind]
    sorry

/- 2.3 (1 point). Explain why `Error` is not a commutative monad. -/

-- enter your answer here

/- 2.4 (1 bonus point). Prove the following composition law for `mmap`, which
holds for commutative monads. -/

theorem mmap_mmap {m : Type → Type} [CommLawfulMonad m]
      {α β γ : Type} (f : α → m β) (g : β → m γ) (as : List α) :
    (mmap f as >>= mmap g) = mmap (fun a ↦ f a >>= g) as :=
  sorry

end LoVe
