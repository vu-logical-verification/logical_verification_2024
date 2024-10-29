/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Minus 2

1.1 (3 points). Define the function `minusTwo` that subtracts two from
its argument.

Hint: There should be three cases. -/

def minusTwo : ℕ → ℕ :=
  sorry

/- 1.2 (1 point). Convince yourself that your definition of `minusTwo` works by
testing it on a few examples. -/

#eval minusTwo 0   -- expected: 0
-- invoke `#eval` or `#reduce` here


/- ## Question 2 (6 points): Lists

Consider the type `List` described in the lecture and the `append` and `reverse`
functions from the lecture's demo. The `List` type is part of Lean's
core libraries. You will find the definition of `append` and `reverse` in
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `List`, `append`, or `reverse`;
3. click the identifier. -/

#print List
#check append
#check reverse

/- 2.1 (2 points). Test that `reverse` behaves as expected on a few examples.

In the first example, the type annotation `: List ℕ` is needed to guide Lean's
type inference. -/

#eval reverse ([] : List ℕ)   -- expected: []
#eval reverse [1, 3, 5]       -- expected: [5, 3, 1]
-- invoke `#eval` here

/- 2.2 (4 points). State (without proving them) the following properties of
`append` and `reverse`. Schematically:

    `append _ (append _ xs ys) zs = append _ xs (append _ ys zs)`
    `reverse (append _ xs ys) = append _ (reverse ys) (reverse xs)`

for all lists `xs`, `ys`, `zs`. Try to give meaningful names to your theorems.

Hint: Take a look at `reverse_reverse` from the demonstration file. -/

#check SorryTheorems.reverse_reverse

-- enter your theorem statements here

end LoVe
