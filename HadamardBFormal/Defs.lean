/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Core definitions (scaffold stub)
-/

namespace HadamardBFormal

/-- An integer is a Hadamard sign when it is `+1` or `-1`. -/
def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

end HadamardBFormal
