/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.Analysis.Normed.Algebra.Norm

/-!
This file contains lemmas that should exist in file
`Mathlib.Analysis.Normed.Algebra.Norm`, at the very end of the file.
-/

namespace MulAlgebraNorm

variable {R S : Type*} [SeminormedCommRing R] [Ring S] [Algebra R S]

/--
The algebra norm underlying an multiplicative algebra norm.
-/
def toAlgebraNorm (f : MulAlgebraNorm R S) : AlgebraNorm R S := {
  f with
  mul_le' _ _ := (f.map_mul' _ _).le
}

instance instCoeAlgebraNorm : Coe (MulAlgebraNorm R S) (AlgebraNorm R S) := ⟨toAlgebraNorm⟩

@[simp]
lemma coe_AlgebraNorm (f : MulAlgebraNorm R S) : ⇑(f : AlgebraNorm R S) = ⇑f := rfl

end MulAlgebraNorm

namespace NormedAlgebra

/--
Given a normed field extension `L / K`, the norm on L is a multiplicative `K`-algebra norm.
-/
def toMulAlgebraNorm (K L : Type*) [NormedField K] [NormedField L]
    [NormedAlgebra K L] : MulAlgebraNorm K L := {
      NormedField.toMulRingNorm L with
      smul' r x := by
        simp only [Algebra.smul_def, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
          map_mul, mul_eq_mul_right_iff, map_eq_zero]
        exact Or.inl <| norm_algebraMap' L r
    }

@[simp]
lemma toMulAlgebraNorm_apply (K : Type*) {L : Type*} [NormedField K] [NormedField L]
    [NormedAlgebra K L] (x : L) : toMulAlgebraNorm K L x = ‖x‖ := rfl

end NormedAlgebra
