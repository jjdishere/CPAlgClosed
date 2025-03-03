/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import LocalClassFieldTheory.FromMathlib.CpDef
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Group.Completion

/-!
This file contains lemmas that should exist in file
`CpDef` after it get merged, at the very end of the file.
-/

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

noncomputable
instance _root_.QPAlg.nontriviallyNormedField: NontriviallyNormedField (QPAlg p) where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
    use x
    rw [QPAlg.QP.norm_extends]
    exact hx

noncomputable
instance nontriviallyNormedField : NontriviallyNormedField ℂ_[p] where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := QPAlg p)
    use x
    rw [PadicComplex.norm_extends]
    exact hx

instance charZero : CharZero ℂ_[p] :=
  (RingHom.charZero_iff ((algebraMap (QPAlg p) ℂ_[p]).comp
      (algebraMap ℚ_[p] (QPAlg p))).injective).mp inferInstance

-- `Diamond of two norm structures on C_p`
theorem norm_eq_norm (x : ℂ_[p]): @norm (UniformSpace.Completion (QPAlg p)) (UniformSpace.Completion.instNorm (QPAlg p)) x = ‖x‖ := by
  apply congrFun
  apply UniformSpace.Completion.extension_unique (f := @norm (QPAlg p) _) (g := @norm ℂ_[p] _)
  · exact uniformContinuous_norm
  · exact uniformContinuous_norm (E := ℂ_[p])
  · exact fun _ ↦ (norm_extends p _).symm

end PadicComplex
