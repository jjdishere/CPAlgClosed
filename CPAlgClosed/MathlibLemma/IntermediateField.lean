/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
This file contains lemmas that should exist in file
`Mathlib.FieldTheory.IntermediateField.Basic` before `IntermediateField.map_map`
-/

namespace IntermediateField

@[simp]
lemma mem_map {K L L': Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L'] {S : IntermediateField K L} {f : L →ₐ[K] L'} {y : L'} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y

-- Higher priority to apply before `mem_map`.
@[simp 1100]
lemma mem_map' {K L L': Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L'] {S : IntermediateField K L} (f : L →ₐ[K] L') {x : L} : f x ∈ S.map f ↔ x ∈ S :=
  ⟨fun h ↦ let ⟨_, ha⟩ := mem_map.mp h; f.injective ha.2 ▸ ha.1, fun h ↦ mem_map.mpr ⟨x, h, rfl⟩⟩

end IntermediateField
