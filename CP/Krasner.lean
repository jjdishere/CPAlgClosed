import Mathlib
import LocalClassFieldTheory.FromMathlib.SpectralNormUnique
import CP.IsConjRoot

/-!
# Krasner's Lemma

In this file, we prove Krasner's lemma. Instead of state and prove the Krasner's lemma directly,
we define a predicate `IsKrasner K L` for arbitary field extensions `L / K` with a normed/valued
instance on `L` as the abstraction of the conclusion of the Krasner's lemma. Then we prove the
Krasner's lemma holds for `L / K` if `K` is a complete normed/valued field and the norm/valuation
on `L` is compatible with the one on `K`.

## Main definitions

* `IsKrasner K L`

* `IsKrasnerNorm K L`

## Main results

* `of_complete` : If `K` is a complete normed/valued field, such that there exists a
unique norm extension on every algebraic extension `L` of `K`, then `IsKrasner K L` holds for every
algebraic extension `L` over `K`.

## Tags

## TODO
1. The condition `Algebra.IsAlgebraic` can be dropped in `of_complete`. This needs a generalization
of the field `Mathlib.FieldTheory.Extension` to trancendental cases. Almost all theorems in that
file still holds without the assumption of being algebraic.

2. After the definition of `Valued` is fixed, the valued version can be proved under the assumption
`IsValExtension K L`

3. Show that if `IsKrasner K (AlgebraicClosure K)` holds, then the completion of
`(AlgebraicClosure K)` is algebraically closed.

4. After the uniqueness of norm extension of complete normed field is in mathlib, drop the
conditions about `uniqueNormExtension` in `of_complete`.
If `K` is a complete normed/valued field and the norm/valuation on `L` is
compatible with the one on `K`, then `IsKrasnerNorm K L` holds.

5. After 3 and 4 are proved, show that $\mathbb{C}_p$ is algebraically closed.

-/

section AlgebraNorm

namespace MulAlgebraNorm

variable {R S : Type*} [SeminormedCommRing R] [Ring S] [Algebra R S]

def toAlgebraNorm (f : MulAlgebraNorm R S) : AlgebraNorm R S := {
  f with
  mul_le' _ _ := (f.map_mul' _ _).le
}

instance : Coe (MulAlgebraNorm R S) (AlgebraNorm R S) := ⟨toAlgebraNorm⟩

@[simp]
lemma coe_AlgebraNorm (f : MulAlgebraNorm R S) : ⇑(f : AlgebraNorm R S) = ⇑f := rfl

end MulAlgebraNorm

namespace NormedAlgebra

def toMulAlgebraNorm (K L : Type*) [NormedField K] [NormedField L]
    [NormedAlgebra K L] : MulAlgebraNorm K L := {
      NormedField.toMulRingNorm L with
      smul' r x := by
        simp only [Algebra.smul_def', AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
          map_mul, mul_eq_mul_right_iff, map_eq_zero]
        exact Or.inl <| norm_algebraMap' L r
    }

@[simp]
lemma toMulAlgebraNorm_apply (K : Type*) {L : Type*} [NormedField K] [NormedField L]
    [NormedAlgebra K L] (x : L) : toMulAlgebraNorm K L x = ‖x‖ := rfl

lemma norm_eq_spectralNorm (K : Type*) {L : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
    [CompleteSpace K] (x : L) : ‖x‖ = spectralNorm K L x := by
  rw [← toMulAlgebraNorm_apply K x, ← spectralAlgNorm_def IsUltrametricDist.isNonarchimedean_norm, ← MulAlgebraNorm.coe_AlgebraNorm]
  congr
  apply spectral_norm_unique'
  exact MulRingNorm.isPowMul (toMulAlgebraNorm K L).toMulRingNorm

end NormedAlgebra

end AlgebraNorm

open IntermediateField Valued

variable (K L : Type*) {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL] [Field K]

section Normed

variable [NormedField L] [Algebra K L]

class IsKrasnerNorm : Prop where
  krasner_norm' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' →  x ≠ x' → ‖x - y‖ < ‖x - x'‖) →
      x ∈ K⟮y⟯

theorem IsKrasnerNorm.krasner_norm [IsKrasnerNorm K L] {x y : L} (hx : (minpoly K x).Separable)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖)) : x ∈ K⟮y⟯ :=
  IsKrasnerNorm.krasner_norm' hx sp hy h

instance IsKrasnerNorm.of_completeSpace {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L] : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let z := x - y
  haveI := IntermediateField.adjoin.finiteDimensional yint
  letI : NontriviallyNormedField K⟮y⟯ := {
    non_trivial := by
      obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
      use algebraMap K K⟮y⟯ k
      simp [hk]
    }
  letI : CompleteSpace K⟮y⟯ := FiniteDimensional.complete K K⟮y⟯
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  let y' : K⟮y⟯ := ⟨y, IntermediateField.subset_adjoin K {y} rfl⟩
  have zsep : IsSeparable K⟮y⟯ z := by
    apply Field.isSeparable_sub (IsSeparable.tower_top K⟮y⟯ xsep)
    simpa using isSeparable_algebraMap y'
  suffices z ∈ K⟮y⟯ by simpa [z, y'] using add_mem this y'.2
  by_contra hz
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra K⟮y⟯ L) := by
    rw [Algebra.mem_bot]
    simp
  rw [this.not] at hz
  obtain ⟨z', hne, h1⟩ := (not_mem_iff_exists_ne_and_isConjRoot zsep
      (minpoly_sub_algebraMap_splits y' (IsIntegral.minpoly_splits_tower_top
        xsep.isIntegral sp))).mp hz
  simp only [ne_eq, Subtype.mk.injEq] at hne
  obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv_of_minpoly_split h1
      (minpoly_sub_algebraMap_splits y'
      (IsIntegral.minpoly_splits_tower_top xsep.isIntegral sp))
  apply_fun σ.symm at hσ
  simp only [AlgEquiv.symm_apply_apply] at hσ
  have : ‖z - z'‖ < ‖z - z'‖ := by
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa only [norm_neg, sub_eq_add_neg] using (IsUltrametricDist.norm_add_le_max z (- z'))
      _ ≤ ‖x - y‖ := by
        simp only [NormedAlgebra.norm_eq_spectralNorm K, hσ, sup_le_iff]
        rw [← AlgEquiv.restrictScalars_apply K, ← spectralNorm_aut_isom (σ.symm.restrictScalars K)]
        simp [z]
      _ < ‖x - (z' + y)‖ := by
        apply kr (z' + y)
        · apply IsConjRoot.of_isScalarTower (L := K⟮y⟯) xsep.isIntegral
          simpa [z, y'] using IsConjRoot.add_algebraMap y' h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  simp only [lt_self_iff_false] at this


-- theorem of_completeSpace {K L : Type*} [Nm_K : NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [Nm_L : NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (uniq : ∀ M : IntermediateField K L, uniqueMulAlgebraNorm M L) : IsKrasnerNorm K L := by
--   constructor
--   intro x y xsep sp yint kr
--   let z := x - y
--   let M := K⟮y⟯
--   have _ := IntermediateField.adjoin.finiteDimensional yint
--   let i_K : NormedAddGroupHom K (⊥ : IntermediateField K L) :=
--     (AddMonoidHomClass.toAddMonoidHom (botEquiv K L).symm).mkNormedAddGroupHom 1 (by sorry) -- simp [extd])
--   have _ : ContinuousSMul K M := by
--     apply Topology.IsInducing.continuousSMul (N := K) (M := (⊥ : IntermediateField K L)) (X := M) (Y := M)
--       (f := (IntermediateField.botEquiv K L).symm) Topology.IsInducing.id i_K.continuous
--     intros c x
--     simp
--     -- exact (algebraMap_smul _ _ _).symm -- add an instance here
--     rw [Algebra.smul_def, @Algebra.smul_def (⊥ : IntermediateField K L) M _ _ _]
--     rfl -- note to reviewers: This is an ugly `rfl`. I'm not sure how to make it better.
--   let _ : CompleteSpace M := FiniteDimensional.complete K M
--   have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
--   have zsep : IsSeparable M z := by
--     apply Field.isSeparable_sub (IsSeparable.tower_top M xsep)
--     simpa using isSeparable_algebraMap (⟨y, hy⟩ : M)
--   suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
--   by_contra hz
--   have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by sorry -- simp [Algebra.mem_bot]
--   rw [this.not] at hz
--   obtain ⟨z', hne, h1⟩ := (not_mem_iff_exists_ne_and_isConjRoot zsep
--       (minpoly_sub_algebraMap_splits (⟨y, hy⟩ : K⟮y⟯) (IsIntegral.minpoly_splits_tower_top
--         xsep.isIntegral sp))).mp hz
--   simp only [ne_eq, Subtype.mk.injEq] at hne

--   -- have eq_spnM : (norm : M → ℝ) = spectralNorm K M :=
--   --   funext <| spectralNorm_unique_field_norm_ext
--   --     (f := instNormedIntermediateField.toMulRingNorm) extd is_na
--   -- have eq_spnL : (norm : L → ℝ) = spectralNorm K L :=
--   --   funext <| spectralNorm_unique_field_norm_ext (f := NL.toMulRingNorm) extd is_na
--   -- have is_naM : IsNonarchimedean (norm : M → ℝ) := eq_spnM ▸ spectralNorm_isNonarchimedean K M is_na
--   -- have is_naL : IsNonarchimedean (norm : L → ℝ) := eq_spnL ▸ spectralNorm_isNonarchimedean K L is_na

--   letI : NontriviallyNormedField M := {
--     SubfieldClass.toNormedField M with
--     non_trivial := by
--       obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
--       use algebraMap K M k
--       change 1 < ‖(algebraMap K L) k‖
--       sorry -- simp [(extd k).symm, hk]-- a lemma for extends nontrivial implies nontrivial
--     }
--   -- have eq_spnML: (norm : L → ℝ) = spectralNorm M L := by
--   --   apply Eq.trans eq_spnL
--   --   apply (_root_.funext <| spectralNorm_unique_field_norm_ext (K := K)
--   --     (f := (spectralMulAlgNorm is_naM).toMulRingNorm) _ is_na).symm
--   --   apply functionExtends_of_functionExtends_of_functionExtends (fA := (norm : M → ℝ))
--   --   · intro m
--   --     exact extd m
--   --   · exact spectralNorm_extends M L -- a lemma for extends extends
--   -- have norm_eq: ‖z‖ = ‖z'‖ := by -- a lemma
--   --   simp only [eq_spnML, spectralNorm]
--   --   congr 1
--     -- spectralNorm K L = spectralnorm M L
--   -- IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1
--   -- need rank one -- exist_algEquiv
--   have extdM : ∀ x : M, ‖x‖ = ‖algebraMap M L x‖ := by
--     sorry
--   have uniqM : uniqueMulAlgebraNorm M L := by
--     sorry
--   have : ‖z - z'‖ < ‖z - z'‖ := by
--     calc
--       _ ≤ max ‖z‖ ‖z'‖ := by
--         sorry -- simpa only [norm_neg, sub_eq_add_neg] using (is_na.norm_extension extd z (- z'))
--       _ ≤ ‖x - y‖ := by

--         sorry -- rw [h1.norm_eq_of_uniqueNormExtension M L z z' uniqM extdM
--              -- (minpoly_sub_algebraMap_splits ⟨y, hy⟩ (xsep.isIntegral.minpoly_splits_tower_top sp))]
--         -- simp only [max_self, le_refl]
--       _ < ‖x - (z' + y)‖ := by
--         apply kr (z' + y)
--         · apply IsConjRoot.of_isScalarTower (L := M) xsep.isIntegral
--           simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
--             IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
--         · simpa [z, sub_eq_iff_eq_add] using hne
--       _ = ‖z - z'‖ := by congr 1; ring
--   simp only [lt_self_iff_false] at this


theorem of_completeSpace' {K L : Type*} [Nm_K : NontriviallyNormedField K] [NL : NormedField L]
    [Algebra K L] (is_na : IsNonarchimedean (‖·‖ : K → ℝ)) [Algebra.IsAlgebraic K L]
    [CompleteSpace K] (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let z := x - y
  let M := K⟮y⟯
  have _ := IntermediateField.adjoin.finiteDimensional yint
  let i_K : NormedAddGroupHom K (⊥ : IntermediateField K L) :=
    (AddMonoidHomClass.toAddMonoidHom (botEquiv K L).symm).mkNormedAddGroupHom 1 (by simp [extd])
  have _ : ContinuousSMul K M := by
    apply Inducing.continuousSMul (N := K) (M := (⊥ : IntermediateField K L)) (X := M) (Y := M)
      (f := (IntermediateField.botEquiv K L).symm) sorry -- inducing_id
      i_K.continuous
    intros c x
    rw [Algebra.smul_def, @Algebra.smul_def (⊥ : IntermediateField K L) M _ _ _]
    sorry -- rfl
    sorry
  let _ : CompleteSpace M := FiniteDimensional.complete K M
  have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
  have zsep : IsSeparable M z := by
    apply Field.isSeparable_sub (IsSeparable.tower_top M xsep)
    simpa using isSeparable_algebraMap (⟨y, hy⟩ : M)
  suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
  by_contra hz
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by sorry -- simp [Algebra.mem_bot]
  rw [this.not] at hz
  -- need + algebra map split and split tower.
  obtain ⟨z', hne, h1⟩ := (not_mem_iff_exists_ne_and_isConjRoot zsep
      (minpoly_sub_algebraMap_splits (⟨y, hy⟩ : K⟮y⟯) (IsIntegral.minpoly_splits_tower_top
        xsep.isIntegral sp))).mp hz
  -- this is where the separablity is used.
  simp only [ne_eq, Subtype.mk.injEq] at hne
  have eq_spnM : (norm : M → ℝ) = spectralNorm K M :=
    sorry
    -- funext <| spectralNorm_unique_field_norm_ext
      -- (f := instNormedIntermediateField.toMulRingNorm) extd is_na
  have eq_spnL : (norm : L → ℝ) = spectralNorm K L :=
    funext <| spectralNorm_unique_field_norm_ext (f := NL.toMulRingNorm
    ) sorry sorry -- extd is_na
  have is_naM : IsNonarchimedean (norm : M → ℝ) := sorry --eq_spnM ▸ spectralNorm_isNonarchimedean K M is_na
  have is_naL : IsNonarchimedean (norm : L → ℝ) := sorry -- eq_spnL ▸ spectralNorm_isNonarchimedean K L is_na
  letI : NontriviallyNormedField M := {
    SubfieldClass.toNormedField M with
    non_trivial := by
      obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
      use algebraMap K M k
      change 1 < ‖(algebraMap K L) k‖
      sorry
      -- simp [extd k, hk]-- a lemma for extends nontrivial implies nontrivial
  }
  have eq_spnML: (norm : L → ℝ) = spectralNorm M L := by
    apply Eq.trans eq_spnL
    apply (_root_.funext <| spectralNorm_unique_field_norm_ext (K := K)
      (f := (spectralMulAlgNorm is_naM).toMulRingNorm) _ is_na).symm
    sorry
    -- apply functionExtends_of_functionExtends_of_functionExtends (fA := (norm : M → ℝ))
    -- · intro m
    --   exact extd m
    -- · exact spectralNorm_extends M L -- a lemma for extends extends
  have norm_eq: ‖z‖ = ‖z'‖ := by -- a lemma
    simp only [eq_spnML, spectralNorm]
    congr 1
    -- spectralNorm K L = spectralnorm M L
  -- IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1
  -- need rank one -- exist_algEquiv
  have : ‖z - z'‖ < ‖z - z'‖ := by
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa only [norm_neg, sub_eq_add_neg] using (is_naL z (- z'))
      _ ≤ ‖x - y‖ := by
        simp [← norm_eq, max_self, le_refl, z]
      _ < ‖x - (z' + y)‖ := by
        apply kr (z' + y)
        · apply IsConjRoot.of_isScalarTower (L := M) xsep.isIntegral
          simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
            IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  simp only [lt_self_iff_false] at this


-- add a requirement that the uniquess is need and
-- TODO: we know this is true and after it is in mathlib we can remove this condition.
theorem of_completeSpace'' {K L : Type*} [Nm_K : NontriviallyNormedField K] [NL : NormedField L]
    [Algebra K L] (is_na : IsNonarchimedean (‖·‖ : K → ℝ)) [CompleteSpace K] : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let L' := algebraicClosure K L
  let xL : L' := ⟨x, IsSeparable.isIntegral xsep⟩
  let yL : L' := ⟨y, yint⟩
  suffices xL ∈ K⟮yL⟯ by
    rwa [← IntermediateField.lift_adjoin_simple K L' yL, IntermediateField.mem_lift xL]
  have hL' : IsKrasnerNorm K L' := sorry -- IsKrasnerNorm.of_completeSpace_aux is_na extd
  apply hL'.krasner_norm
  · exact IsSeparable.of_algHom L'.val xsep
  · rw [← (minpoly.algHom_eq L'.val Subtype.val_injective xL)]
    sorry -- apply minpoly_split_algebraClosure (x := x) xsep.isIntegral sp
  · exact (isIntegral_algHom_iff _ L'.val.toRingHom.injective).mp yint
  · exact fun x' hx' hne => kr x' ((isConjRoot_algHom_iff L'.val).mpr hx')
      (Subtype.coe_ne_coe.mpr hne)

end Normed

section Valued

variable [Field L] [Algebra K L] [vL : Valued L ΓL]

class IsKrasner : Prop where
  krasner' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' → x ≠ x' → v (x - y) < v (x - x')) →
      x ∈ K⟮y⟯

variable {K L}

theorem IsKrasner.krasner [IsKrasner K L] {x y : L} (hx : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x'))) : x ∈ K⟮y⟯ :=
  IsKrasner.krasner' hx sp hy h

end Valued

def uniqueValExtension {K L ΓK} [LinearOrderedCommGroupWithZero ΓK] [Field K]
[Field L] [Algebra K L] [vK : Valued K ΓK] : Prop :=
  ∀ {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ'], ∀ v : Valuation L Γ, ∀ v' : Valuation L Γ',
  IsValExtension vK.v v → IsValExtension vK.v v' → v.IsEquiv v' ∧
    ∃ (Γ : Type*), ∃ (_ : LinearOrderedCommGroupWithZero Γ),
    ∃ (v : Valuation L Γ), IsValExtension vK.v v

theorem IsKrasner.of_completeSpace {K L ΓK ΓL: Type*} [Field K] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK]
[CompleteSpace K] [Field L] [vL : Valued L NNReal] [Algebra K L]
[IsValExtension vK.v vL.v] [Algebra.IsAlgebraic K L] [vK.v.RankOne] [vL.v.RankOne]
(uniq : ∀ M : IntermediateField K L, sorry) : IsKrasnerNorm K L := by sorry

#check spectral_norm_unique'

#check Nat
