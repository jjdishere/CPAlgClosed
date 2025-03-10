/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import CPAlgClosed.Krasner
import CPAlgClosed.PadicComplex
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The `p`-adic complex number field is algebraically complete.

In this file, we prove that the `p`-adic complex number field `ℂ_[p]` is algebraically closed
using Krasner's lemma.

## Main results
* `PadicComplex.isAlgClosed`: the `p`-adic complex number field is algebraically closed.

## Tags
p-adic complex numbers, algebraically closed
-/

open Polynomial

theorem Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt {K L : Type*}
    [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K} (a : L) {ε : ℝ}
    (hε : 0 < ε) (ha : f.aeval a = 0) (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, i ≤ f.natDegree → (‖g.coeff i - f.coeff i‖) < ε) (hg : g.Splits (algebraMap K L)) :
    ∃ b ∈ g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  have hcard : (g.aroots L).card = f.natDegree := by
    rw [aroots, Polynomial.splits_iff_card_roots.mp]
    · simpa
    · rw [Polynomial.splits_map_iff]
      simpa
  have hne : (f.natDegree : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, hfm, Polynomial.Monic.natDegree_eq_zero_iff_eq_one]
    intro h
    simp [h] at ha
  suffices this : ((g.aroots L).map fun x => ‖a - x‖).prod < ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : ℝ) by
    by_contra! h
    have := Multiset.prod_map_le_prod_map₀ (fun b ↦ ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * (‖a‖ ⊔ 1)) (fun b ↦ ‖a - b‖) (by intros; positivity) h
    simp [Multiset.map_const', hcard, Multiset.prod_replicate, mul_pow, ←
      Real.rpow_natCast, ← Real.rpow_mul (by positivity : ((f.natDegree + 1) * ε) > 0).le, inv_mul_cancel₀ hne] at this
    linarith
  calc
  _ = (Multiset.map (fun x ↦ NormedField.toMulRingNorm L (a - x)) (g.aroots L)).prod := rfl
  _ = ‖(Multiset.map (fun x ↦ a - x) (g.aroots L)).prod‖ := by
    rw [Multiset.prod_hom' (g.aroots L) (NormedField.toMulRingNorm L) (fun x : L ↦ a - x)]
    rfl
  _ = ‖g.aeval a‖ := by
    congr
    rw [Polynomial.aeval_eq_prod_aroots_sub_of_monic_of_splits hgm hg]
  _ ≤ ‖g.aeval a - f.aeval a‖ + ‖f.aeval a‖ := by
    convert norm_add_le (g.aeval a - f.aeval a) (f.aeval a)
    simp
  _ = ‖(∑ i ∈ Finset.range (g.natDegree + 1), C (g.coeff i - f.coeff i) * X ^ i).aeval a‖ := by
    rw [← map_sub (aeval a) g f]
    simp only [ha, norm_zero, add_zero]
    rw [Polynomial.as_sum_range' (g - f) (g.natDegree + 1)]
    · congr
      simp [← Polynomial.C_mul_X_pow_eq_monomial]
    · simpa [hdeg, Nat.lt_succ_iff] using Polynomial.natDegree_sub_le g f
  _ ≤ ∑ i ∈ Finset.range (g.natDegree + 1), ‖algebraMap K L (g.coeff i - f.coeff i) * a ^ i‖ := by
    have := norm_sum_le (Finset.range (g.natDegree + 1)) (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).aeval a)
    simpa [Polynomial.aeval_mul] using this
    -- The following tactic does not work:
    -- simpa [Polynomial.aeval_mul] using norm_sum_le (Finset.range (g.natDegree + 1))
    --     (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).aeval a)
  _ < _ := by
    rw [hdeg]
    convert Finset.sum_lt_sum_of_nonempty (g := fun i ↦ ε * (‖a‖ ⊔ 1) ^ ↑f.natDegree) (Finset.nonempty_range_succ) ?_
    · simp [mul_assoc]
    · simp only [Finset.mem_range, map_sub, norm_mul, norm_pow]
      intro i hi
      apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      · simpa [← map_sub] using hcoeff i (Nat.le_of_lt_succ hi)
      · refine (pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ 1) i).trans ?_
        exact pow_le_pow_right₀ (le_max_right ‖a‖ 1) (Nat.le_of_lt_succ hi)
      all_goals positivity

theorem Polynomial.exists_monic_norm_map_algebraMap_coeff_sub_lt {K} [NormedField K] {f : Polynomial (UniformSpace.Completion K)} (hf : f.Monic) {ε : ℝ} (hε : ε > 0) : ∃ g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ (∀ i : ℕ, i ≤ f.natDegree → (‖(g.map (algebraMap _ _)).coeff i - f.coeff i‖) < ε) := by
  by_cases h : f.natDegree = 0
  · use 1
    simp only [monic_one, h, natDegree_one, nonpos_iff_eq_zero, Polynomial.map_one, forall_eq,
      coeff_one_zero, true_and]
    rw [← h, ← Polynomial.leadingCoeff]
    simp [hf, hε]
  choose c hc using fun i ↦ Metric.denseRange_iff.mp (UniformSpace.Completion.denseRange_coe (α := K)) (f.coeff i) ε hε
  let g := C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i
  have hdeg : g.natDegree = f.natDegree := by
    calc
    _ = (C (1 : K) * X ^ f.natDegree).natDegree := by
      simp only [g]
      apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
      simp
      rw [← Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      simpa [Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)] using hi
    _ = f.natDegree := by
      simp
  use g
  refine ⟨?_, ?_, fun i hi ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg]
    simp [g]
  · exact hdeg.symm
  · by_cases h : i = f.natDegree
    · simp [g, h, hf, hε]
    · simpa [g, h, lt_of_le_of_ne hi h, ← dist_eq_norm_sub'] using hc i

variable (p : ℕ) [Fact p.Prime]

/--
`ℂ_[p]` is algebraically closed.
-/
instance PadicComplex.isAlgClosed : IsAlgClosed ℂ_[p] := by
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  by_cases fnatdeg1 : f.natDegree = 1
  · rw [fmon.eq_X_add_C fnatdeg1]
    use - f.coeff 0
    simp
  let F := f.SplittingField
  letI : NormedField F :=
    spectralNormToNormedField (K := ℂ_[p]) IsUltrametricDist.isNonarchimedean_norm
  letI : NormedAlgebra ℂ_[p] F := {
    spectralNormToNormedSpace (K := ℂ_[p]) IsUltrametricDist.isNonarchimedean_norm with
    ..}
  let a := Polynomial.rootOfSplits _ (Polynomial.SplittingField.splits f)
      (Polynomial.degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := Polynomial.map_rootOfSplits (algebraMap _ _) (Polynomial.SplittingField.splits f) (Polynomial.degree_ne_of_natDegree_ne fnatdeg0)
  classical
    let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  have Snonempty : S.Nonempty := by
    have : 1 < Fintype.card (f.rootSet F) := by
      rw [Polynomial.card_rootSet_eq_natDegree firr.separable (Polynomial.SplittingField.splits f)]
      omega
    rw [Fintype.one_lt_card_iff_nontrivial] at this
    let ⟨⟨a', h1⟩, h2⟩ := exists_ne (⟨a, Polynomial.mem_rootSet.mpr ⟨firr.ne_zero, fa0⟩⟩ : (f.rootSet F))
    use a'
    simp only [ne_eq, Finset.mem_filter, Set.mem_toFinset, S]
    simp only [ne_eq, Subtype.mk.injEq] at h2
    exact ⟨h1, h2⟩
  let δ : ℝ := Finset.min' (S.image fun x => ‖a - x‖) (Finset.image_nonempty.mpr Snonempty)
  have norm_sub_le : ∀ a' : F, IsConjRoot ℂ_[p] a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
    apply Finset.mem_image_of_mem
    simp only [S, minpoly.eq_of_irreducible_of_monic firr fa0 fmon, Finset.mem_filter, Set.mem_toFinset]
    rw [← (isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩)]
    exact ⟨conj, ne.symm⟩
  have δpos : δ > 0 := by
    simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, δ]
    rintro a' ha'
    simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
    rw [norm_pos_iff, sub_ne_zero]
    exact ha'.2.symm
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  let ⟨g, gmon, gdeg, gcoeff⟩ := Polynomial.exists_monic_norm_map_algebraMap_coeff_sub_lt fmon hε
  let gCp := g.map (algebraMap _ ℂ_[p])
  have gCpcoeff : ∀ i : ℕ, i ≤ f.natDegree → (‖gCp.coeff i - f.coeff i‖) < (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) := by
    simpa [gCp, PadicComplex.norm_eq_norm] using gcoeff
  have gCpSplitsId : gCp.Splits (RingHom.id _) := by
    simp only [Polynomial.splits_map_iff, RingHomCompTriple.comp_eq, gCp]
    apply Polynomial.splits_of_isScalarTower (K := QPAlg p)
    simp only [Algebra.id.map_eq_id]
    exact IsAlgClosed.splits g
  have gCpSplits : gCp.Splits (algebraMap ℂ_[p] F) :=
    Polynomial.splits_of_isScalarTower _ gCpSplitsId
  let ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt a hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gCpcoeff gCpSplits
  have hab : ‖a - b‖ < δ := by
    have : (max ‖a‖ 1) > 0 := by positivity
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul, ← Real.rpow_mul (div_pos δpos this).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ this.ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have bbot : b ∈ (⊥ : IntermediateField ℂ_[p] F) := by
    rw [Polynomial.aroots_def, Polynomial.roots_map _ gCpSplitsId, Multiset.mem_map] at hb
    let ⟨bCp, _, hbCp⟩ := hb
    rw [IntermediateField.mem_bot]
    exact ⟨bCp, hbCp⟩
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  have abot : a ∈ (⊥ : IntermediateField ℂ_[p] F) := by
    have masp : (minpoly ℂ_[p] a).Splits (algebraMap ℂ_[p] F) := by
      simpa [minpoly.eq_of_irreducible_of_monic firr fa0 fmon] using (Polynomial.SplittingField.splits f)
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using
        IsKrasnerNormed.krasner_normed (minpoly.irreducible ⟨f, fmon, fa0⟩).separable
          masp ⟨gCp, gmon.map _, hb.2⟩ fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  let ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp abot
  use aCp
  apply_fun algebraMap ℂ_[p] F
  · rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
    exact fa0
  · exact RingHom.injective _
