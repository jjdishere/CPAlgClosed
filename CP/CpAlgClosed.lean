import CP.Krasner
import LocalClassFieldTheory.FromMathlib.CpDef

#check PadicComplex
#check Multiset.prod_map_le_prod_map₀
#check Polynomial.splits_iff_card_roots

theorem exists_aroots_norm_sub_lt {K L} [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K} (a : L) {ε : ℝ} (hε : 0 < ε)
    (ha : f.aeval a = 0) (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, i ≤ f.natDegree → (‖g.coeff i - f.coeff i‖) < ε) (hg : g.Splits (algebraMap K L)) :
    ∃ b ∈ g.aroots L, ‖a - b‖ < ε ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  have hcard : (g.aroots L).card = f.natDegree := by
    sorry
    -- rw [← Polynomial.splits_iff_card_roots.mp]
  have hne : (f.natDegree : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, hfm, Polynomial.Monic.natDegree_eq_zero_iff_eq_one]
    intro h
    simp [h] at ha
  suffices this : ((g.aroots L).map fun x => ‖a - x‖).prod < ε * (max ‖a‖ 1)^(f.natDegree : ℝ) by
    by_contra! h
    have := Multiset.prod_map_le_prod_map₀ (fun b ↦ ε ^ (f.natDegree : ℝ)⁻¹ * (‖a‖ ⊔ 1)) (fun b ↦ ‖a - b‖) (by intros; positivity) h
    simp [Multiset.map_const', hcard, Multiset.prod_replicate, mul_pow, ←
      Real.rpow_natCast, ← Real.rpow_mul hε.le, inv_mul_cancel₀ hne] at this
    linarith
  sorry -- calc

#check spectral_norm_unique'
instance foo {K L} [NontriviallyNormedField K] [CompleteSpace K] [NormedField L] [NormedAlgebra K L] [IsUltrametricDist K] [Algebra.IsAlgebraic K L] : IsKrasnerNorm K L := sorry -- input from last file


namespace PadicComplex

variable (p : ℕ) [Fact p.Prime] {L} [NormedField L] [NormedAlgebra ℂ_[p] L] [Algebra.IsAlgebraic ℂ_[p] L]
#synth Field ℂ_[p]
#synth CompleteSpace ℂ_[p]

noncomputable
instance : NontriviallyNormedField ℂ_[p] where
  non_trivial := sorry

#synth NontriviallyNormedField ℂ_[p]
#synth IsKrasnerNorm ℂ_[p] L
#synth IsUltrametricDist ℂ_[p]


#synth CharZero ℚ_[p]
#synth Algebra ℚ_[p] (QPAlg p)
#synth Algebra (QPAlg p) ℂ_[p]
#synth CharZero (QPAlg p)
instance charZero : CharZero ℂ_[p] :=
  (RingHom.charZero_iff ((algebraMap (QPAlg p) ℂ_[p]).comp
      (algebraMap ℚ_[p] (QPAlg p))).injective).mp inferInstance

end PadicComplex

variable {K} [NormedField K]
#synth NormedField (UniformSpace.Completion K)
#synth NormedAlgebra K (UniformSpace.Completion K)
theorem Polynomial.approximation_completion {K} [NormedField K] {f : Polynomial (UniformSpace.Completion K)} (hf : f.Monic) {ε : ℝ} (hε : ε > 0) : ∃ g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ (∀ i : ℕ, i ≤ f.natDegree → (‖(g.map (algebraMap _ _)).coeff i - f.coeff i‖) < ε) := sorry

variable (K L) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (S :IntermediateField K L)
#synth Algebra K S

variable (p : ℕ) [Fact p.Prime]

#check mulNormToNormedField
#check spectralNorm
#check spectralAlgNormOfFdNormal
#check spectralAlgNorm
#check spectralAlgNorm_isPowMul
instance PadicComplex.isAlgClosed : IsAlgClosed ℂ_[p] := by
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fdegnezero : f.degree ≠ 0 := sorry -- Irreducible.natDegree_pos
  let F := f.SplittingField
  letI : NormedField F :=
    spectralNormToNormedField (K := ℂ_[p]) IsUltrametricDist.isNonarchimedean_norm
  letI : NormedAlgebra ℂ_[p] F := {
    spectralNormToNormedSpace (K := ℂ_[p]) IsUltrametricDist.isNonarchimedean_norm with
    ..
  }
  -- letI : IsKrasnerNorm ℂ_[p] F := inferInstance
  let a := Polynomial.rootOfSplits _ (Polynomial.SplittingField.splits f) sorry
  have fa0 : f.aeval a = 0 := Polynomial.map_rootOfSplits (algebraMap _ _) (Polynomial.SplittingField.splits f) fdegnezero
  have fa : f = minpoly ℂ_[p] a := minpoly.eq_of_irreducible_of_monic firr fa0 fmon
  have masp : (minpoly ℂ_[p] a).Splits (algebraMap ℂ_[p] F) := by
    simpa [fa] using (Polynomial.SplittingField.splits f)
  have aint : IsIntegral ℂ_[p] a := ⟨f, fmon, fa0⟩
  classical
    let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  have Snonempty : S.Nonempty := sorry
  let δ : ℝ := Finset.min' (S.image fun x => ‖a - x‖) (Finset.image_nonempty.mpr Snonempty)
  have norm_sub_le : ∀ a' : F, IsConjRoot ℂ_[p] a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
    apply Finset.mem_image_of_mem
    simp only [S, fa, Finset.mem_filter, Set.mem_toFinset]
    rw [← (isConjRoot_iff_mem_minpoly_rootSet aint)]
    exact ⟨conj, ne.symm⟩
  let ε := (δ / (max ‖a‖ 1)) ^ f.natDegree
  have hε : ε > 0 := sorry
  let ⟨g, gmon, gdeg, gcoeff⟩ := Polynomial.approximation_completion fmon hε
  let gCp := g.map (algebraMap _ ℂ_[p])
  have gCpmon : gCp.Monic := sorry
  have gCpdeg : gCp.natDegree = f.natDegree := sorry
  have gCpcoeff : ∀ i : ℕ, i ≤ f.natDegree → (‖gCp.coeff i - f.coeff i‖) < ε := sorry
  have gCpSplitsId : gCp.Splits (RingHom.id _) := sorry
  have gCpSplits : gCp.Splits (algebraMap ℂ_[p] F) := sorry
  let ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt a hε fa0 fmon gCpmon gCpdeg gCpcoeff gCpSplits
  have bbot : b ∈ (⊥ : IntermediateField ℂ_[p] F) := sorry -- Polynomial.roots_map
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  have bint : IsIntegral ℂ_[p] b :=
  ⟨gCp, gCpmon, hb.2⟩
  have : a ∈ (⊥ : IntermediateField ℂ_[p] F) := by
    have := IsKrasnerNorm.krasner_norm ℂ_[p] F (minpoly.irreducible aint).separable
        (x := a) (y := b) masp bint sorry
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using this
  let ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp this
  use aCp
  apply_fun algebraMap ℂ_[p] F
  · rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
    exact fa0
  · exact RingHom.injective _
