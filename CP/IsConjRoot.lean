import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Closure

open IntermediateField

theorem IsConjRoot.mem_normalClosure {K L} [Field K] [Field L] [Algebra K L]
    {x y : L} (hx : IsAlgebraic K x) (h : IsConjRoot K x y) :
    y ∈ normalClosure K K⟮x⟯ L := by
  sorry

-- wrong , should be K(all conj of x)
theorem IsConjRoot.exists_algEquiv_of_minpoly_split {K L} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {x y : L}
    (h : IsConjRoot K x y) (sp : (minpoly K x).Splits (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, σ y = x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval
      (fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, sorry⟩)
    --minpoly_add_algebraMap_splits
      (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ sorry, hσ⟩ -- fin dim vector space inj => bij
-- another PR
