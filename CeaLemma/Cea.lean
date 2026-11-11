import CeaLemma.Bounds.Pointwise
import CeaLemma.Approximation.Infimum

/-!
# Céa's lemma: quasi-optimality of a Galerkin approximation

All vector/norm/linear/subspace facts come from this project. The only
external mathematical facts belong to the ordered real field and infimum.
-/

namespace Cea

universe u

/-- Céa's lemma for an abstract, locally axiomatized normed vector space. -/
theorem cea_lemma {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (N : VectorNorm E) (S : TrialSpace E)
    (M alpha : ℝ)
    (hM : 0 ≤ M) (halpha : 0 < alpha)
    (hcont : HasContinuityBound a N M)
    (hcoer : HasCoercivityBound a N alpha)
    (u uh : V) (huh : uh ∈ S.carrier)
    (horth : IsGalerkinOrthogonal a S u uh) :
    N.norm (E.sub u uh) ≤ (M / alpha) * bestApproxError N S u := by
  by_cases hMzero : M = 0
  · have h0 :
        N.norm (E.sub u uh) ≤
          (M / alpha) * N.norm (E.sub u E.zero) :=
      cea_pointwise a N S M alpha hM halpha hcont hcoer
        u uh huh horth E.zero S.zero_mem
    have hz : N.norm (E.sub u uh) ≤ 0 := by
      calc
        N.norm (E.sub u uh) ≤
            (M / alpha) * N.norm (E.sub u E.zero) := h0
        _ = 0 := by rw [hMzero, zero_div, zero_mul]
    calc
      N.norm (E.sub u uh) ≤ 0 := hz
      _ = (M / alpha) * bestApproxError N S u := by
        rw [hMzero, zero_div, zero_mul]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have hcpos : 0 < M / alpha :=
      RealInequalities.positive_div hMpos halpha
    have hlow :
        N.norm (E.sub u uh) / (M / alpha) ≤
          bestApproxError N S u := by
      apply bestApproxError_greatestLowerBound N S u _
      intro vh hvh
      apply RealInequalities.div_le_of_le_mul hcpos
      exact cea_pointwise a N S M alpha hM halpha hcont hcoer
        u uh huh horth vh hvh
    exact RealInequalities.le_mul_of_div_le hcpos hlow

end Cea
