import CeaLemma.Bounds.Energy

/-!
# The pointwise Cea bound without `ring`, `linarith`, or `simp`
-/

namespace Cea

universe u

theorem cea_pointwise {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (N : VectorNorm E) (S : TrialSpace E)
    (M alpha : ℝ) (hM : 0 ≤ M) (halpha : 0 < alpha)
    (hcont : HasContinuityBound a N M)
    (hcoer : HasCoercivityBound a N alpha)
    (u uh : V) (huh : uh ∈ S.carrier)
    (horth : IsGalerkinOrthogonal a S u uh)
    (vh : V) (hvh : vh ∈ S.carrier) :
    N.norm (E.sub u uh) ≤ (M / alpha) * N.norm (E.sub u vh) := by
  have he :
      alpha * (N.norm (E.sub u uh)) ^ 2 ≤
        M * N.norm (E.sub u uh) * N.norm (E.sub u vh) :=
    cea_energy_bound a N S M alpha hcont hcoer u uh huh horth vh hvh
  by_cases hzero : N.norm (E.sub u uh) = 0
  · rw [hzero]
    exact mul_nonneg (RealInequalities.nonneg_div hM halpha)
      (N.norm_nonneg (E.sub u vh))
  · have hpos : 0 < N.norm (E.sub u uh) :=
      lt_of_le_of_ne (N.norm_nonneg (E.sub u uh)) (Ne.symm hzero)
    have hmul :
        N.norm (E.sub u uh) * (alpha * N.norm (E.sub u uh)) ≤
          N.norm (E.sub u uh) * (M * N.norm (E.sub u vh)) := by
      calc
        N.norm (E.sub u uh) * (alpha * N.norm (E.sub u uh)) =
            alpha * (N.norm (E.sub u uh)) ^ 2 :=
          RealInequalities.mul_square_swap _ _
        _ ≤ M * N.norm (E.sub u uh) * N.norm (E.sub u vh) := he
        _ = N.norm (E.sub u uh) * (M * N.norm (E.sub u vh)) :=
          RealInequalities.mul_triple_swap _ _ _
    have hcancel :
        alpha * N.norm (E.sub u uh) ≤ M * N.norm (E.sub u vh) :=
      RealInequalities.cancel_pos_left hmul hpos
    have hreorder :
        N.norm (E.sub u uh) * alpha ≤ M * N.norm (E.sub u vh) := by
      calc
        N.norm (E.sub u uh) * alpha = alpha * N.norm (E.sub u uh) :=
          mul_comm _ _
        _ ≤ M * N.norm (E.sub u vh) := hcancel
    calc
      N.norm (E.sub u uh) ≤ (M * N.norm (E.sub u vh)) / alpha :=
        RealInequalities.le_div_of_mul_le halpha hreorder
      _ = (M / alpha) * N.norm (E.sub u vh) :=
        RealInequalities.div_mul_swap _ _ _

end Cea
