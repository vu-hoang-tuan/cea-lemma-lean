import CeaLemma.Galerkin.ErrorIdentity
import CeaLemma.Foundation.RealInequalities

/-!
# Energy bound (coercivity + Galerkin identity + continuity)
-/

namespace Cea

universe u

theorem cea_energy_bound {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (N : VectorNorm E) (S : TrialSpace E)
    (M alpha : ℝ)
    (hcont : HasContinuityBound a N M)
    (hcoer : HasCoercivityBound a N alpha)
    (u uh : V) (huh : uh ∈ S.carrier)
    (horth : IsGalerkinOrthogonal a S u uh)
    (vh : V) (hvh : vh ∈ S.carrier) :
    alpha * (N.norm (E.sub u uh)) ^ 2 ≤
      M * N.norm (E.sub u uh) * N.norm (E.sub u vh) := by
  calc
    alpha * (N.norm (E.sub u uh)) ^ 2 ≤
        a.eval (E.sub u uh) (E.sub u uh) := hcoer (E.sub u uh)
    _ = a.eval (E.sub u uh) (E.sub u vh) :=
      galerkin_error_identity a S u uh vh huh hvh horth
    _ ≤ |a.eval (E.sub u uh) (E.sub u vh)| :=
      RealInequalities.self_le_abs _
    _ ≤ M * N.norm (E.sub u uh) * N.norm (E.sub u vh) :=
      hcont (E.sub u uh) (E.sub u vh)

end Cea
