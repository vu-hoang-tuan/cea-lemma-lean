import CeaLemma.Bilinear.Properties

/-!
# Galerkin orthogonality

Derive orthogonality by subtracting continuous and discrete weak equations.
-/

namespace Cea

universe u

/-- Galerkin orthogonality, with our own trial-space interface. -/
def IsGalerkinOrthogonal {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (S : TrialSpace E) (u uh : V) : Prop :=
  ∀ v : V, v ∈ S.carrier → a.eval (E.sub u uh) v = 0

/-- The discrete and exact equations imply orthogonality. -/
theorem galerkin_orthogonality {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (L : LinearFunctional E) (S : TrialSpace E)
    (u uh : V)
    (hexact : ∀ v : V, a.eval u v = L.eval v)
    (hdiscrete : ∀ v : V, v ∈ S.carrier → a.eval uh v = L.eval v) :
    IsGalerkinOrthogonal a S u uh := by
  intro v hv
  calc
    a.eval (E.sub u uh) v = a.eval u v - a.eval uh v :=
      a.sub_left u uh v
    _ = L.eval v - L.eval v := by rw [hexact v, hdiscrete v hv]
    _ = 0 := sub_self (L.eval v)

end Cea
