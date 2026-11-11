import CeaLemma.Galerkin.Orthogonality

/-!
# The Galerkin error identity

Vector decomposition was already proved locally in Foundation/VectorSpace;
no `abel` tactic and no Mathlib vector-space theorem is used.
-/

namespace Cea

universe u

theorem galerkin_error_identity {V : Type u} {E : VectorSpace V}
    (a : BilinearForm E) (S : TrialSpace E)
    (u uh vh : V)
    (huh : uh ∈ S.carrier) (hvh : vh ∈ S.carrier)
    (horth : IsGalerkinOrthogonal a S u uh) :
    a.eval (E.sub u uh) (E.sub u uh) =
      a.eval (E.sub u uh) (E.sub u vh) := by
  have hmem : E.sub vh uh ∈ S.carrier := S.sub_mem hvh huh
  have hzero : a.eval (E.sub u uh) (E.sub vh uh) = 0 :=
    horth (E.sub vh uh) hmem
  have hsplit : E.sub u uh = E.add (E.sub u vh) (E.sub vh uh) :=
    E.sub_split u uh vh
  calc
    a.eval (E.sub u uh) (E.sub u uh) =
        a.eval (E.sub u uh) (E.add (E.sub u vh) (E.sub vh uh)) := by
      rw [hsplit]
    _ = a.eval (E.sub u uh) (E.sub u vh) +
          a.eval (E.sub u uh) (E.sub vh uh) :=
      a.add_right (E.sub u uh) (E.sub u vh) (E.sub vh uh)
    _ = a.eval (E.sub u uh) (E.sub u vh) := by rw [hzero, add_zero]

end Cea
