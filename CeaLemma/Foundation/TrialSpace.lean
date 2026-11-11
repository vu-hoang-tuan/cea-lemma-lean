import CeaLemma.Foundation.Norm

/-!
# Galerkin trial spaces, defined independently of `Submodule`
-/

namespace Cea

universe u

structure TrialSpace {V : Type u} (E : VectorSpace V) where
  carrier : Set V
  zero_mem : E.zero ∈ carrier
  add_mem : ∀ {x y : V}, x ∈ carrier → y ∈ carrier → E.add x y ∈ carrier
  neg_mem : ∀ {x : V}, x ∈ carrier → E.neg x ∈ carrier
  smul_mem : ∀ (a : ℝ) {x : V}, x ∈ carrier → E.smul a x ∈ carrier

namespace TrialSpace

variable {V : Type u} {E : VectorSpace V}

theorem sub_mem (S : TrialSpace E) {x y : V}
    (hx : x ∈ S.carrier) (hy : y ∈ S.carrier) :
    E.sub x y ∈ S.carrier := by
  change E.add x (E.neg y) ∈ S.carrier
  exact S.add_mem hx (S.neg_mem hy)

end TrialSpace
end Cea
