import CeaLemma.Foundation.TrialSpace

/-!
# Best approximation in our own trial space

The construction uses Mathlib's complete-real infimum (`sInf`, `csInf_le`,
`le_csInf`) ONLY, as explicitly permitted by the project's boundary.
-/

namespace Cea

universe u

/-- Candidate approximation errors, each evaluated using our own norm. -/
def approxErrors {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V) : Set ℝ :=
  {r : ℝ | ∃ vh : V, vh ∈ S.carrier ∧ r = N.norm (E.sub u vh)}

theorem approxErrors_nonempty {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V) :
    (approxErrors N S u).Nonempty := by
  refine ⟨N.norm (E.sub u E.zero), ?_⟩
  exact ⟨E.zero, S.zero_mem, rfl⟩

theorem approxErrors_bddBelow {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V) :
    BddBelow (approxErrors N S u) := by
  refine ⟨0, ?_⟩
  intro r hr
  obtain ⟨vh, _, hr⟩ := hr
  rw [hr]
  exact N.norm_nonneg (E.sub u vh)

/-- Optimal approximation error as a greatest lower bound. -/
noncomputable def bestApproxError {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V) : ℝ :=
  sInf (approxErrors N S u)

theorem bestApproxError_le {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u vh : V)
    (hvh : vh ∈ S.carrier) :
    bestApproxError N S u ≤ N.norm (E.sub u vh) := by
  unfold bestApproxError
  apply csInf_le (approxErrors_bddBelow N S u)
  exact ⟨vh, hvh, rfl⟩

theorem bestApproxError_greatestLowerBound {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V)
    (c : ℝ) (h : ∀ vh : V, vh ∈ S.carrier → c ≤ N.norm (E.sub u vh)) :
    c ≤ bestApproxError N S u := by
  unfold bestApproxError
  apply le_csInf (approxErrors_nonempty N S u)
  intro r hr
  obtain ⟨vh, hvh, hr⟩ := hr
  rw [hr]
  exact h vh hvh

theorem bestApproxError_nonneg {V : Type u} {E : VectorSpace V}
    (N : VectorNorm E) (S : TrialSpace E) (u : V) :
    0 ≤ bestApproxError N S u := by
  apply bestApproxError_greatestLowerBound N S u 0
  intro vh _
  exact N.norm_nonneg (E.sub u vh)

end Cea
