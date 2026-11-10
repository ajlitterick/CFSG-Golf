module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreConj

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {X : Type*} [Group X]

theorem GLAPPrimeCoreOf_le_of_normal_sub {p : ℕ} [Finite X] (hp : p.Prime) {H M : Subgroup X}
    (hHM : H ≤ M) (hn : (H.subgroupOf M).Normal) :
    GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p M := by
  refine le_GLAPPrimeCoreOf_of_normal ((GLAPPrimeCoreOf_le (p := p) H).trans hHM) ?_
    (coprime_card_GLAPPrimeCoreOf hp H)
  intro g hg x hx
  have hconj : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := by
    intro m hm h hh
    have := hn.conj_mem ⟨h, hHM hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have hgN : g ∈ Subgroup.normalizer (H : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj g hg h
    · intro hh
      simpa [mul_assoc] using hconj g⁻¹ (M.inv_mem hg) _ hh
  exact GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp hgN x hx

theorem GLAPPrimeCoreOf_le_of_isSubnormal_sub {p : ℕ} [Finite X] (hp : p.Prime)
    {L C : Subgroup X} (h : IsSubnormal L C) :
    GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (GLAPPrimeCoreOf_le_of_normal_sub hp hHM hn).trans ih


end CFSG.HardMathSupport.Timmesfeld.Proving

end
