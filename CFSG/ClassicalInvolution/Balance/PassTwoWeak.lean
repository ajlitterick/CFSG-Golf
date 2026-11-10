module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceWeakFrame
public import CFSG.ClassicalInvolution.Balance.SL2
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.SmallCases.FrameRank

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

section Data

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}


variable [Finite G]


end Data

section TheoremQ

variable {F : Type*} [Field F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem WeakMember.data {K : Subgroup G} {z : G} (h : WeakMember F K z) [Finite F]
    (h4 : 4 ≤ Nat.card F) :
    commutator K = ⊤ ∧ K ≠ ⊥ ∧ CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) := by
  have hm := IsInvolutionMember.of_weakMember h h4
  refine ⟨hm.perfect, ?_, hm.quasisimple⟩
  have hc := h.isCentralInvolution
  intro hbot
  have := hc.mem
  rw [hbot, Subgroup.mem_bot] at this
  exact hc.ne_one this


end TheoremQ

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem classicalInvolutionOddCore_conjSub_eq_bot {L : Subgroup G}
    (h : classicalInvolutionOddCore L = ⊥) (n : G) :
    classicalInvolutionOddCore (conjSub n L) = ⊥ := by
  let e : L ≃* conjSub n L :=
    L.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
      classicalInvolutionOddCore (conjSub n L) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [← hO, h, Subgroup.map_bot]

theorem exactMembers_of_isQuasisimple (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {L₀ : Subgroup G} (hL₀ : L₀ ∈ Ω)
    (hq : CFSG.Open.IsQuasisimple L₀) : ExactMembers Ω := by
  obtain ⟨z, hz⟩ := hΩ.classical L₀ hL₀
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hO₀ : classicalInvolutionOddCore L₀ = ⊥ :=
    (classicalInvolutionOddCore_eq_bot_of_isQuasisimple hq hp2 hf h9 e).1
  obtain ⟨K, -, hall⟩ := hsingle
  obtain ⟨g₀, hg₀⟩ := hall L₀ hL₀
  intro L hL
  obtain ⟨g, hg⟩ := hall L hL
  have hK : K = conjSub g₀⁻¹ L₀ := by rw [hg₀, conjSub_inv_conjSub]
  have hLeq : L = conjSub (g * g₀⁻¹) L₀ := by rw [conjSub_mul, ← hK, hg]
  rw [hLeq]
  exact classicalInvolutionOddCore_conjSub_eq_bot hO₀ _


end Exact

end CFSG.ClassicalInvolution.Balance
