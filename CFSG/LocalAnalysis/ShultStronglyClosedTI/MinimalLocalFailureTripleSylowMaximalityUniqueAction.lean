module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityPointTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding
open CFSG.OrderReductions.UniqueInvolutionAction

universe u v

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem unique_fixed_of_right_conjugate
    {Ω : Type v} [MulAction G Ω] {z x g : G}
    (hz : ∃! alpha : Ω, z • alpha = alpha)
    (hx : rightConjugateElem z g = x) :
    ∃! alpha : Ω, x • alpha = alpha := by
  obtain ⟨alpha, hza, huniq⟩ := hz
  have hconj : g⁻¹ * z * g = x := hx
  refine ⟨g⁻¹ • alpha, ?_, ?_⟩
  · rw [← hconj]
    simp only [mul_smul, smul_inv_smul, hza]
  · intro omega hfix
    have hzfix : z • (g • omega) = g • omega := by
      have h := congrArg (fun a : Ω => g • a) hfix
      rw [← hconj] at h
      simpa only [mul_smul, smul_inv_smul] using h
    have heq := huniq (g • omega) hzfix
    simpa only [inv_smul_smul] using congrArg (fun a : Ω => g⁻¹ • a) heq


omit [Finite G] in
theorem normal_join_action_transitive
    {Ω : Type v} [MulAction G Ω] (L R : Subgroup G)
    (hLtrans : MulAction.IsPretransitive L Ω) :
    MulAction.IsPretransitive (L ⊔ R : Subgroup G) Ω := by
  constructor
  intro a b
  obtain ⟨l, hl⟩ := hLtrans.exists_smul_eq a b
  exact ⟨⟨l.val, (le_sup_left : L ≤ L ⊔ R) l.property⟩, hl⟩


end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
