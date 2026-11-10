module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Leaves
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem exists_setup1D [Finite G] (x : G) (K : Subgroup G) : ∃ T : Subgroup G, Setup1D x K T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_isSylowOf (G := G) 2 (NxK x K)
  have hNC : NxK x K ≤ centralizer ({x} : Set G) := inf_le_left
  obtain ⟨T, hS₀T, hTC, hTp, hTidx⟩ := P34.exists_sylow_ge (N := centralizer ({x} : Set G))
    (hS₀.le.trans hNC) hS₀.isPGroup
  refine ⟨T, isSylowOf_iff.2 ⟨hTC, hTp, hTidx⟩, ?_⟩
  have hTN : IsPGroup 2 ↥(T ⊓ NxK x K) := hTp.to_inf_left
  have heq : T ⊓ NxK x K = S₀ := hS₀.eq_of_le (le_inf hS₀T hS₀.le) inf_le_right hTN
  rw [heq]
  exact hS₀

theorem kBar_model_of_U2 [Finite G] (hG : C3Hyp G) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    {x y : G} {K : Subgroup G} (hu2 : Is2TerminalU2Triple x y K) :
    HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, hU⟩ := h102 G hG x y K hu2.1
  rcases hU with h | h | ⟨h34, hab, hcard⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ⟨h34, hab, hcard⟩ (hL34 G hG.gen4 x K hu2.1.1.1 hu2.1.1.2)


end CFSG.GH74.GLS.C3.Layer1.Thm1
