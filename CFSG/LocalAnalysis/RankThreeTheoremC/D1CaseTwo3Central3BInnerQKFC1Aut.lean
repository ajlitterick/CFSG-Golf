module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAutThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
public import CFSG.GH74.KGroups.A6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34
import CFSG.Quasithin.Background.L34OutFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

namespace InnerQ.KFC1

@[expose] def SqInner (K : Type*) [Group K] (T : Subgroup K) : Prop :=
  ∀ f : MulAut K, (∀ b ∈ T, f b = b) → ∃ t ∈ T, f ^ 2 = MulAut.conj t

variable {K K' : Type*} [Group K] [Group K'] {T : Subgroup K}


theorem SqInner.map (e : K ≃* K') (h : SqInner K T) : SqInner K' (T.map e.toMonoidHom) := by
  intro f hf
  set g : MulAut K := (e.trans f).trans e.symm with hg
  have hgT : ∀ b ∈ T, g b = b := fun b hb => by
    have := hf (e b) ⟨b, hb, rfl⟩
    simp [hg, this]
  obtain ⟨t, ht, hgt⟩ := h g hgT
  refine ⟨e t, ⟨t, ht, rfl⟩, ?_⟩
  ext y
  have h1 := congrArg (fun φ : MulAut K => φ (e.symm y)) hgt
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, hg, MulEquiv.trans_apply] at h1
  have h2 := congrArg e h1
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv] at h2
  simpa [pow_two, MulAut.mul_apply, MulAut.conj_apply] using h2

theorem SqInner.of_equiv {T' : Subgroup K'} (e : K ≃* K') (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (h : SqInner K T) : SqInner K' T' := by
  have : T' = T.map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, hT, MulEquiv.apply_symm_apply]
  exact this ▸ h.map e


end InnerQ.KFC1

end CFSG.LocalAnalysis.RankThreeTheoremC
