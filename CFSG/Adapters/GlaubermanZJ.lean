module

public import CFSG.Open.GlaubermanZJCharacteristicMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
import CFSG.GroupTheory.SylowNaturalCharacteristic
import CFSG.GroupTheory.PCore.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.Open.Catalog

public section

namespace CFSG
namespace Adapters

open scoped Pointwise commutatorElement

section Bridges

variable {G : Type*} [Group G]


theorem leanEval_thompsonSubgroup_eq (S : Subgroup G) :
    CFSG.Open.thompsonSubgroup S = CFSG.thompsonSubgroup (G := G) S :=
  rfl

theorem mulAut_smul_eq_map (ψ : MulAut G) (H : Subgroup G) :
    ψ • H = H.map ψ.toMonoidHom := by
  ext x
  simp [Subgroup.pointwise_smul_def]


theorem map_mem_thompsonAbelianSubgroups {H : Type*} [Group H] (e : G ≃* H)
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    A.map e.toMonoidHom ∈ thompsonAbelianSubgroups (G := H) (P.map e.toMonoidHom) := by
  obtain ⟨hAP, hAc, hAm⟩ := hA
  refine ⟨Subgroup.map_mono hAP, inferInstance, ?_⟩
  intro B hB hBc
  have hBP : B.map e.symm.toMonoidHom ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hB hy
    simpa using hz
  calc
    Nat.card B = Nat.card (B.map e.symm.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := B) e.symm.injective).symm
    _ ≤ Nat.card A := hAm _ hBP inferInstance
    _ = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := A) e.injective).symm

theorem map_symm_map {H : Type*} [Group H] (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

theorem thompsonSubgroup_map_mulEquiv {H : Type*} [Group H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
      thompsonSubgroup (G := H) (P.map e.toMonoidHom) :=
  map_thompsonSubgroup_of_injective e.toMonoidHom P (e.injective.comp P.subtype_injective)

theorem thompsonCenter_map_mulEquiv {H : Type*} [Group H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonCenter (G := G) P).map e.toMonoidHom =
      thompsonCenter (G := H) (P.map e.toMonoidHom) :=
  map_thompsonCenter_of_injective e.toMonoidHom P (e.injective.comp P.subtype_injective)


end Bridges


end Adapters
end CFSG
