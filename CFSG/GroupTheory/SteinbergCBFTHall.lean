module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup

universe u

section General

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_eq_relIndex_sup_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) : H.relIndex K = H.relIndex (H ⊔ K) := by
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h
  have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (inf_le_right : H ⊓ K ≤ K)
  have h3 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (le_sup_left : H ≤ H ⊔ K)
  rw [h2, h3] at h1
  rw [← inf_relIndex_right]
  have hpos : 0 < Nat.card H * Nat.card ↥(H ⊓ K) := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  linarith


omit [Finite G] in
theorem pCore_map_of_surjective {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    {f : G →* G'} (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (pCore p G).map f = pCore p G' := by
  apply le_antisymm
  · exact le_sSup ⟨(pCore_normal (p := p) (G := G)).map f hf,
      (pCore_isPGroup (p := p) (G := G)).map f⟩
  · have hle : (pCore p G').comap f ≤ pCore p G :=
      le_sSup ⟨(pCore_normal (p := p) (G := G')).comap f,
        (pCore_isPGroup (p := p) (G := G')).comap_of_ker_isPGroup f hker⟩
    calc pCore p G' = ((pCore p G').comap f).map f := (map_comap_eq_self_of_surjective hf _).symm
      _ ≤ (pCore p G).map f := map_mono hle

omit [Finite G] in
theorem map_pCore_map_subtype {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    (f : G →* G') (H : Subgroup G) (hker : IsPGroup p ↥(f.ker ⊓ H)) :
    ((pCore p H).map H.subtype).map f = (pCore p (H.map f)).map (H.map f).subtype := by
  have hg : IsPGroup p (f.subgroupMap H).ker := by
    intro x
    have hx : ((x : H) : G) ∈ f.ker :=
      f.mem_ker.2 (congrArg Subtype.val ((f.subgroupMap H).mem_ker.1 x.2))
    obtain ⟨k, hk⟩ := hker ⟨x, mem_inf.2 ⟨hx, x.1.2⟩⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg (fun y : ↥(f.ker ⊓ H) => (y : G)) hk
  rw [← pCore_map_of_surjective (f.subgroupMap_surjective H) hg, map_map, map_map]
  rfl


end General

section Main


end Main

end CFSG.GroupTheory.FT63ChII
