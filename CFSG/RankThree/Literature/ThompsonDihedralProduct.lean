module

public import CFSG.RankThree.Literature.ThompsonDihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.CharacterTheory.Semidihedral.Principal.ThreeCentralizerSymmetricLocal
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.Literature

open Subgroup CFSG.OddInversion CFSG.RankThree.Literature.Thompson534

variable {G : Type*} [Group G]


theorem nonempty_closure_mulEquiv_dihedralGroup [Finite G] {ρ σ : G} (hσ : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ zpowers ρ) :
    Nonempty (closure {ρ, σ} ≃* DihedralGroup (orderOf ρ)) := by
  set H := closure ({ρ, σ} : Set G)
  have hρH : ρ ∈ H := subset_closure (by simp)
  have hσH : σ ∈ H := subset_closure (by simp)
  have hgen : (⊤ : Subgroup H) = zpowers ⟨ρ, hρH⟩ ⊔ zpowers ⟨σ, hσH⟩ := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      ← closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (D := H) ⟨ρ, hρH⟩ ⟨σ, hσH⟩
    hgen (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ
      (by
        obtain ⟨k, hk⟩ := (mem_zpowers_iff).mp hmem
        exact (mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h


end CFSG.RankThree.Literature
