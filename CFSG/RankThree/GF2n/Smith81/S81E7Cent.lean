module

public import CFSG.RankThree.GF2n.Smith81.S81E7Lam
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7Psi_pinnedElt' {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K) :
    e7Psi K (pinnedElt .E7 β c) = e7Data_valid.xm K β c :=
  (e7Equiv (K := K)).symm_apply_eq.2 (Subtype.ext (CFSG.SeitzReduction.E8Pilot.coe_e7Isogeny_xm hβ c).symm)


theorem perpRoots_eq : EPilot.perpRoots .E7 = Perp := by
  have hn : highNode .E7 = node1 := by decide
  ext β
  rw [EPilot.mem_perpRoots_iff, perp_iff, hn]

theorem Lam_eq_map : Lam K =
    ((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype := by
  apply le_antisymm
  · rw [Lam, Subgroup.closure_le]
    rintro g ⟨β, hβ, c, rfl⟩
    have hβR : IsRoot .E7 β := (perp_iff.1 hβ).1
    have hβP : β ∈ EPilot.perpRoots .E7 := by
      rw [perpRoots_eq]
      exact hβ
    have hmem : pinnedElt .E7 β c ∈ EPilot.perpLevi .E7 K :=
      EPilot.pinnedElt_mem_perpLevi hβP c
    have h1 : e7Psi K (pinnedElt .E7 β c) ∈ (EPilot.perpLevi .E7 K).map (e7Psi K) :=
      Subgroup.mem_map_of_mem (e7Psi K) hmem
    have h2 := Subgroup.mem_map_of_mem (e7Data_valid.minGroup K).subtype h1
    rw [e7Psi_pinnedElt' hβR c] at h2
    exact h2
  · obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥(adjointGroup .E7 K),
        ∀ x, x ∈ M ↔ (e7Data_valid.minGroup K).subtype (e7Psi K x) ∈ Lam K :=
      ⟨((Lam K).comap (e7Data_valid.minGroup K).subtype).comap (e7Psi K), fun x => Iff.rfl⟩
    have hspan : CFSG.Blueprint.Chevalley.rootSpan .E7 K (EPilot.perpRoots .E7) ≤
        M.map (adjointGroup .E7 K).subtype := by
      unfold CFSG.Blueprint.Chevalley.rootSpan
      refine iSup₂_le fun β hβ => ?_
      unfold CFSG.Blueprint.Chevalley.rootSubgroup
      rw [Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      have hβP : β ∈ Perp := by
        rw [← perpRoots_eq]
        exact hβ
      have hβR : IsRoot .E7 β := (perp_iff.1 hβP).1
      have hMem : pinnedElt .E7 β c ∈ M := by
        rw [hM, e7Psi_pinnedElt' hβR c]
        exact xu_mem_Lam hβP c
      exact Subgroup.mem_map_of_mem (adjointGroup .E7 K).subtype hMem
    have hle : EPilot.perpLevi .E7 K ≤ M := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hspan (Subgroup.mem_subgroupOf.1 hx))
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    rintro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact (hM x).1 (hle hx)


theorem isSimpleGroup_Lam : IsSimpleGroup (Lam K) := by
  have hD : IsSimpleGroup (EPilot.perpLevi .E7 K) :=
    CFSG.SeitzReduction.E7Pilot.isSimpleGroup_perpLevi_E7 (K := K)
  have hinj : Function.Injective (e7Psi K) := (e7Equiv (K := K)).symm.injective
  have e1 : ↥(EPilot.perpLevi .E7 K) ≃* ↥((EPilot.perpLevi .E7 K).map (e7Psi K)) :=
    (EPilot.perpLevi .E7 K).equivMapOfInjective (e7Psi K) hinj
  have e2 : ↥((EPilot.perpLevi .E7 K).map (e7Psi K)) ≃*
      ↥(((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype) :=
    ((EPilot.perpLevi .E7 K).map (e7Psi K)).equivMapOfInjective
      (e7Data_valid.minGroup K).subtype Subtype.val_injective
  have e3 : ↥(((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype) ≃*
      ↥(Lam K) :=
    MulEquiv.subgroupCongr Lam_eq_map.symm
  exact @MulEquiv.isSimpleGroup _ _ _ _ hD (e1.trans (e2.trans e3)).symm

end CFSG.RankThree.GF2n.Smith81.E7Model
