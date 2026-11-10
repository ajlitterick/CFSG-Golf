module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFact

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F]

theorem apply_mem_blockTorus_of_mem_modelToG (e : L ≃* LinearFlag.projectiveSL n K)
    {I : Finset (Fin n)} {d : G} (hd : d ∈ modelToG e (blockTorus (K := K) I)) :
    e ⟨d, modelToG_le e _ hd⟩ ∈ blockTorus (K := K) I := by
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hd
  simpa using hy

theorem pieceCore_eq_map_of_conjDiag [Finite G] [Finite F] (e : L ≃* LinearFlag.projectiveSL n K)
    (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ := by
  set T := modelToG e (blockTorus (K := K) I)
  let f : T → blockTorus (K := K) I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_blockTorus_of_mem_modelToG e d.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [f]
  have hα : ∀ (d : T) (x : blockSpecialLinear (K := F) N),
      Φ (conjDiag ι N (blockTorusLift (f d)) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (blockTorusLift_mem (f d)) x, proj_torusDiagSL_blockTorusLift]
    have hd : ((e.symm ((f d : blockTorus (K := K) I) : LinearFlag.projectiveSL n K) : L) : G) =
        (d : G) := by
      simp [f]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le Φ hker hXI hrange
    (fun d => conjDiag ι N (blockTorusLift (f d))) hα]
  congr 1
  rw [show (fixAll fun d : T => conjDiag ι N (blockTorusLift (f d))) =
      fixAll (fun d : blockTorus (K := K) I => conjDiag ι N (blockTorusLift d)) from
    fixAll_comp_of_surjective (fun d : blockTorus (K := K) I => conjDiag ι N (blockTorusLift d)) hf]
  refine perfectCore_fixAll_conjDiag ι hIN _ blockTorusLift_mem (fun i hi j hj hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := hsep i hi j hj hij hIJ
  exact exists_blockTorusLift_ne hc hcij

theorem pieceCore_eq_map_of_conjDiag_of_notMem [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ :=
  pieceCore_eq_map_of_conjDiag e ι hIN
    (fun _ hi _ hj hij hIJ => exists_mem_blockTorusParam_ne_of_notMem hIN hk hκ hi hj hij hIJ)
    hperf hXI Φ hker hrange hΦ


end CFSG.SeitzReduction.LinearPilot
