module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFact
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCores

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono fixAll
  fixAll_comp_of_surjective centralizerPerfectCore_eq_map_of_le)

section General

variable {G : Type*} [Group G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} {n : ℕ}

theorem apply_mem_unitaryBlockTorus_of_mem_modelToG (e : L ≃* unitaryPSU h n)
    {I : Finset (Fin n)} {d : G} (hd : d ∈ modelToG e (unitaryBlockTorus h I)) :
    e ⟨d, modelToG_le e _ hd⟩ ∈ unitaryBlockTorus h I :=
  (coe_mem_modelToG_iff e (y := ⟨d, modelToG_le e _ hd⟩)).1 hd

theorem pieceCore_eq_map_of_conjTorus_of_sep [Finite G] (e : L ≃* unitaryPSU h n)
    {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ unitaryTorusParam h I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h I →
      ∀ x : blockSpecialLinear (K := K) N,
        Φ (conjTorus h N c x) = ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Φ x *
          ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map Φ := by
  have := h.finite
  set T := modelToG e (unitaryBlockTorus h I)
  let φ : T → unitaryBlockTorus h I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_unitaryBlockTorus_of_mem_modelToG e d.2⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [φ]
  have hα : ∀ (d : T) (x : blockSpecialLinear (K := K) N),
      Φ (conjTorus h N (unitaryBlockTorusLift h (φ d)) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (unitaryBlockTorusLift_mem h (φ d)) x,
      unitaryProj_torusDiagSU_unitaryBlockTorusLift]
    have hd : ((e.symm ((φ d : unitaryBlockTorus h I) : unitaryPSU h n) : L) : G) = (d : G) := by
      simp [φ]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le Φ hker hXI hrange
    (fun d => conjTorus h N (unitaryBlockTorusLift h (φ d))) hα]
  congr 1
  rw [show (fixAll fun d : T => conjTorus h N (unitaryBlockTorusLift h (φ d))) =
      fixAll (fun d : unitaryBlockTorus h I => conjTorus h N (unitaryBlockTorusLift h d)) from
    fixAll_comp_of_surjective
      (fun d : unitaryBlockTorus h I => conjTorus h N (unitaryBlockTorusLift h d)) hφ]
  refine perfectCore_fixAll_conjTorus h hIN _ (unitaryBlockTorusLift_mem h)
    (fun i hi j hj hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := hsep i hi j hj hij hIJ
  exact exists_unitaryBlockTorusLift_ne h hc hcij


end General

section Even

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} (e : L ≃* unitaryPSU h n)

@[expose] def TorusEquivariant (N I : Finset (Fin n)) (Φ : blockSpecialLinear (K := K) N →* G) :
    Prop :=
  ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h I →
    ∀ x : blockSpecialLinear (K := K) N,
      Φ (conjTorus h N c x) = ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Φ x *
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹

omit [Finite G] in
theorem TorusEquivariant.mono {N I I' : Finset (Fin n)} (hII' : I ⊆ I')
    {Φ : blockSpecialLinear (K := K) N →* G} (hΦ : TorusEquivariant e N I Φ) :
    TorusEquivariant e N I' Φ :=
  fun c hc x => hΦ c (unitaryTorusParam_anti h hII' hc) x

theorem pieceCore_eq_map_of_conjTorus {N I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card)
    (hIc : 2 ≤ Iᶜ.card) {X : Subgroup G} (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦ : TorusEquivariant e N I Φ) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map Φ :=
  pieceCore_eq_map_of_conjTorus_of_sep e hIN
    (fun _ _ _ _ hij hIJ => exists_mem_unitaryTorusParam_ne h hIc hij hIJ)
    (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hI2) hXI Φ hker hrange hΦ


end Even

end CFSG.SeitzReduction.UnitaryPilot
