module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureLink
public import CFSG.ClassicalInvolution.Reduction
import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn conj_mem_oddCoreIn)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

section SimplyLaced


theorem FrameGenerationModO.cover (hΩ : InClass p f Ω) (hS : S ⊆ Ω) {a : G}
    (h : FrameGenerationModO Ω S a) : FrameCoversModO Ω S a := by
  intro L hL
  by_contra hno
  push Not at hno
  set Y := centralizingLayer Ω {a} with hY
  have hLY : L ≤ Y := le_centralizingLayer hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hclaim : ∀ x ∈ L, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn Y := by
    intro x hx y hy
    have hxY : x ∈ Y := hLY hx
    let C : Subgroup ↥Y :=
      (Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hxY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))).comap
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
    have hC : ∀ t : ↥Y, t ∈ C ↔ x * (t : G) * x⁻¹ * (t : G)⁻¹ ∈ oddCoreIn Y := by
      intro t
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, eq_comm]
      exact mk_comm_eq_iff hxY t.2
    have hO : oddCoreIn Y ≤ C.map Y.subtype := by
      rintro _ ⟨w, hw, rfl⟩
      have hwO : (w : G) ∈ oddCoreIn Y := ⟨w, hw, rfl⟩
      exact ⟨w, (hC w).mpr ((oddCoreIn Y).mul_mem (conj_mem_oddCoreIn hxY hwO)
        ((oddCoreIn Y).inv_mem hwO)), rfl⟩
    have hKle : ∀ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) → K ≤ C.map Y.subtype := by
      intro K hK hKa k hk
      have hkY : k ∈ Y := le_centralizingLayer ⟨hS hK, hKa⟩ hk
      exact ⟨⟨k, hkY⟩, (hC ⟨k, hkY⟩).mpr (hno K hK hKa x hx k hk), rfl⟩
    have hYle : Y ≤ C.map Y.subtype :=
      h.trans (sup_le hO (iSup₂_le fun K hK => iSup_le fun hKa => hKle K hK hKa))
    obtain ⟨t, ht, rfl⟩ := hYle hy
    exact (hC t).mp ht
  have hcomm : commutator ↥L ≤ (oddCoreIn Y).subgroupOf L := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_subgroupOf]
    exact hclaim x x.2 y (hLY y.2)
  have hzc : (⟨z, hz.mem⟩ : ↥L) ∈ commutator ↥L := by
    rw [hz.perfect.commutator_eq_top]
    exact Subgroup.mem_top _
  have hzO : z ∈ oddCoreIn Y := hcomm hzc
  have hz1 := eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn Y) hzO (sq_eq_one hz)
  have := hz.orderOf_eq_two
  rw [hz1, orderOf_one] at this
  exact absurd this (by norm_num)


end SimplyLaced

section Toral

variable {F : Type*} [Field F] {E : Subgroup G}

omit [Finite G] in
private theorem comm_of_sq_eq_one {x y : G} (hE : ∀ z ∈ E, z * z = 1) (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h1 := hE (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]


end Toral

section Connected

omit [Finite G] in
theorem omegaConnected_of_deltaConnected {J : Subgroup G}
    (h : CFSG.ClassicalInvolution.DeltaConnected J) :
    OmegaConnected (CFSG.ClassicalInvolution.conjugateSet J) := by
  intro L hL L' hL'
  have hle : CFSG.ClassicalInvolution.commutingAdj J ≤
      fun M N : Subgroup G => N ∈ CFSG.ClassicalInvolution.conjugateSet J ∧ Commutes M N :=
    fun _ _ hMN => ⟨hMN.2.1, fun x hx y hy => hMN.2.2.2 x hx y hy⟩
  exact Relation.ReflTransGen.mono hle L L' (h L hL L' hL')

omit [Finite G] in
theorem omegaConnected_range_conjSub {J : Subgroup G}
    (h : CFSG.ClassicalInvolution.DeltaConnected J) :
    OmegaConnected (Set.range fun g : G => conjSub g J) := by
  have hset : Set.range (fun g : G => conjSub g J) = CFSG.ClassicalInvolution.conjugateSet J := by
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [conjSub]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [conjSub]⟩
  rw [hset]
  exact omegaConnected_of_deltaConnected h

end Connected

end CFSG.ClassicalInvolution.Generic.DeltaClosure
