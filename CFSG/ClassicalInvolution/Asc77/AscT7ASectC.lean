module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectB
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal2
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

section Facts

variable (h : Hyp21 p f Ω K K' z u J t W)
include h

omit [IsSimpleGroup G] in
theorem Hyp21.tz_sq : (t * z) * (t * z) = 1 := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp h.std.stand.hyp
  calc (t * z) * (t * z) = t * (z * t) * z := by group
    _ = t * (t * z) * z := by rw [hzt]
    _ = (t * t) * (z * z) := by group
    _ = 1 := by rw [h.ht.sq, h.std.hz.sq, one_mul]

omit [IsSimpleGroup G] in
theorem Hyp21.tz_ne_one : t * z ≠ 1 := by
  intro h1
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

theorem Hyp21.oddCore_centralizer_tz_comm (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({t * z} : Set G))) : n * z = z * n := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp h.std.stand.hyp
  have hE : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.ht.sq h.std.hz.sq h.ht.ne_one h.std.hz.ne_one
      h.twinFrameData.t_ne_z hzt.symm
  have hsub : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hA' : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ :=
    ((h3 G Ω K K' z u J t W h).2 _ hsub hE).trans hα
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hcA : t * z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ htA hzA
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({t, z} : Set G)) := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le (t * z) hcA
      (le_iSup_of_le h.tz_ne_one le_rfl))
  rw [hA'] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))

end Facts

section Main

variable (h : Hyp21 p f Ω K K' z u J t W)
include h


omit [IsSimpleGroup G] in
theorem Hyp21.mem_tqMembers_tz_J : J ∈ tqMembers Ω (t * z) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hRsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  refine (mem_tqMembers_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one h.tz_sq)).mpr
    ⟨h.hJ.1, T, hTsyl, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxt : x * t = t * x := (h.ht.commute_of_mem (hTsyl.1 hx)).symm
  have hxz : x * z = z * x := (hRT z hzR x hx).symm
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group


end Main


end CFSG.ClassicalInvolution.Asc77
