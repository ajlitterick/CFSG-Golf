module

public import CFSG.Milestones.ASVolI.J1
public import CFSG.Quasithin.Recognition.RuTypeSetting
public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK.RuType


namespace BridgeTwo

open CFSG.Open
open scoped MatrixGroups

local notation "F4c" => CFSG.Quasithin.RuType.F4
local notation "SigmaL2" => CFSG.Quasithin.RuType.SigmaL2F4

section Vocabulary

variable {G : Type} [Group G]

theorem centerOf_eq (W : Subgroup G) :
    CFSG.ASVolI.ChIJK.centerOf W = CFSG.Quasithin.centerOf W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hxW, hxc⟩
    refine ⟨⟨x, hxW⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc w w.2)


theorem conjClosure_eq (L Y : Subgroup G) :
    CFSG.ASVolI.ChIJK.conjClosure L Y = CFSG.Quasithin.conjClosure L Y := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rintro _ ⟨l, hl, rfl⟩
    exact CFSG.Quasithin.mem_conjClosure (Y.inv_mem hy) hl
  · rw [CFSG.Quasithin.conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, z, hz, rfl⟩
    exact (le_iSup₂ (f := fun y (_ : y ∈ Y) => CFSG.conjugate L y) h⁻¹ (Y.inv_mem hh))
      ⟨z, hz, by simp⟩


end Vocabulary

section Basic

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}


theorem S_le_T (h : RuType G L V T) : SRu L ≤ T := by
  have hTL : IsSylowTwoIn (T ⊓ L) L := by
    have h2 := h.T_choice
    rwa [← h.L_eq] at h2
  obtain ⟨hle, hp, hidx⟩ := hTL
  have hP : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  let P : Sylow 2 ↥L := IsPGroup.toSylow hP hidx
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hcore : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).le_sylow_of_normal P
  have hmap := Subgroup.map_mono (f := L.subtype) hcore
  have e : (P : Subgroup ↥L).map L.subtype = T ⊓ L := Subgroup.map_subgroupOf_eq_of_le hle
  rw [e] at hmap
  exact hmap.trans inf_le_left


end Basic

section Field

open CFSG.Quasithin.RuType (frobF4 frobF4_apply frobF4_frobF4 frobVec)
open CFSG.Quasithin.RuType.Sigma (zmod2_cases)

noncomputable def e4 : F4 ≃+* F4c :=
  haveI : Fintype F4 := Fintype.ofFinite F4
  FiniteField.ringEquivOfCardEq (by
    have h1 : Fintype.card F4 = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [h1, CFSG.Quasithin.RuType.F4.card])


@[expose] noncomputable def E4 : (Fin 2 → F4) ≃+ (Fin 2 → F4c) :=
  AddEquiv.piCongrRight fun _ => e4.toAddEquiv

@[simp] theorem E4_apply (v : Fin 2 → F4) (i : Fin 2) : E4 v i = e4 (v i) := rfl

end Field

section Sigma

open CFSG.Quasithin.RuType (frobF4 frobVec sigmaAct SigmaL2F4)
open CFSG.Quasithin.RuType.Sigma (sigmaAct_mk sigmaAct_mul sigmaAct_one eq_one_of_sigmaAct_eq)


end Sigma

section Assembly

open CFSG.Quasithin.RuType (sigmaAct SigmaL2F4)


end Assembly

end BridgeTwo

section Main

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}

open CFSG.Open
open CFSG.Quasithin.RuType (sigmaAct SigmaL2F4)

local notation "F4c" => CFSG.Quasithin.RuType.F4


end Main

end CFSG.ASVolI.ChIJK.RuType
