module

public import CFSG.Quasithin.Background.HLUCode24
public import CFSG.Quasithin.AppendixH.Common.OctadBasic
public import CFSG.Quasithin.Background.H16TwoM22PfA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def oct1Basis : List ℕ := [3]


@[expose] def octV1 : Subgroup W11 := maskSub 11 oct1Basis


@[expose] noncomputable def ko11 (t : Fin 16) : MulAut W11 :=
  rhoC11 AutPerm le_rfl ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩

theorem ko11_toW (t : Fin 16) (m : ℕ) :
    ko11 t (toW 11 m) = toW 11 (actC11 (koArr t) m) :=
  rhoC11_toW AutPerm le_rfl ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩
    (hasArr_permOfArr (koArr_ok t).1) m

theorem ko11_mem_imgCd_fixO (t : Fin 16) : ko11 t ∈ imgCd fixO :=
  ⟨⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩,
    Subgroup.mem_subgroupOf.2 ((mem_fixO_iff _).2 ⟨t, rfl⟩), rfl⟩

theorem mem_imgCd_fixO_iff (φ : MulAut W11) : φ ∈ imgCd fixO ↔ ∃ t : Fin 16, φ = ko11 t := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hγ)
    refine ⟨t, ?_⟩
    have hγt : γ = ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ := Subtype.ext ht
    rw [hγt]
    rfl
  · rintro ⟨t, rfl⟩
    exact ko11_mem_imgCd_fixO t

theorem actC11_ko_three : ∀ t : Fin 16, actC11 (koArr t) 3 = 3 := by decide +kernel


theorem fixV_imgCd_fixO : fixV (imgCd fixO) = octV1 := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rcases fix_koRho11 v fun i => mem_fixV.1 hv _ (ko11_mem_imgCd_fixO (koT i)) with h | h
    · rw [h]
      exact octV1.one_mem
    · rw [h]
      exact toW_mem_maskSub (mem_combos_of_mem (by simp [oct1Basis]))
  · rintro v ⟨m, hm, rfl⟩ φ hφ
    obtain ⟨t, rfl⟩ := (mem_imgCd_fixO_iff φ).1 hφ
    have h : m = 0 ∨ m = 3 := by simpa [oct1Basis, combos] using hm
    rcases h with rfl | rfl
    · rw [toW_zero]
      exact map_one _
    · rw [ko11_toW, actC11_ko_three]


end CFSG.ASVolI.H16
