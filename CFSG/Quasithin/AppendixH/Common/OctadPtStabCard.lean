module

public import CFSG.Quasithin.AppendixH.Common.OctadOrbit
public import CFSG.Quasithin.AppendixH.Common.OctadPtStab
public import CFSG.Quasithin.Background.H16TwoM22PfA

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code
open CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def octad0 : Finset (Fin 24) := Finset.univ.filter fun i => (i : ℕ) < 8

theorem isOctad_octad0 : IsOctad octad0 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · have hbvec : ∀ i : Fin 24, bvec 24 255 i = if (i : ℕ) < 8 then 1 else 0 := by
      intro i
      have htb : (255 : ℕ).testBit (i : ℕ) = decide ((i : ℕ) < 8) := by
        rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp only [bvec, htb]
      by_cases hi : (i : ℕ) < 8 <;> simp [hi]
    rw [mem_golayC_iff']
    have h : Multiplicative.toAdd (eY octad0) = bvec 24 255 := by
      funext i
      rw [toAdd_eY, hbvec i]
      by_cases hi : (i : ℕ) < 8
      · simp [octad0, hi]
      · simp [octad0, hi]
    rw [h]
    exact (bvec_mem_C_iff 255).2 (by decide +kernel)

theorem octFix_octad0 : octFix octad0 = CFSG.Quasithin.H.Mathieu.H16Pf.fixO := by
  ext g
  simp only [mem_octFix_iff, M24g, CFSG.Quasithin.H.Mathieu.H16Pf.fixO]
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, fun i hi => hfix i (by simpa [octad0] using hi)⟩
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, fun i hi => hfix i (by simpa [octad0] using hi)⟩

private theorem card_fixO_eq : Nat.card CFSG.Quasithin.H.Mathieu.H16Pf.fixO = 16 := by
  have hinj : Function.Injective koPerm := by
    intro s t h
    have hs := koPerm_eight s
    rw [h, koPerm_eight t] at hs
    exact Fin.ext (by omega)
  have h : (CFSG.Quasithin.H.Mathieu.H16Pf.fixO : Set S24) = Set.range koPerm := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixO_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective hinj,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem card_octFix0 : Nat.card (octFix octad0) = 16 := by
  rw [octFix_octad0, card_fixO_eq]

theorem card_octFix {O : Finset (Fin 24)} (hO : IsOctad O) :
    Nat.card (octFix O) = 16 := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octad0 hO
  rw [← hσO, octFix_smul hσ]
  rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]
  exact card_octFix0


end CFSG.ASVolI.AppH
