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


end CFSG.ASVolI.AppH
