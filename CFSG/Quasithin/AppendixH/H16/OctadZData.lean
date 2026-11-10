module

public import CFSG.Quasithin.AppendixH.H16.OctadBetaMask

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def wz0Basis : List ℕ := [3, 5, 9, 17, 160, 352, 512]


@[expose] def dTab : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  #[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 21, 20, 23, 22],
  #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23],
  #[2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
  #[2, 3, 0, 1, 7, 6, 5, 4, 9, 8, 11, 10, 12, 13, 14, 15, 17, 16, 19, 18, 20, 21, 22, 23],
  #[3, 2, 1, 0, 6, 7, 4, 5, 8, 9, 10, 11, 13, 12, 15, 14, 17, 16, 19, 18, 20, 21, 22, 23],
  #[3, 2, 1, 0, 6, 7, 4, 5, 9, 8, 11, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 20, 23, 22],
  #[4, 5, 7, 6, 0, 1, 3, 2, 8, 9, 11, 10, 12, 13, 15, 14, 16, 17, 19, 18, 20, 21, 23, 22],
  #[4, 5, 7, 6, 0, 1, 3, 2, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23],
  #[5, 4, 6, 7, 1, 0, 2, 3, 8, 9, 11, 10, 12, 13, 15, 14, 17, 16, 18, 19, 21, 20, 22, 23],
  #[5, 4, 6, 7, 1, 0, 2, 3, 9, 8, 10, 11, 13, 12, 14, 15, 16, 17, 19, 18, 20, 21, 23, 22],
  #[7, 6, 4, 5, 2, 3, 1, 0, 8, 9, 11, 10, 13, 12, 14, 15, 16, 17, 19, 18, 21, 20, 22, 23],
  #[7, 6, 4, 5, 2, 3, 1, 0, 9, 8, 10, 11, 12, 13, 15, 14, 17, 16, 18, 19, 20, 21, 23, 22],
  #[6, 7, 5, 4, 3, 2, 0, 1, 8, 9, 11, 10, 13, 12, 14, 15, 17, 16, 18, 19, 20, 21, 23, 22],
  #[6, 7, 5, 4, 3, 2, 0, 1, 9, 8, 10, 11, 12, 13, 15, 14, 16, 17, 19, 18, 21, 20, 22, 23]
]

@[expose] def dArr (u : ℕ) : Array ℕ := dTab.getD u idArr


theorem dArr_ok : ∀ u < 16, InvPairOK 24 (dArr u) (dArr u) = true := by decide +kernel

theorem dArr_aut : ∀ u < 16, autArrOK (dArr u) (dArr u) = true := by decide +kernel


theorem dArr_fix_octad_iff : ∀ u < 16, ((∀ i < 8, (dArr u)[i]! = i) ↔ u < 2) := by decide +kernel


theorem dArr_triv_wz_mod : ∀ u < 16, ∀ m ∈ combos wz0Basis, actC11 (dArr u) m ^^^ m ∈ combos oct5Basis := by
  decide +kernel

end CFSG.ASVolI.H16
