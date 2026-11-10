module

public import CFSG.Quasithin.Background.HLUBlocks
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Quasithin.AppendixH.H16.SextetPack

public section

namespace CFSG.ASVolI.H16

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU
  CFSG.Quasithin.H.LU24

@[expose] def sxTC : List ℕ := [1547, 790, 126, 38, 1430, 310, 598, 1268, 592, 1168, 1300]

theorem sxTC_eq : matOf 11 (actC11 sxTArr) = sxTC := by
  decide +kernel

theorem sxTC_lt : ∀ c ∈ sxTC, c < 2 ^ 11 := by
  decide +kernel

@[expose] def ksConjT (i : ℕ) : ℕ := [30, 57, 58, 41, 9, 43].getD i 0

@[expose] def ksConjTInv (i : ℕ) : ℕ := [46, 40, 29, 62, 10, 24].getD i 0

theorem ks6_conj_t : ∀ i < 6,
    cArr (cArr sxTArr (ks6Arr i)) sxTInv =
        wArr ((List.range 6).map ks6Arr) (subW (ksConjT i)) ∧
      cArr (cArr sxTInv (ks6Arr i)) sxTArr =
        wArr ((List.range 6).map ks6Arr) (subW (ksConjTInv i)) :=
  SxPack.conj_of_conjB ksConjT ksConjTInv (by decide +kernel)

@[expose] def sTP : Equiv.Perm (Fin 6) :=
  perm6 ![0, 3, 4, 5, 2, 1] ![0, 5, 4, 1, 2, 3] (by decide)

theorem sign_sTP : Equiv.Perm.sign sTP ≠ 1 := by
  decide

theorem th_t_ok : ∀ m ∈ combos uSBasis, ∀ i : Fin 6,
    bvec 6 (actM thC (actM sxTC m)) i =
      bvec 6 (actM thC m) (sTP⁻¹ i) + bvec 6 (actM thC m) (sTP⁻¹ 5) := by
  decide +kernel


end CFSG.ASVolI.H16
