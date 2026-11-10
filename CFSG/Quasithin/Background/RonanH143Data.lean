module

public import CFSG.Quasithin.Background.RonanH143Vocab
public import CFSG.Quasithin.Background.HModChk
public import CFSG.Quasithin.Background.H16TwoM22PfA
public import CFSG.Quasithin.Background.H16TwoM22PfB

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk

@[expose] def zMask : Fin 5 → ℕ := ![60, 49920, 15360, 12779520, 3932160]

@[expose] def Zq (i : Fin 5) : Finset (Fin 24) := maskSet (zMask i)


@[expose] def Qstd : Finset (Finset (Fin 24)) := Finset.univ.image Zq


theorem Zq_injective : Function.Injective Zq := by
  intro i j h
  have : ∀ i j : Fin 5, Zq i = Zq j → i = j := by decide +kernel
  exact this i j h


theorem mem_Qstd_iff (T : Finset (Fin 24)) : T ∈ Qstd ↔ ∃ i, Zq i = T := by
  simp [Qstd]


@[expose] def sig1 : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 3, 2, 4]

@[expose] def sig2 : Equiv.Perm (Fin 5) := Equiv.swap 2 3


end CFSG.Quasithin.RonanH143
