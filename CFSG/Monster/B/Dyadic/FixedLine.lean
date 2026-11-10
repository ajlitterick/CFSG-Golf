module

public import CFSG.Monster.B.Dyadic.Data
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate3101

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  generalize a = b
  revert b
  decide

theorem vec_add_self {n : ℕ} (z : Fin n → ZMod 2) : z + z = 0 :=
  funext fun i => zmod2_add_self (z i)


theorem fvec_fixed (g : Fin 26) : fvec ᵥ* Cmat g = fvec :=
  Certificates.certificate3101.1 g


theorem rank_Q0 : (Qmat 0 - 1).rank = 1860 :=
  Certificates.certificate3101.2.2.2.1

theorem rank_Q25 : (Qmat 25 - 1).rank = 2862 :=
  Certificates.certificate3101.2.2.2.2.1


theorem Q25_ne_one : Qmat 25 ≠ 1 := by
  intro h
  have := rank_Q25
  rw [h, sub_self, Matrix.rank_zero] at this
  exact absurd this (by norm_num)

end CFSG.Monster.B.Dyadic

end
