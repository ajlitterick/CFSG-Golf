module

public import CFSG.GH74.M12.HypLocal

public section

namespace CFSG.GH74.M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.M12.Hyp CFSG.Blueprint

theorem factorization_192_two : Nat.factorization 192 2 = 6 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (192 : ℕ) = 2 ^ 6 * 3 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]


theorem Jelt_mem_bfS' : Jelt ∈ bfS' := bfJ_mem_bfS


theorem bfS'_comm_Jelt
    {s : G12} (hs : s ∈ bfS') : s * Jelt = Jelt * s := by
  obtain ⟨x, hx⟩ := tauC_real (tbl s.1) (BT_sub_HT _ (mem_bfS_iff.1 hs))
  have h1 : x.1.1 = s.1 := tbl_injective hx
  have h2 := mem_CJ.1 x.2
  rw [h1] at h2
  exact Subtype.ext h2.symm


end CFSG.GH74.M12
