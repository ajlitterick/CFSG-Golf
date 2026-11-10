
module

public import Certificates.Data.CFSGNative.H13.J4Fix
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.J4.Action

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native


theorem u_mem_J : u ∈ J := by
  rw [u_eq_wordProd]
  exact wordProd_mem J baseGL_mem _

theorem v_mem_J : v ∈ J := by
  rw [v_eq_wordProd]
  exact wordProd_mem J baseGL_mem _

theorem W_le_J : W ≤ J := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact u_mem_J
  · exact v_mem_J

theorem t_mem_J : t ∈ J := W_le_J t_mem_W

@[expose] def tJ : J := ⟨t, t_mem_J⟩

theorem tJ_coe : (tJ : GL (Fin 112) (ZMod 2)) = t := rfl


end CFSG.Quasithin.H13.J4
