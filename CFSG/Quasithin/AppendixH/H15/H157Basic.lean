module

public import CFSG.Quasithin.Background.H153Grp
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def tA : ↥AutPerm := ⟨tP, tP_mem⟩


@[expose] def Is3A (y : ↥AutPerm) : Prop := ∃ c : ↥AutPerm, c * y * c⁻¹ = tA

theorem Is3A.orderOf_eq {y : ↥AutPerm} (hy : Is3A y) : orderOf y = 3 := by
  obtain ⟨c, hc⟩ := hy
  have h1 : orderOf (MulAut.conj c y) = orderOf y := by
    simpa using orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  have hcy : MulAut.conj c y = tA := by
    rw [MulAut.conj_apply]
    exact hc
  rw [← h1, hcy]
  simpa [tA] using orderOf_tP


end CFSG.ASVolI.AppH.H157
