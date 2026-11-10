
module

public import CFSG.Monster.B.TwoA.Sp8.DataBase

public import CFSG.Monster.B.TwoA.Base.EU
public import CFSG.Monster.B.TwoA.Triality.PermLift
public import Certificates.Certificate16951
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv

theorem XQ_dC_mem_centralizer :
    XQ ⟨dC, 0⟩ ∈ Subgroup.centralizer {rStar} := by
  rw [mem_centralizer_iff_bL, coordOf_rStar, coordOf_XQ]
  refine (bL_phi0 0 dC (deltaPair 0 1) (thetaD dC)).trans ?_
  rw [pair_zero_left, zero_add, deltaPair, pair_mk]
  exact Certificates.certificate16951

@[expose] def ubar : Cbar :=
  kappa ⟨rhoEquiv (XQ ⟨dC, 0⟩), rhoEquiv_mem_Cgen XQ_dC_mem_centralizer⟩

theorem ubar_mem_Ebar :
    ubar ∈ Ebar := kappa_rho_mem_Ebar XQ_dC_mem_centralizer

@[expose] def uhat : Dfull := iotaD ubar

theorem uhat_mem_Ehat : uhat ∈ Ehat := ⟨ubar, ubar_mem_Ebar, rfl⟩

@[expose] def ghat8 : Dfull := tauhat * uhat * tauhat⁻¹

@[expose] def B7 : Subgroup Dfull :=
  Subgroup.closure {xhat, yhat, dhat 2 3, dhat 2 4, dhat 2 5, dhat 2 6, uhat}

@[expose] def A8 :
    Subgroup Dfull := Subgroup.closure (insert ghat8 (B7 : Set Dfull))

@[expose] def H1 :
    Subgroup Dfull := (Cr.comap jhatToKv0).map Jhat.subtype

@[expose] def Xgrp :
    Subgroup Dfull := Subgroup.closure (insert tauhat (H1 : Set Dfull))

@[expose] def aT : Fin 8 → Dfull :=
  ![xhat, yhat, dhat 2 3, dhat 2 4, dhat 2 5, dhat 2 6, uhat, ghat8]

theorem B7_le_Ehat :
    B7 ≤ Ehat := by
  rw [B7, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xhat_mem_Ehat
  · exact yhat_mem_Ehat
  · exact dhat_mem_Ehat 2 3
  · exact dhat_mem_Ehat 2 4
  · exact dhat_mem_Ehat 2 5
  · exact dhat_mem_Ehat 2 6
  · exact uhat_mem_Ehat

theorem ghat8_mem_Shat : ghat8 ∈ Shat :=
  Shat.mul_mem (Shat.mul_mem tauhat_mem_Shat (Ehat_le_Shat uhat_mem_Ehat))
    (Shat.inv_mem tauhat_mem_Shat)

theorem A8_le_Shat :
    A8 ≤ Shat := by
  rw [A8, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact ghat8_mem_Shat
  · exact Ehat_le_Shat (B7_le_Ehat hx)

theorem H1_le_Jhat : H1 ≤ Jhat := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem Xgrp_le_Shat :
    Xgrp ≤ Shat := by
  rw [Xgrp, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact tauhat_mem_Shat
  · exact Jhat_le_Shat (H1_le_Jhat hx)

theorem mem_H1_iff
    (g : Dfull) : g ∈ H1 ↔ ∃ h : g ∈ Jhat, jhatToKv0 ⟨g, h⟩ ∈ Cr := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨g, h⟩, hk, rfl⟩


end CFSG.Monster.B.TwoA.Sp8
