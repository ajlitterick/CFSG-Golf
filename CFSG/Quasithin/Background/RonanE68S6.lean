module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Quasithin.Background.RonanE68Mat

public section

namespace CFSG.Quasithin.RonanE68

open CFSG.ComponentClassification.PresentationLocal Equiv Equiv.Perm Matrix
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6

section Decide


end Decide

section Sp42

@[expose] def longHat : sympFour :=
  sympOfInvolutive (1 + single 0 3 1) (by decide) (by decide)


theorem omegaPerm_longHat : omegaPerm longHat = swap 0 1 := by decide


theorem minorJ_two_eq : minorJ (ZMod 2) = antidiagGram := by
  ext i j
  simp [minorJ_apply, antidiagGram]

theorem sympFour_eq_antiSp : sympFour = antiSp (ZMod 2) := by
  ext g
  rw [mem_sympFour_iff, mem_antiSp, minorJ_two_eq]

@[expose] noncomputable def Psi : ↥(CFSG.Open.StatedSp 2 (ZMod 2)) ≃* Perm (Fin 6) :=
  (antiSpEquiv (ZMod 2)).symm.trans
    ((MulEquiv.subgroupCongr sympFour_eq_antiSp).symm.trans
      (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩))

theorem Psi_antiSpEquiv (x : antiSp (ZMod 2)) :
    Psi (antiSpEquiv (ZMod 2) x) = omegaPerm ((MulEquiv.subgroupCongr sympFour_eq_antiSp).symm x) := by
  simp only [Psi, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem symm_subgroupCongr_uElt_long :
    (MulEquiv.subgroupCongr sympFour_eq_antiSp).symm (uElt (0 : ZMod 2) 0 1 0) = longHat :=
  Subtype.ext (Units.ext (glMat_uElt_long (F := ZMod 2) 1))


theorem Psi_long :
    Psi (antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 0 1 0)) = swap 0 1 := by
  rw [Psi_antiSpEquiv, symm_subgroupCongr_uElt_long, omegaPerm_longHat]


end Sp42

end CFSG.Quasithin.RonanE68
