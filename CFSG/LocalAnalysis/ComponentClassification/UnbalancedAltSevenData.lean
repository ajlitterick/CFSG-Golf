module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenAlternating
public import CFSG.Sporadic.Schreier.LyDoubleCover

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open Equiv Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

@[expose] def lyPi : lyC →* alternatingGroup (Fin 11) :=
  lyCoverEquiv.toMonoidHom.comp (QuotientGroup.mk' zGroup)

theorem lyPi_apply (g : lyC) : lyPi g = lyCoverEquiv (g : lyC ⧸ zGroup) := rfl

theorem coe_lyPi (g : lyC) : (lyPi g : Perm (Fin 11)) = imgC g := rfl

theorem lyPi_surjective : Function.Surjective lyPi :=
  lyCoverEquiv.surjective.comp (QuotientGroup.mk'_surjective zGroup)

theorem lyPi_ker : lyPi.ker = zGroup := by
  ext g
  rw [MonoidHom.mem_ker, lyPi_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem lyPi_zC : lyPi zC = 1 := (MonoidHom.mem_ker).1 (lyPi_ker ▸ mem_zpowers zC)


@[expose] def altSevenE : Subgroup lyC := stabFour.comap lyPi


theorem zC_mem_altSevenE : zC ∈ altSevenE := by
  change lyPi zC ∈ stabFour
  rw [lyPi_zC]
  exact one_mem _

@[expose] def altSevenZ : altSevenE := ⟨zC, zC_mem_altSevenE⟩

@[expose] def altSevenPi : altSevenE →* alternatingGroup (Fin 7) :=
  relabel.toMonoidHom.comp (lyPi.subgroupComap stabFour)

theorem altSevenPi_apply (g : altSevenE) :
    altSevenPi g = relabel ⟨lyPi g, g.2⟩ := rfl


end CFSG.ComponentClassification.UnbalancedAltSeven
