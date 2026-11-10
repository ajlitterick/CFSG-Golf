
module

public import CFSG.Sporadic.Schreier.RuOddCoreBase

public import CFSG.Sporadic.Schreier.RuAutInner
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
public meta import CFSG.Sporadic.Schreier.RuTreeEltA
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem noOddNormal_centralizer_ruA0 :
    NoOddNormal (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) :=
  NoOddNormal.of_mulEquiv (MulEquiv.subgroupCongr ruCentralizer_a.symm) ruL_noOddNormal

theorem noOddNormal_centralizer
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    NoOddNormal (ruP ⊓ Subgroup.centralizer {t} : Subgroup _) := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact NoOddNormal.of_mulEquiv (conjCentralizerEquiv hg ruZ) noOddNormal_centralizer_ruZ
  · exact NoOddNormal.of_mulEquiv (conjCentralizerEquiv hg ruA0) noOddNormal_centralizer_ruA0


end CFSG.Sporadic.RuSchreier
