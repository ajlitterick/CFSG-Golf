module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthInputs
import CFSG.LocalAnalysis.StandardType.GGTBJD4Frame
import CFSG.LocalAnalysis.StandardType.GGTBJD4Spin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggSecFiveTBJTypeD4Input_holds
    : GGSecFiveTBJTypeD4Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL f ψ hadm hker hrange
  obtain ⟨hp, hp2, hpf, ψ', hinj, u, hu, hup, hu1, J', hJ', hmap, hcount⟩ :=
    ggTBJD4_frame hcfg hL ψ hadm hker hrange
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by have := hadm.2.1; omega)
  exact ggTBJD4_spin (F := GaloisField 2 f) hF hp hp2 hpf hu hup hu1 hJ' hcount
    ((J'.equivMapOfInjective ψ' hinj).trans (MulEquiv.subgroupCongr hmap)).symm

end CFSG.StandardType

end
