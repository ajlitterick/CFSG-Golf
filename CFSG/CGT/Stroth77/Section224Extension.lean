module

public import CFSG.CGT.Stroth77.Section224Deviation

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}


@[expose] def thetaD (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho) (d : Z.D) : Z.D :=
  ⟨(d : G) * (d : G) * ((deviation Z s hs (Additive.ofMul d)).toMul : G), by
    have hd2 : (d : G) * (d : G) ∈ Z.D := Z.D.mul_mem d.2 d.2
    have hφ : ((deviation Z s hs (Additive.ofMul d)).toMul : G) ∈ Z.D :=
      omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul d)).toMul.2
    exact Z.D.mul_mem hd2 hφ⟩

@[simp] theorem coe_thetaD (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) :
    (thetaD Z s hs d : G) =
      (d : G) * (d : G) * ((deviation Z s hs (Additive.ofMul d)).toMul : G) := rfl


end CFSG.CGT.Stroth77
