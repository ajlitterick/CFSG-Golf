module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample -- minimalCounterexample_isSimple and the centralizer setup witness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection -- reflection elements in the dihedral Sylow are involutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23IIHelpers -- inversion endpoint for Lemma 2.3(ii)
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers -- elementary normalizer and inverted-subgroup endpoints
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers -- elementary intersection endpoint for Lemma 2.9
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23II
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.HhatConjugateTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem210
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1 -- needed by the proofs of 2.7-2.9 (fact_1_4_*, fact_1_5_iii, centralizerIn, sqrtOf); make `public import` only if a Section2 statement cites a Section 1 name (Section3/Section4 do not import Section1)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23ControlCore -- the control-core bridge: discharges `lemma_2_3` below (re-exports ControlCore)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU -- lower acyclic proof of the recalled equality `H = S ⊔ O(H)`
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions -- local assembly from GW Lemma 2.1

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2: maximal subgroups related to an involution centralizer
-/

noncomputable section

open Matrix

namespace CFSG.GorensteinWalter

universe u

/-! ## Section 2 preamble facts (Bender p. 219) -/

/-- Section 2 preamble: all involutions of the minimal counterexample `G` are
conjugate ("We recall that all involutions of `G` are conjugate"). -/
public theorem fact_2_preamble_involutions_conjugate
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    ∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y := by
  exact fact_2_preamble_involutions_conjugate_proved hmin

/-- Section 2 preamble: `H = S·U`, i.e. `C_G(t) = S·O(C_G(t))` ("We recall
that ... `H` is `SU`").  The paper's product `SU` is the subgroup generated
by `S` and `U`, written here as the join. -/
public theorem fact_2_preamble_H_eq_SU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    (c.S : Subgroup G) ⊔ c.U = c.H := by
  exact fact_2_preamble_H_eq_SU_proved hmin c


end CFSG.GorensteinWalter
