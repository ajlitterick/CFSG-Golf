module

public import CFSG.RankThree.GF2n.Smith81.S81E5Tr
public import CFSG.RankThree.GF2n.Smith81.S81E7Reg
public import CFSG.RankThree.GF2n.Smith81.S81BBridge
public import CFSG.RankThree.GF2n.Smith81.S81LS5

public section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable {K : Type} [Field K]

theorem IsRootElt.conj_E {g a : (Module.End K (V K))ˣ} (hg : IsRootElt g) (ha : a ∈ EGrp K) :
    IsRootElt (a * g * a⁻¹) := by
  obtain ⟨h, hh, γ, c, hγ, hc, rfl⟩ := hg
  refine ⟨a * h, mul_mem ha hh, γ, c, hγ, hc, ?_⟩
  group

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81.E5Tr

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model
open scoped commutatorElement

section Setup


end Setup

end CFSG.RankThree.GF2n.Smith81.E5Tr

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model
open scoped commutatorElement

section Main


end Main

end CFSG.RankThree.GF2n.Smith81
