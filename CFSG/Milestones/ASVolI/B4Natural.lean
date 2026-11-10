module

public import CFSG.GroupTheory.GLnTwoSplitting.Main
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
public import CFSG.Milestones.ASVolI.B4
public import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.FFC5Coh3
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.FFC5Piece
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.ASVolI

open CFSG.Open

section Gaschutz

variable {Γ : Type*} [Group Γ] {W V : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup V] [Module (ZMod 2) V]


end Gaschutz

section GLForm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


section Quad

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end Quad

section Sec

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end Sec

end GLForm

section KLevi

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


section Extend

variable (φ : Module.Dual (ZMod 2) W) {w₀ : W} (hw₀ : φ w₀ = 1)

include hw₀


end Extend


section KFixNat

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end KFixNat

section KFixDual

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end KFixDual

section Core

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end Core

end KLevi

section Interface

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin


section Quot

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)


variable (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end Quot

section Facts

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n K) →* ↥G}


end Facts

end Interface

section Transport

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)


variable (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end Transport

section Bijective

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin


variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n K) →* ↥G}


end Bijective

section TransData

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


end TransData

section QuotRange

variable {V : Type} [CommGroup V] [Finite V] (U : Subgroup V)


end QuotRange

section RankOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end RankOne

section Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


variable {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}


end Assembly

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V))


variable {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}


end Final

section PFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end PFix

section FinalThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}


end FinalThree

section FourIso

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]


variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end FourIso

section KFixFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end KFixFour

section CoreF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end CoreF1

section FinalF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}


end FinalF1

section AddGaschutz

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {Γ : Type*} [Group Γ] {W V : Type*} [AddCommGroup W] [AddCommGroup V]


end AddGaschutz

section MatTool

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]


end MatTool

section SLFacts

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]


end SLFacts

section S1Sec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]


end S1Sec

section Core3Sec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Sec

section Core3Lifts

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]


variable {A : Type} [AddCommGroup A]


end Core3Lifts

section Core3Match

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]


variable {A : Type} [AddCommGroup A]


end Core3Match

section Core3Nat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Nat

section Core3Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Dual

section Core3Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Main

section Core3Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Final

section Trans3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {V : Type} [CommGroup V]


end Trans3

section Coord3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end Coord3

section Core3Conj

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end Core3Conj

section Coord3Nat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end Coord3Nat

section SplitsSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end SplitsSec

section TraceForm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]


end TraceForm

section DualCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {K : Type} [Field K] [Finite K] [CharP K 2] {U : Type} [CommGroup U]


end DualCoord

section Coord3Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}


end Coord3Dual

section Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}


end Three

section Bridge

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end Bridge

section CardRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}


end CardRank

section RankOne3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K]


end RankOne3

section TransvRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}


end TransvRank

section Normalize

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]


end Normalize

section Normalize2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K]


end Normalize2

section RootConjSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]


end RootConjSec

section InRoot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end InRoot

section RootLine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}


end RootLine

section RelSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]


end RelSec

section Spread1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]


variable {A : Type} [AddCommGroup A]


end Spread1

section Cubes

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2]


end Cubes

section Spread2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {A : Type} [AddCommGroup A]


end Spread2

section Assemble3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}


end Assemble3

section Three3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}


end Three3

section TransvConverse

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V]


end TransvConverse

section TransvConverse2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}


end TransvConverse2

section FTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [CharP K 2]


end FTwo

section DepRoot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]


end DepRoot

section FTwoEp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}


end FTwoEp

section FTwoFinal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}


end FTwoFinal

section Spread3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {A : Type} [AddCommGroup A]


end Spread3

section FinalThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}


end FinalThree

section Part1All

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end Part1All

section Reduction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end Reduction

end CFSG.ASVolI
