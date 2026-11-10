module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.Transfer.Yoshida
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

namespace Wales147Free

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G} {𝓕 : Set (Subgroup G)}
  {M : G → Subgroup G}

theorem card_eq_nine (hA : Late.IsE27 A) {E : Subgroup G} (hE : IsHyperplane A E) :
    Nat.card E = 9 := by
  have h := hE.2
  rw [hA.2] at h
  omega

theorem exists_ne_one_mem_inf (hA : Late.IsE27 A) {E F : Subgroup G} (hE : IsHyperplane A E)
    (hF : IsHyperplane A F) : ∃ b ∈ E, b ∈ F ∧ b ≠ 1 := by
  have hi : ∀ {H : Subgroup G}, IsHyperplane A H → H.relIndex A = 3 := fun {H} hH => by
    have h := Subgroup.relIndex_mul_card H A
    rw [inf_eq_left.mpr hH.1, card_eq_nine hA hH, hA.2] at h
    omega
  by_contra hno
  push Not at hno
  have hbot : E ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (hno x (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2)
  have hle : (E ⊓ F).relIndex A ≤ E.relIndex A * F.relIndex A := Subgroup.relIndex_inf_le
  have h2 := Subgroup.relIndex_mul_card (E ⊓ F) A
  rw [hbot, bot_inf_eq, Subgroup.card_bot, mul_one, hA.2] at h2
  rw [hbot, h2, hi hE, hi hF] at hle
  omega


end Wales147Free

open Wales147Free


end CFSG.RankThree.PartTwo.Sec14
