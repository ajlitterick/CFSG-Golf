module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityActions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Lemma73
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem2

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} [Group G]

theorem sylow_conj [Finite G] {p : ℕ} (hp : p.Prime)
    {P D : Subgroup G} (hP : theorem4bIsSylowSubgroupOf p P D) (g : G) :
    theorem4bIsSylowSubgroupOf p (P.conjBy g) (D.conjBy g) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨PD, hPD⟩ := hP
  let e : D ≃* D.conjBy g := MulEquiv.subgroupMap (MulAut.conj g) D
  let Q : Sylow p (D.conjBy g) := PD.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q, ?_⟩
  rw [hPD]
  change ((PD : Subgroup D).map D.subtype).map (MulAut.conj g).toMonoidHom =
    ((PD : Subgroup D).map e.toMonoidHom).map (D.conjBy g).subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1


theorem three_le_fixed_card {Ω : Type v} [MulAction G Ω] [Finite Ω]
    (P : Subgroup G) {a b c : Ω}
    (ha : P ≤ MulAction.stabilizer G a) (hb : P ≤ MulAction.stabilizer G b)
    (hc : P ≤ MulAction.stabilizer G c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} := by
  let A : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨a, fun x hx => MulAction.mem_stabilizer_iff.mp (ha hx)⟩
  let B : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨b, fun x hx => MulAction.mem_stabilizer_iff.mp (hb hx)⟩
  let C : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨c, fun x hx => MulAction.mem_stabilizer_iff.mp (hc hx)⟩
  let := Fintype.ofFinite {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P}
  rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
  exact ⟨A, B, C, fun h => hab (congrArg Subtype.val h),
    fun h => hac (congrArg Subtype.val h), fun h => hbc (congrArg Subtype.val h)⟩


end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
