module

public import CFSG.Milestones.ASVolI.A3Aut.D5Base
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped commutatorElement Matrix

section D5U3Generic


theorem burnsideAut_d5_sylow_eq_of_mem {X : Type} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) {P Q : Sylow 2 X} {t : X} (ht : t ≠ 1)
    (htP : t ∈ (P : Subgroup X)) (htQ : t ∈ (Q : Subgroup X)) : P = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P Q
  by_cases hg : g ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)
  · exact (Sylow.smul_eq_iff_mem_normalizer.2 hg).symm
  · exfalso
    set N := Subgroup.normalizer ((P : Subgroup X) : Set X) with hN
    have hg' : g⁻¹ ∉ N := fun h => hg (by simpa using N.inv_mem h)
    have hodd := (hB P).1.2.2 g⁻¹ hg'
    rw [inv_inv] at hodd
    have htN : t ∈ N := Subgroup.le_normalizer htP
    have htN' : t ∈ N.map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ
      obtain ⟨s, hs, rfl⟩ := htQ
      exact ⟨s, Subgroup.le_normalizer hs, rfl⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨t, htP⟩
    have hj' : orderOf t = 2 ^ j :=
      (Subgroup.orderOf_coe (⟨t, htP⟩ : ↥(P : Subgroup X))).trans hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact ht (orderOf_eq_one_iff.mp (by rw [hj', pow_zero]))
    have h2 : 2 ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj g).toMonoidHom) :=
      (dvd_pow_self 2 hj0).trans (hj' ▸ Subgroup.orderOf_dvd_natCard _ ⟨htN, htN'⟩)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)


end D5U3Generic

section D5U3Model

variable {n : ℕ} {K : Type} [Field K]

theorem burnsideAut_d5u3_fusionIsBender [Finite K] (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n) :
    fusionIsBenderGroup (unitaryPSU hu 3) := by
  let e' : unitaryPSU hu 3 ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) :=
    unitaryPSUEquiv hu (by norm_num)
  exact Or.inr (Or.inl ⟨n, hn, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hu.card)⟩⟩)


end D5U3Model


end CFSG.ASVolI
