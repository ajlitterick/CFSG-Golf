module

public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Dihedral.DihedralFusionAutomorphisms
import CFSG.Dihedral.PerfectDihedralFourgroupAction
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.Census3 TauCeti
open scoped commutatorElement


@[expose] def EvenListBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (ThmThreeItem7 X ∨ ThmThreeItem8 X ∨ ThmThreeItem9 X) →
    CFSG.Blueprint.EvenLieType X


theorem not_sq_dvd_factorial_of_le_twelve {n p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hn : n ≤ 12) :
    ¬ p ^ 2 ∣ Nat.factorial n := by
  intro h
  have hpn : p ∣ Nat.factorial n := (dvd_pow_self p two_ne_zero).trans h
  have hp12 : p ≤ 12 := ((hp.dvd_factorial).1 hpn).trans hn
  have key : ∀ m ≤ 12, ¬ 7 ^ 2 ∣ Nat.factorial m ∧ ¬ 11 ^ 2 ∣ Nat.factorial m := by decide +kernel
  interval_cases p
  · exact (key n hn).1 h
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact (key n hn).2 h
  · exact absurd hp (by norm_num)


theorem no_action_of_dihedral {X : Type} [Group X] [Finite X]
    (hd : GorensteinWalter.HasDihedralSylowTwo X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E S : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1) (hS : IsPGroup 2 S)
    (hN : E ≤ Subgroup.normalizer (S : Set X)) : E ≤ Subgroup.centralizer (S : Set X) := by
  classical
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  obtain ⟨m, hm, ⟨eT⟩⟩ := hd T
  let φ : E →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hφ : ∀ x : E, φ x = 1 := by
    intro x
    have hxp : x ^ p = 1 := Subtype.ext (hE x x.2)
    have hord : orderOf (φ x) ∣ p :=
      (orderOf_map_dvd φ x).trans (orderOf_dvd_of_pow_eq_one hxp)
    have hne : orderOf (φ x) ≠ p := by
      intro hop
      by_cases hk : IsKleinFour S
      · have h6 : Nat.card (MulAut S) = 6 := GorensteinWalter.kleinFourAut_card S
        have hdv : orderOf (φ x) ∣ 6 := h6 ▸ orderOf_dvd_natCard (φ x)
        rw [hop] at hdv
        have h23 : p ∣ 2 * 3 := by simpa using hdv
        rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
        · have := Nat.le_of_dvd (by norm_num) h2
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · have hM : IsPGroup 2 (MulAut S) :=
          GorensteinWalter.dihedral_subgroup_automorphism_isTwoGroup T hm eT S hST hk
        obtain ⟨j, hj⟩ := hM (φ x)
        have hdv : p ∣ 2 ^ j := hop ▸ orderOf_dvd_of_pow_eq_one hj
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdv)
        omega
    exact orderOf_eq_one_iff.1 ((Nat.dvd_prime hp).1 hord |>.resolve_right hne)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : (φ ⟨x, hx⟩) ⟨s, hs⟩ = ⟨s, hs⟩ := by rw [hφ ⟨x, hx⟩]; rfl
  have h2 : x * s * x⁻¹ = s := congrArg Subtype.val h1
  calc s * x = (x * s * x⁻¹) * x := by rw [h2]
    _ = x * s := by group


end CFSG.RankThree.PartOne.N143
