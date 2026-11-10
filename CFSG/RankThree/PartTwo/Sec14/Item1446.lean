module

public import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Theta.SignalizerCompleteness
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

@[expose] def Concl142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ c : G, Subgroup.zpowers c ∈ omegaA A →
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {c})

@[expose] def Concl143 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
    ∀ Q ∈ maxInvariantPiSubgroups (delta A LB (Subgroup.centralizer {a})) A (piCompl 3),
      Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item1443 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ S : Set (Subgroup G),
    S ⊆ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) →
    sSup S ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
    sSup S ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item1444 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}),
    ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3),
      ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item146 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ invariantPiSubgroups ⊤ A (piCompl 3), Y = delta A LB Y → ∀ a ∈ A, a ≠ 1 →
    Y ⊓ Subgroup.centralizer {a} = delta A LB (Y ⊓ Subgroup.centralizer {a}) ∧
      delta A LB (Y ⊓ Subgroup.centralizer {a}) ∈
        collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

omit [Finite G] in
theorem centralizer_singleton_le_normalizer_zpowers (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {w : G}
    (h : H.map (MulAut.conj w).toMonoidHom = H) : w ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : w * y * w⁻¹ = w * x * w⁻¹ := hyx
    rwa [← mul_left_cancel (mul_right_cancel h1)]

omit [Finite G] in
theorem le_normalizer_sSup {S : Set (Subgroup G)}
    (h : ∀ Q ∈ S, A ≤ Subgroup.normalizer (Q : Set G)) :
    A ≤ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_map_conj_eq ?_
  rw [sSup_eq_iSup', Subgroup.map_iSup]
  exact iSup_congr fun Q => map_conj_eq_of_mem_normalizer (h Q.1 Q.2 hx)

omit [Finite G] in
theorem le_normalizer_commutator {Q S : Subgroup G} (hQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((⁅Q, S⁆ : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hQ hx),
    map_conj_eq_of_mem_normalizer (hS hx)]

omit [Finite G] in
theorem isPiSubgroup_piCompl_of_le {X Y : Subgroup G} (hY : IsPiSubgroup (piCompl 3) Y)
    (hXY : X ≤ Y) : IsPiSubgroup (piCompl 3) X :=
  fun q hq => hY q (hq.trans (Subgroup.card_dvd_of_le hXY))

theorem rank3II_14_4_3_reduction (h142 : Concl142 A LB) (h143 : Concl143 A LB) :
    Item1443 A LB := by
  intro a ha ha1 S hS hY
  have hYC : sSup S ≤ Subgroup.centralizer {a} := sSup_le fun Q hQ => (hS hQ).2
  have hAY : A ≤ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := hY.2.2
  by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
  · have hYN : sSup S ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G))
        A (piCompl 3) := ⟨hYC.trans (centralizer_singleton_le_normalizer_zpowers a), hY.2.1, hAY⟩
    obtain ⟨Q, hQ, hYQ⟩ := exists_le_mem_maxInvariantPiSubgroups hYN
    exact ⟨mem_scriptQ_of_le (h142 a hΩ Q hQ).1 hYQ hAY, hYC⟩
  · have hYΔ : sSup S ≤ delta A LB (Subgroup.centralizer {a}) :=
      sSup_le fun Q hQ => le_delta (hS hQ).1 (hS hQ).2
    obtain ⟨Q, hQ, hYQ⟩ := exists_le_mem_maxInvariantPiSubgroups
      (⟨hYΔ, hY.2.1, hAY⟩ : sSup S ∈ invariantPiSubgroups (delta A LB (Subgroup.centralizer {a}))
        A (piCompl 3))
    exact ⟨mem_scriptQ_of_le (h143 a ha ha1 hΩ Q hQ).1 hYQ hAY, hYC⟩

omit [Finite G] in
theorem commutator_mem_invariantPiSubgroups {a : G} {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ≤ S ∧ ⁅Q, S⁆ ∈ invariantPiSubgroups (Subgroup.centralizer {a}) A (piCompl 3) := by
  have hQS : Q ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hS.2.2
  have hle : ⁅Q, S⁆ ≤ S := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQS
  exact ⟨hle, hle.trans hS.1, isPiSubgroup_piCompl_of_le hS.2.1 hle,
    le_normalizer_commutator hQ.1.1.2.2 (le_sup_left.trans hS.2.2)⟩

theorem rank3II_14_4_4_of_mem_omegaA (h142 : Concl142 A LB) {a : G}
    (hΩ : Subgroup.zpowers a ∈ omegaA A) {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  obtain ⟨-, hQS⟩ := commutator_mem_invariantPiSubgroups ⟨hQ.1.1, hQ.2⟩ hS
  obtain ⟨Q', hQ', hle⟩ := exists_le_mem_maxInvariantPiSubgroups
    (⟨hQS.1.trans (centralizer_singleton_le_normalizer_zpowers a), hQS.2.1, hQS.2.2⟩ :
      ⁅Q, S⁆ ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G)) A
        (piCompl 3))
  exact ⟨mem_scriptQ_of_le (h142 a hΩ Q' hQ').1 hle hQS.2.2, hQS.1⟩


end CFSG.RankThree.PartTwo.Sec14
