module

public import CFSG.ClassicalInvolution.Q3.Closure
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL

section Closure

variable {G : Type} [Group G]


variable [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}


end Closure

section Normalizes

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem oddCoreIn_le_rankTwoSpan_of_normalizes {Y : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hnorm : A ≤ Subgroup.normalizer (oddCoreIn Y : Set G)) :
    oddCoreIn Y ≤ rankTwoSpan A := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (oddCoreIn Y) hA (by simpa using h8) hnorm
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem mem_normalizer_centralizingLayer_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) {n : G} (hn : n ∈ Subgroup.centralizer ({a} : Set G)) :
    n ∈ Subgroup.normalizer (centralizingLayer Φ {a} : Set G) := by
  have key : ∀ m ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ centralizingLayer Φ {a},
      m * y * m⁻¹ ∈ centralizingLayer Φ {a} := by
    intro m hm y hy
    have hle : centralizingLayer Φ {a} ≤
        (centralizingLayer Φ {a}).comap (MulAut.conj m).toMonoidHom := by
      refine iSup₂_le fun L hL x hx => ?_
      have hmem : conjSub m L ∈ centralizingMembers Φ {a} := by
        refine ⟨hΦ.conj m hm L hL.1, fun x hx => ?_⟩
        rw [mem_conjSub_iff] at hx
        have hx' := hΦ.le L hL.1 hx
        have : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx') ((Subgroup.inv_mem _) hm)
      exact le_centralizingLayer hmem (conj_mem_conjSub hx)
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key n hn y hy, fun hy => ?_⟩
  have := key n⁻¹ ((Subgroup.centralizer ({a} : Set G)).inv_mem hn) _ hy
  simpa [mul_assoc] using this

theorem normalizes_oddCoreIn_centralizingLayer_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) (hA : IsElemAbelian 2 A) (ha : a ∈ A) :
    A ≤ Subgroup.normalizer (oddCoreIn (centralizingLayer Φ {a}) : Set G) := fun _ hg =>
  mem_normalizer_oddCoreIn_of_mem_normalizer
    (mem_normalizer_centralizingLayer_of_secData hΦ
      (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hg ha)))

theorem centralizingLayer_le_rankTwoSpan_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) (ha : a ∈ A)
    (hgen : centralizingLayer Φ {a} ≤ oddCoreIn (centralizingLayer Φ {a}) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A,
        (Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Φ {a})) :
    centralizingLayer Φ {a} ≤ rankTwoSpan A :=
  hgen.trans (sup_le
    (oddCoreIn_le_rankTwoSpan_of_normalizes hA h8
      (normalizes_oddCoreIn_centralizingLayer_of_secData hΦ hA ha))
    (iSup₂_le fun _ hF => le_rankTwoSpan_of_le_centralizer hF inf_le_left))

end Normalizes

section Exact


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem exactLayer3_le_rankTwoSpan (hΩ : InClass3 Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A)
    (hgen : exactLayer3 Ω a ≤ oddCoreIn (exactLayer3 Ω a) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ exactLayer3 Ω a)) :
    exactLayer3 Ω a ≤ rankTwoSpan A := by
  by_cases hne : (tqMembers3 Ω a).Nonempty
  · exact centralizingLayer_le_rankTwoSpan_of_secData
      (secData3_exactFamily hΩ (isPGroup_zpowers_of_mem_isElemAbelian3 hA ha) hne) hA h8 ha hgen
  · rw [exactLayer3_eq_bot_of_not_nonempty hne]
    exact bot_le


end Exact

end CFSG.ClassicalInvolution.Q3.Q3NF
