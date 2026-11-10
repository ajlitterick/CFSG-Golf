module

public import CFSG.Dihedral.DihedralFusionDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import CFSG.GroupTheory.DihedralTwoClassFusionSupport

public section

namespace CFSG.GorensteinWalter.TwoClassFusion

open DihedralGroup BenderSuzuki.PFchapter1section1

universe u


theorem exists_normal_index_two_of_normal_index_four {X : Type u} [Group X] [Finite X]
    {N : Subgroup X} (hN : N.Normal) (hindex : N.index = 4) :
    ∃ M : Subgroup X, M.Normal ∧ M.index = 2 := by
  have hcard : Nat.card (X ⧸ N) = 4 := by rw [← Subgroup.index_eq_card, hindex]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X ⧸ N) 2 (by rw [hcard]; norm_num)
  have hJ : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).index_mul_card
    rw [Nat.card_zpowers, hx, hcard] at h
    omega
  exact ⟨(Subgroup.zpowers x).comap (QuotientGroup.mk' N),
    (Subgroup.normal_of_index_eq_two hJ).comap _,
    (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)).trans hJ⟩

theorem exists_normal_index_two_of_not_isConj {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 1 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : ¬ IsConj u v) :
    ∃ N : Subgroup X, N.Normal ∧ N.index = 2 := by
  have hdih : HasDihedralSylowTwo X := fun S => ⟨m, hm, ⟨(Sylow.equiv S D).trans e⟩⟩
  have hinv : ∀ {y : X}, orderOf y = 2 → BenderSuzuki.PFAppendixIII.IsInvolution y :=
    fun {y} hy => ⟨fun h1 => by simp [h1] at hy, by rw [← hy]; exact pow_orderOf_eq_one y⟩
  rcases gw_lemma_2_1 hdih with h1 | h2 | ⟨⟨N, hN, hindex⟩, -⟩
  · obtain ⟨g, hg⟩ := h1.2.1 u v (hinv hu) (hinv hv)
    exact absurd (isConj_iff.mpr ⟨g, hg⟩) huv
  · exact h2.1
  · exact exists_normal_index_two_of_normal_index_four hN hindex


end CFSG.GorensteinWalter.TwoClassFusion
