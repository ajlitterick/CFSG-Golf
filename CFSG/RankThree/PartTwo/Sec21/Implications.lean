module

public import CFSG.RankThree.PartTwo.Sec21.Notation
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

abbrev lBar (L : Subgroup G) : Type :=
  ↥L ⧸ aschbacherSolvableCore 3 ↥L

@[expose] def IsL4L5Sp6 (L : Subgroup G) : Prop :=
  StatedClassicalModel (lBar L) .PSL 4 2 1 ∨ StatedClassicalModel (lBar L) .PSL 5 2 1 ∨
    StatedClassicalModel (lBar L) .PSp 3 2 1

theorem rank3II_21_16 {A L : Subgroup G} {c : G}
    (h21_2 : IsL4L5Sp6 L → Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G))
    (h21_15 : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)) :
    ¬ IsL4L5Sp6 L :=
  fun h => h21_15 (h21_2 h)

theorem inSubgroup_theta_map_subtype [Finite G] {H : Subgroup G} (K : Subgroup H) :
    inSubgroup (aschbacherSolvableCore 3) (K.map H.subtype) =
      (inSubgroup (aschbacherSolvableCore 3) K).map H.subtype := by
  set e := K.equivMapOfInjective H.subtype H.subtype_injective
  have h := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  rw [inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem theta_le_theta_centralizer [Finite G] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) :
    inSubgroup (aschbacherSolvableCore 3) L ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨L', hL', rfl⟩ := hL
  rw [inSubgroup_theta_map_subtype,
    solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL'.2.1]
  exact Subgroup.map_mono inf_le_right

theorem map_conj_eq_of_mem_normalizer {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) : L.map (MulAut.conj a).toMonoidHom = L := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ha x).mp hx
  · intro x hx
    refine ⟨a⁻¹ * x * a, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) x).mp hx
    simpa using this

theorem le_normalizer_theta [Finite G] {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
  intro a ha
  have hmap : (inSubgroup (aschbacherSolvableCore 3) L).map (MulAut.conj a).toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) L := by
    rw [map_inSubgroup_aschbacherSolvableCore, map_conj_eq_of_mem_normalizer (hAL ha)]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      simpa [MulAut.conj_apply] using hyh
    exact this ▸ hy

theorem eq_bot_of_isPGroup_two_of_odd [Finite G] {X : Subgroup G} (h2 : IsPGroup 2 X)
    (hodd : Odd (Nat.card X)) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rcases n with _ | n
  · exact Subgroup.card_eq_one.mp (by simpa using hn)
  · rw [hn, pow_succ] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_mul_left 2 _)))


end CFSG.RankThree.PartTwo.Sec21
