module

public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.ClassicalInvolution.AschTight.OmegaD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem isPGroup_of_mem_rSet {Ω : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ RSet Ω) :
    IsPGroup 2 R := by
  obtain ⟨J, -, P, rfl⟩ := hR
  exact P.isPGroup'.map _

theorem quaternionGroup_a_mul_xa_ne {n : ℕ} (hn : 2 ≤ n) :
    (QuaternionGroup.a 1 : QuaternionGroup n) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
  intro h
  have h' : (0 - 1 : ZMod (2 * n)) = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have : 2 * n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem exists_ne_comm_of_mem_rSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hK : IsClassicalMember p f K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) :
    (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) ∧ 8 ≤ Nat.card R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨r, hr, ⟨e⟩⟩ := quaternion_sylow_of_isClassicalMember hp hq (hK.conj g) P
  let e' : ↥((P : Subgroup ↥(conjSub g K)).map (conjSub g K).subtype) ≃*
      QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective _ _ (conjSub g K).subtype_injective).symm.trans e
  have hn : 2 ≤ 2 ^ (r - 2) :=
    le_of_eq_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ r - 2))
  refine ⟨⟨(e'.symm (QuaternionGroup.a 1) : G), (e'.symm _).2,
    (e'.symm (QuaternionGroup.xa 0) : G), (e'.symm _).2, fun h => ?_⟩, ?_⟩
  · apply quaternionGroup_a_mul_xa_ne hn
    apply e'.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext h
  · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega

theorem isUniqueInvolution_of_mem_rSet_of_le (ht : S19R.TightStdDelta p f K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) : IsUniqueInvolution R z := by
  have hI := isUniqueInvolution_of_tight ht
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR).2
  obtain ⟨k, hk⟩ := (isPGroup_of_mem_rSet hR).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at h8
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huz : (u : G) = z := (uniqueInvolutionNormal_of_tight ht).2.2.1 _ (hRK u.2) hu'
  exact ⟨huz ▸ u.2, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y (hRK hy) hy2⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight
