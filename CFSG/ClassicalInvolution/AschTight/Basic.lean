module

public import CFSG.ClassicalInvolution.AschTight.S19RCore

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem le_centralizer_of_tight (ht : S19R.TightStdDelta p f K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le ht.branch.member.subnormal

theorem uniqueInvolutionNormal_of_tight (ht : S19R.TightStdDelta p f K z) :
    UniqueInvolutionNormal K z := by
  have hz := ht.branch.member
  let Q : Sylow 2 K := Classical.choice Sylow.nonempty
  exact uniqueInvolutionNormal_of_quaternion_sylow hz.orderOf_eq_two hz.mem
    (le_centralizer_of_tight ht)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_centralizer_of_tight ht)).mpr
      ht.normEq.ge) Q (quaternion_sylow_of_isClassicalMember ht.branch.odd ht.branch.five hz Q)


theorem normalizer_eq_centralizer_of_tight (ht : S19R.TightStdDelta p f K z) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hU := uniqueInvolutionNormal_of_tight ht
  apply le_antisymm
  · intro n hn
    have hmem : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hU.2.1
    have hord : orderOf (n * z * n⁻¹) = 2 := by
      have := (MulAut.conj n).orderOf_eq z
      simpa [MulAut.conj_apply, hU.1] using this
    have h := hU.2.2.1 _ hmem hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]
  · exact ht.normEq.ge

theorem mem_of_isSylow2Of_of_tight (ht : S19R.TightStdDelta p f K z) {P : Subgroup G}
    (hP : IsSylow2Of P K) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := uniqueInvolutionNormal_of_tight ht
  have h2K : 2 ∣ Nat.card K := by
    have h := Subgroup.orderOf_dvd_natCard K hU.2.1
    rwa [hU.1] at h
  have hPcard := hP.card_eq
  have h2P : 2 ∣ Nat.card P := by
    rw [hPcard]
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨x, hxP⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have hx2' : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxP]; exact hx2
  rw [← hU.2.2.1 x (hP.1 hxP) hx2']
  exact hxP


omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * x := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_self :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer hg, fun h => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this


end CFSG.ClassicalInvolution.Disconnected.AschTight
