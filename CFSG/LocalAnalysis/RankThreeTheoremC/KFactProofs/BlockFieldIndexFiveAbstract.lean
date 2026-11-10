module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)
open scoped commutatorElement

class OddPrime (p : ℕ) : Prop where
  prime : p.Prime
  odd : Odd p

instance : OddPrime 5 := ⟨by norm_num, by decide⟩

instance (priority := low) OddPrime.fact {p : ℕ} [OddPrime p] : Fact p.Prime :=
  ⟨OddPrime.prime⟩

theorem OddPrime.odd_pow (p : ℕ) [OddPrime p] (k : ℕ) : Odd (p ^ k) :=
  (OddPrime.odd (p := p)).pow

theorem OddPrime.ne_two (p : ℕ) [OddPrime p] : p ≠ 2 := by
  rintro rfl
  exact absurd (OddPrime.odd (p := 2)) (by decide)

theorem OddPrime.three_le (p : ℕ) [OddPrime p] : 3 ≤ p := by
  have h2 := (OddPrime.prime (p := p)).two_le
  have h3 := OddPrime.ne_two p
  omega

theorem exists_normal_index_prime {p : ℕ} [Fact p.Prime] {Y Γ : Type*} [Group Y] [Finite Y]
    [Group Γ] [Finite Γ] (φ : Y →* Γ) {D : Subgroup Γ} (hD : PCentral p D) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a)) (hφa : φ a ∉ D) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  classical
  haveI : D.Normal := hD.1
  set q : Y →* Γ ⧸ D := (QuotientGroup.mk' D).comp φ with hq
  have hqa : q a ≠ 1 := fun h => hφa ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hqak : (q a) ^ (p ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hcent : ∀ y : Γ ⧸ D, (∃ k : ℕ, y ^ (p ^ k) = 1) → y ∈ Subgroup.center (Γ ⧸ D) := by
    rintro y ⟨k, hk⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : ⁅γ, g⁆ ∈ D := hD.2 g ⟨k, by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hk⟩ γ
    have h2 : ⁅(QuotientGroup.mk' D γ), (QuotientGroup.mk' D g)⁆ = 1 := by
      rw [← map_commutatorElement]; exact (QuotientGroup.eq_one_iff _).2 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  obtain ⟨S⟩ : Nonempty (Sylow p (Γ ⧸ D)) := inferInstance
  have hSc : (S : Subgroup (Γ ⧸ D)) ≤ Subgroup.center (Γ ⧸ D) := by
    intro s hs
    apply hcent
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hS : Subgroup.normalizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) ≤
      Subgroup.centralizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_center_iff.1 (hSc hs) n).symm
  let T : Γ ⧸ D →* S := MonoidHom.transferSylow S hS
  let t : Y →* S := T.comp q
  have hdisj := MonoidHom.ker_transferSylow_disjoint S hS (Subgroup.zpowers (q a)) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ⟨k, Subtype.ext (by
      show (q a ^ m) ^ p ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqak, one_zpow])⟩)
  have hta : t a ≠ 1 := by
    intro h
    have hmem : q a ∈ T.ker := by rw [MonoidHom.mem_ker]; exact h
    exact hqa (Subgroup.disjoint_def.1 hdisj hmem (Subgroup.mem_zpowers _))
  have htak : (t a) ^ (p ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hB3 : IsPGroup p t.range := S.isPGroup'.of_injective t.range.subtype
    (Subgroup.subtype_injective _)
  haveI : Group.IsNilpotent t.range := hB3.isNilpotent
  have hd3 : p ∣ Nat.card t.range := by
    have h1 : orderOf (t a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one htak
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hta (orderOf_eq_one_iff.1 (by simpa using hj))
    have h2 : orderOf (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range) = p ^ j := by
      rw [← hj, ← Subgroup.orderOf_coe]
    have h3 := orderOf_dvd_natCard (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range)
    rw [h2] at h3
    exact (dvd_pow_self p hj0).trans h3
  obtain ⟨M, hMi, hMn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hd3
  refine ⟨M.comap t.rangeRestrict, Subgroup.Normal.comap hMn _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ t.rangeRestrict_surjective, hMi]

section Levi


end Levi

section Families


end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
