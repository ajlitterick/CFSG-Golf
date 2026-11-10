module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem power_kernel_characteristic
    {source : Type u} [CommGroup source] (exponent : ℕ) :
    (powMonoidHom exponent : source →* source).ker.Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro equivalence element helement
  obtain ⟨lift, hlift, rfl⟩ := helement
  change equivalence lift ^ exponent = 1
  rw [← map_pow, show lift ^ exponent = 1 from hlift, map_one]

theorem elementary_abelian_sup_of_commuting
    {ambient : Type u} [Group ambient]
    (prime : ℕ) {first second : Subgroup ambient}
    (hfirst : IsElemAbelian prime first) (hsecond : IsElemAbelian prime second)
    (hcommute : first ≤ Subgroup.centralizer (second : Set ambient)) :
    IsElemAbelian prime (first ⊔ second) := by
  let : IsMulCommutative first := hfirst.1
  let : IsMulCommutative second := hsecond.1
  let hom : first × second →* ambient :=
    { toFun := fun element => (element.1 : ambient) * (element.2 : ambient)
      map_one' := one_mul 1
      map_mul' := fun left right => by
        change ((left.1 : ambient) * (right.1 : ambient)) *
          ((left.2 : ambient) * (right.2 : ambient)) =
          ((left.1 : ambient) * (left.2 : ambient)) *
            ((right.1 : ambient) * (right.2 : ambient))
        have hmiddle := Subgroup.mem_centralizer_iff.mp
          (hcommute right.1.property) left.2 left.2.property
        calc
          _ = (left.1 : ambient) * ((right.1 : ambient) * (left.2 : ambient)) *
              (right.2 : ambient) := by group
          _ = (left.1 : ambient) * ((left.2 : ambient) * (right.1 : ambient)) *
              (right.2 : ambient) := by rw [hmiddle]
          _ = _ := by group }
  have hrange : hom.range = first ⊔ second := by
    apply le_antisymm
    · rintro element ⟨lift, rfl⟩
      exact (first ⊔ second).mul_mem
        ((show first ≤ first ⊔ second from le_sup_left) lift.1.property)
        ((show second ≤ first ⊔ second from le_sup_right) lift.2.property)
    · apply sup_le
      · intro element helement
        exact ⟨(⟨element, helement⟩, 1), mul_one element⟩
      · intro element helement
        exact ⟨(1, ⟨element, helement⟩), one_mul element⟩
  have hproduct : IsElemAbelian prime (⊤ : Subgroup (first × second)) := by
    refine ⟨inferInstance, ?_⟩
    intro element _
    apply Prod.ext
    · apply Subtype.ext
      exact hfirst.2 element.1 element.1.property
    · apply Subtype.ext
      exact hsecond.2 element.2 element.2.property
  have hmap := elementary_abelian_map prime hproduct hom
  rw [← MonoidHom.range_eq_map, hrange] at hmap
  exact hmap

theorem elementary_subgroup_eq_of_rank_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) {first second : Subgroup ambient}
    (hsecond : IsElemAbelian prime second) (hcontained : first ≤ second)
    (rank : ℕ) (hcard : Nat.card first = prime ^ rank)
    (hrank : pRank prime second ≤ rank) : first = second := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hgroup : IsPGroup prime second := isPGroup_iff_pow_pow_eq_one.mpr
    fun element => ⟨1, by
      apply Subtype.ext
      change element.val ^ (prime ^ 1) = 1
      simpa only [pow_one] using hsecond.2 element.val element.property⟩
  obtain ⟨secondRank, hsecondCard⟩ := IsPGroup.iff_card.mp hgroup
  have hsecondRank : secondRank ≤ rank :=
    (le_csSup (pRank_bddAbove prime hprime second)
      ⟨second, le_rfl, hsecond, hsecondCard⟩).trans hrank
  apply Subgroup.eq_of_le_of_card_ge hcontained
  rw [hcard, hsecondCard]
  exact Nat.pow_le_pow_right hprime.pos hsecondRank


theorem commutative_pGroup_isCyclic_of_rank_le_one
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hgroup : IsPGroup prime source)
    (hrank : pRank prime (⊤ : Subgroup source) ≤ 1) : IsCyclic source := by
  let : Fact prime.Prime := ⟨hprime⟩
  let hom : source →* source := powMonoidHom prime
  have hkernelElementary : IsElemAbelian prime hom.ker := by
    refine ⟨inferInstance, ?_⟩
    intro element helement
    exact helement
  obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp (hgroup.to_subgroup hom.ker)
  have hkernelRank : kernelRank ≤ 1 :=
    (le_csSup (pRank_bddAbove prime hprime (⊤ : Subgroup source))
      ⟨hom.ker, le_top, hkernelElementary, hkernelCard⟩).trans hrank
  have hkernelBound : Nat.card hom.ker ≤ prime := by
    rw [hkernelCard]
    simpa only [pow_one] using Nat.pow_le_pow_right hprime.pos hkernelRank
  have hquotientRangeCard : Nat.card (source ⧸ hom.range) = Nat.card hom.ker := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := hom.range))
    calc
      _ = Nat.card source := hom.range.card_eq_card_quotient_mul_card_subgroup.symm
      _ = Nat.card hom.range * Nat.card hom.ker := by
        rw [hom.ker.card_eq_card_quotient_mul_card_subgroup,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange hom).toEquiv]
      _ = _ := Nat.mul_comm _ _
  have hrangeFrattini : hom.range ≤ frattini source := by
    rintro element ⟨lift, rfl⟩
    exact pGroup_pow_mem_frattini prime hgroup lift
  have hquotientBound : Nat.card (source ⧸ frattini source) ≤ prime := by
    change (frattini source).index ≤ prime
    apply (Subgroup.index_antitone hrangeFrattini).trans
    change Nat.card (source ⧸ hom.range) ≤ prime
    rw [hquotientRangeCard]
    exact hkernelBound
  obtain ⟨quotientRank, hquotientCard⟩ :=
    IsPGroup.iff_card.mp (hgroup.to_quotient (frattini source))
  have hquotientRank : quotientRank ≤ 1 :=
    (Nat.pow_le_pow_iff_right hprime.one_lt).mp
      (by simpa only [pow_one] using (hquotientCard ▸ hquotientBound))
  let : IsCyclic (source ⧸ frattini source) := isCyclic_of_card_dvd_prime (p := prime)
    (by
      rw [hquotientCard]
      simpa only [pow_one] using Nat.pow_dvd_pow prime hquotientRank)
  obtain ⟨generator, hgenerator⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (source ⧸ frattini source))
  obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective (frattini source) generator
  have hmap : (Subgroup.zpowers lift).map (QuotientGroup.mk' (frattini source)) = ⊤ := by
    rw [MonoidHom.map_zpowers, hlift, hgenerator]
  have hgenerates : Subgroup.zpowers lift ⊔ frattini source = ⊤ := by
    rw [← QuotientGroup.ker_mk' (frattini source), ← Subgroup.comap_map_eq, hmap]
    exact Subgroup.comap_top _
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨lift, frattini_nongenerating hgenerates⟩


end CFSG.PreuniquenessRankFour.Helpers
