module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.UnipotentRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCritical
public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalChain

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem class_two_product_power
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source)
    (first second : source) (exponent : ℕ) :
    (first * second) ^ exponent =
      first ^ exponent * second ^ exponent * ⁅second, first⁆ ^ (exponent.choose 2) := by
  have hcentral : ⁅second, first⁆ ∈ Subgroup.center source :=
    hcommutator (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top second) (Subgroup.mem_top first))
  have hcommute : ∀ member : source, Commute ⁅second, first⁆ member := by
    intro member
    exact (Subgroup.mem_center_iff.mp hcentral member).symm
  induction exponent with
  | zero => simp
  | succ exponent hinduction =>
    have hswap : second ^ exponent * first =
        first * second ^ exponent * ⁅second, first⁆ ^ exponent := by
      have hequal := class_two_commutator_pow_left hcommutator second first exponent
      have hraw : second ^ exponent * first = ⁅second, first⁆ ^ exponent * first * second ^ exponent := by
        rw [← hequal]
        simp only [commutatorElement_def]
        group
      rw [hraw, (hcommute first).pow_left exponent]
      rw [mul_assoc, (hcommute (second ^ exponent)).pow_left exponent, ← mul_assoc]
    have hmove : ⁅second, first⁆ ^ (exponent.choose 2) * (first * second) =
        (first * second) * ⁅second, first⁆ ^ (exponent.choose 2) :=
      ((hcommute (first * second)).pow_left _).eq
    rw [pow_succ, hinduction, mul_assoc, hmove]
    calc
      _ =
          first ^ exponent * (second ^ exponent * first) * second *
            ⁅second, first⁆ ^ (exponent.choose 2) := by simp only [mul_assoc]
      _ = first ^ exponent * first * second ^ exponent *
          (⁅second, first⁆ ^ exponent * second) * ⁅second, first⁆ ^ (exponent.choose 2) := by
        rw [hswap]
        simp only [mul_assoc]
      _ = first ^ (exponent + 1) * second ^ (exponent + 1) *
          ⁅second, first⁆ ^ (exponent + exponent.choose 2) := by
        rw [((hcommute second).pow_left exponent).eq]
        simp only [pow_succ, mul_assoc]
        rw [← pow_add]
      _ = _ := by rw [Nat.choose_succ_succ, Nat.choose_one_right]


theorem normal_prime_subgroup_is_central
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hcard : Nat.card normal = prime) :
    normal ≤ Subgroup.center source := by
  have hnontrivial : normal ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Fact.out : prime.Prime).ne_one hcard.symm
  obtain ⟨line, hline, hcentral, hlineCard, _⟩ :=
    normal_pSubgroup_has_central_prime_line prime hsource normal hnontrivial
  have hequal : line = normal := Subgroup.eq_of_le_of_card_ge hline (by omega)
  exact hequal ▸ hcentral


theorem normal_elementary_contains_ambient_normal_elementary_of_each_rank
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnormal : IsElemAbelian prime normal)
    (rank : ℕ) (hcard : Nat.card normal = prime ^ rank) (width : ℕ) (hwidth : width ≤ rank) :
    ∃ elementary : Subgroup source, elementary ≤ normal ∧ elementary.Normal ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ width := by
  obtain ⟨elementary, hcontained, helementaryNormal, helementaryCard⟩ :=
    normal_pSubgroup_has_ambient_normal_subgroup_of_each_order
      prime rank hsource normal (inferInstance : normal.Normal) hcard width hwidth
  have helementary : IsElemAbelian prime elementary := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      let : IsMulCommutative normal := hnormal.1
      let : CommGroup normal := IsMulCommutative.instCommGroup
      exact congrArg (fun member : normal => (member : source))
        (mul_comm (⟨first, hcontained first.property⟩ : normal)
          (⟨second, hcontained second.property⟩ : normal))
    · intro member hmember
      exact hnormal.2 member (hcontained hmember)
  exact ⟨elementary, hcontained, helementaryNormal, helementary, helementaryCard⟩


theorem no_normal_elementary_rank_two_forces_normal_abelian_cyclic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hnormalElementary : ∀ elementary : Subgroup source, elementary.Normal →
      IsElemAbelian prime elementary → Nat.card elementary ≠ prime ^ 2)
    (abelian : Subgroup source) [abelian.Normal] (habelian : IsMulCommutative abelian) :
    IsCyclic abelian := by
  by_contra hnoncyclic
  let : IsMulCommutative abelian := habelian
  let : CommGroup abelian := IsMulCommutative.instCommGroup
  let torsion := centralPrimeTorsion prime abelian
  let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
  let image := torsion.map abelian.subtype
  let : image.Normal := inferInstance
  have himageElementary := elementary_abelian_map prime (centralPrimeTorsion_elementary prime) abelian.subtype
  have hlarge : 2 ≤ pRank prime image := by
    rw [pRank_map_of_injective prime (Fact.out : prime.Prime) abelian.subtype Subtype.val_injective,
      centralPrimeTorsion_rank_eq_center_rank prime (Fact.out : prime.Prime), Subgroup.center_eq_top]
    exact noncyclic_commutative_pGroup_rank_at_least_two
      prime (Fact.out : prime.Prime) (hsource.to_subgroup abelian) hnoncyclic
  obtain ⟨rank, himageCard⟩ := (hsource.to_subgroup image).exists_card_eq
  have hrank : 2 ≤ rank := by
    obtain ⟨witness, hcontained, _, hwitnessCard⟩ :=
      pRank_attained prime (Fact.out : prime.Prime) image
    have hcardBound := Subgroup.card_le_of_le hcontained
    rw [hwitnessCard, himageCard] at hcardBound
    exact hlarge.trans ((Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hcardBound)
  obtain ⟨small, _, hsmallNormal, hsmallElementary, hsmallCard⟩ :=
    normal_elementary_contains_ambient_normal_elementary_of_each_rank
      prime hsource image himageElementary rank himageCard 2 hrank
  exact hnormalElementary small hsmallNormal hsmallElementary hsmallCard

theorem odd_prime_class_two_power_monoidHom
    {source : Type u} [Group source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source) :
    ∃ hom : source →* source, ∀ member : source, hom member = member ^ prime := by
  refine ⟨{ toFun := fun member => member ^ prime, map_one' := one_pow _, map_mul' := ?_ }, fun _ => rfl⟩
  intro first second
  have hlarge : 2 < prime := by
    have hlower := (Fact.out : prime.Prime).two_le
    omega
  obtain ⟨correction, hcorrection⟩ := (Fact.out : prime.Prime).dvd_choose_self (by omega) hlarge
  have hcommutatorPower := commutator_pow_prime_eq_one_of_powers_central
    prime hcommutator hpowers second first
  rw [class_two_product_power hcommutator, hcorrection, pow_mul,
    hcommutatorPower, one_pow, mul_one]

theorem power_monoidHom_kernel_characteristic
    {source : Type u} [Group source] (exponent : ℕ) (hom : source →* source)
    (hhom : ∀ member : source, hom member = member ^ exponent) : hom.ker.Characteristic := by
  apply Subgroup.characteristic_iff_comap_eq.mpr
  intro automorphism
  ext member
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker, hhom, ← map_pow]
  exact automorphism.map_eq_one_iff

theorem normal_prime_cube_elementary_central_extension_has_normal_elementary_rank_two
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (normal line : Subgroup source) [normal.Normal] [line.Normal]
    (hnormalCard : Nat.card normal = prime ^ 3) (hlineCard : Nat.card line = prime)
    (hcommutator : ⁅normal, normal⁆ ≤ line)
    (hpowers : ∀ member ∈ normal, member ^ prime ∈ line) :
    ∃ elementary : Subgroup source, elementary ≤ normal ∧ elementary.Normal ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  have hlineCentral := normal_prime_subgroup_is_central prime hsource line hlineCard
  have hclassTwo : commutator normal ≤ Subgroup.center normal := by
    apply Subgroup.commutator_le.mpr
    intro first _ second _
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hlineCentral (hcommutator (Subgroup.commutator_mem_commutator
        first.property second.property))) (other : source)
  have hpowersLocal : ∀ member : normal, member ^ prime ∈ Subgroup.center normal := by
    intro member
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hlineCentral (hpowers member member.property)) (other : source)
  obtain ⟨hom, hhom⟩ := odd_prime_class_two_power_monoidHom prime hodd hclassTwo hpowersLocal
  let : hom.ker.Characteristic := power_monoidHom_kernel_characteristic prime hom hhom
  let image := hom.ker.map normal.subtype
  let : image.Normal := inferInstance
  have hrange : hom.range.map normal.subtype ≤ line := by
    rintro member ⟨lift, ⟨preimage, hpreimage⟩, rfl⟩
    rw [← hpreimage, hhom]
    exact hpowers preimage preimage.property
  have hrangeCard : Nat.card hom.range ≤ prime := by
    have hbound := Subgroup.card_le_of_le hrange
    rwa [Subgroup.card_map_of_injective Subtype.val_injective, hlineCard] at hbound
  obtain ⟨kernelRank, hkernelCard⟩ := ((hsource.to_subgroup normal).to_subgroup hom.ker).exists_card_eq
  have hkernelRank : 2 ≤ kernelRank := by
    have hsourceCard : Nat.card normal = Nat.card hom.range * Nat.card hom.ker := by
      rw [hom.ker.card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange hom).toEquiv]
    have hbound : prime ^ 3 ≤ prime * prime ^ kernelRank := by
      rw [← hnormalCard, hsourceCard, ← hkernelCard]
      exact Nat.mul_le_mul_right _ hrangeCard
    rw [← pow_succ'] at hbound
    have hrankBound := (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    omega
  have himageCard : Nat.card image = prime ^ kernelRank := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hkernelCard]
  obtain ⟨elementary, hcontained, helementaryNormal, helementaryCard⟩ :=
    normal_pSubgroup_has_ambient_normal_subgroup_of_each_order
      prime kernelRank hsource image (inferInstance : image.Normal) himageCard 2 hkernelRank
  refine ⟨elementary, hcontained.trans (Subgroup.map_subtype_le _), helementaryNormal,
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq helementaryCard, ?_⟩, helementaryCard⟩
  intro member hmember
  obtain ⟨lift, hlift, rfl⟩ := hcontained hmember
  have hpower : lift ^ prime = 1 := (hhom lift).symm.trans hlift
  exact congrArg (fun value : normal => (value : source)) hpower

theorem odd_pGroup_noncyclic_has_normal_elementary_rank_two
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (cardinality : ℕ) :
    ∀ {source : Type u} [Group source] [Finite source], Nat.card source = cardinality →
      IsPGroup prime source → ¬ IsCyclic source →
        ∃ elementary : Subgroup source, elementary.Normal ∧
          IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  induction cardinality using Nat.strong_induction_on with
  | h cardinality hinduction =>
    intro source _ _ hcardinality hsource hnoncyclic
    classical
    by_contra hnone
    have hnoNormal : ∀ elementary : Subgroup source, elementary.Normal →
        IsElemAbelian prime elementary → Nat.card elementary ≠ prime ^ 2 := by
      intro elementary hnormal helementary hcard
      exact hnone ⟨elementary, hnormal, helementary, hcard⟩
    let : Nontrivial source := not_subsingleton_iff_nontrivial.mp (by
      intro htrivial
      let : Subsingleton source := htrivial
      exact hnoncyclic inferInstance)
    obtain ⟨line, _, hlineCentral, hlineCard, hlineNormal⟩ :=
      normal_pSubgroup_has_central_prime_line prime hsource (⊤ : Subgroup source) top_ne_bot
    let : line.Normal := hlineNormal
    let quotientMap := QuotientGroup.mk' line
    have hquotientSmall : Nat.card (source ⧸ line) < cardinality := by
      have hproduct := line.card_eq_card_quotient_mul_card_subgroup
      rw [hlineCard, hcardinality] at hproduct
      have hpositive : 0 < Nat.card (source ⧸ line) := Nat.card_pos
      have hprime := (Fact.out : prime.Prime).one_lt
      nlinarith
    by_cases hquotientCyclic : IsCyclic (source ⧸ line)
    · let : IsCyclic (source ⧸ line) := hquotientCyclic
      let : IsMulCommutative source := quotientMap.isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk']; exact hlineCentral)
      let : IsCyclic (⊤ : Subgroup source) := no_normal_elementary_rank_two_forces_normal_abelian_cyclic
        prime hsource hnoNormal (⊤ : Subgroup source) inferInstance
      exact hnoncyclic (isCyclic_of_surjective (⊤ : Subgroup source).subtype (by
        intro member
        exact ⟨⟨member, Subgroup.mem_top member⟩, rfl⟩))
    · obtain ⟨quotientElementary, hquotientNormal, hquotientElementary, hquotientCard⟩ :=
        hinduction _ hquotientSmall rfl (hsource.to_quotient line) hquotientCyclic
      let : quotientElementary.Normal := hquotientNormal
      let preimage := quotientElementary.comap quotientMap
      let : preimage.Normal := inferInstance
      have hpreimageCard : Nat.card preimage = prime ^ 3 := by
        rw [surjective_hom_preimage_card quotientMap (QuotientGroup.mk'_surjective line),
          QuotientGroup.ker_mk', hlineCard, hquotientCard]
        simp only [pow_succ]
      have hcommutatorImage : ⁅preimage, preimage⁆ ≤ line := by
        apply Subgroup.commutator_le.mpr
        intro first hfirst second hsecond
        apply (QuotientGroup.eq_one_iff _).mp
        change quotientMap ⁅first, second⁆ = 1
        rw [map_commutatorElement]
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        let : IsMulCommutative quotientElementary := hquotientElementary.1
        let : CommGroup quotientElementary := IsMulCommutative.instCommGroup
        exact congrArg (fun value : quotientElementary => (value : source ⧸ line))
          (mul_comm (⟨quotientMap first, hfirst⟩ : quotientElementary)
            (⟨quotientMap second, hsecond⟩ : quotientElementary))
      obtain ⟨elementary, _, helementaryNormal, helementary, helementaryCard⟩ :=
        normal_prime_cube_elementary_central_extension_has_normal_elementary_rank_two
          prime hodd hsource preimage line hpreimageCard hlineCard hcommutatorImage (by
            intro member hmember
            apply (QuotientGroup.eq_one_iff _).mp
            change quotientMap (member ^ prime) = 1
            rw [map_pow]
            exact hquotientElementary.2 _ hmember)
      exact hnoNormal elementary helementaryNormal helementary helementaryCard


end CFSG.PreuniquenessRankFour.Helpers
