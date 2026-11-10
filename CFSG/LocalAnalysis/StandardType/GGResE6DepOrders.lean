module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Final.Orders
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4h_factorization_two_of_profile {m N : ℕ} {Z : ℕ → Prop}
    (h : CFSG.Timmesfeld.Orders.Profile m N Z) : m.factorization 2 = N := by
  obtain ⟨r, hr, hm⟩ := h.two
  have hr2 : ¬ 2 ∣ r := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hr
  have h2 : (2 ^ N * r).factorization 2 = N := by
    rw [Nat.factorization_mul (pow_ne_zero N (by norm_num)) hr.pos.ne']
    change (2 ^ N).factorization 2 + r.factorization 2 = N
    rw [Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hr2, add_zero]
  rwa [hm]

theorem l05nL4h_markedModel
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hperf : commutator X = ⊤)
    (hnt : Nontrivial (X ⧸ Subgroup.center X)) (hlab : LargeEvenInLambda2 lab)
    (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hperf hnt
  obtain ⟨R, _, I, F, ⟨e⟩, hm⟩ := largeEvenRawDatum_exists
    (largeEvenRawDatum_markedModel hlab
      (Q := fun R' _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R'))
      (by rintro R _ I F ⟨e⟩; exact nonabelian_of_mulEquiv e ⟨a, b, hab⟩)
      hl)
  exact MarkedModel.of_mulEquiv e.symm hm

private theorem l05nL4h_card_A5 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hA : GGA5Label lab) (hm : MarkedModel lab R) :
    (lab.tag = .A → Nat.card R = CFSG.Open.ordA 5 (2 ^ lab.n)) ∧
    (lab.tag = .twA → Nat.card R = CFSG.Open.ordTwistedA 5 (2 ^ lab.n)) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · have hmodel : LieModel R .PSL 6 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht, hA.1] using hm
    simpa using CFSG.GH74.card_of_lieModel_PSL (by norm_num : (6 : ℕ) ≠ 0) hmodel
  · have hmodel : LieModel R .PSU 6 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht, hA.1] using hm
    have hc := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num : (6 : ℕ) ≠ 0) hmodel
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl

private theorem l05nL4h_card_E6 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hE : GGE6DepLabel lab) (hm : MarkedModel lab R) :
    (lab.tag = .E6 → Nat.card R = CFSG.Open.ordE6 (2 ^ lab.n)) ∧
    (lab.tag = .twE6 → Nat.card R = CFSG.Open.ordTwistedE6 (2 ^ lab.n)) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · have hmodel : LieModel R .E6 0 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hm
    have hc := CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel
      (by decide : StatedLieTag.E6 ∈ CFSG.Blueprint.chevalleyExceptionalTags) hmodel
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
  · have hmodel : LieModel R .twistedE6 0 2 lab.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hm
    have hc := CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel
      (by decide : StatedLieTag.twistedE6 ∈ CFSG.Blueprint.chevalleyExceptionalTags) hmodel
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc

private theorem l05nL4h_two_part_A5 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hA : GGA5Label lab) (hm : MarkedModel lab R) :
    (Nat.card R).factorization 2 = 15 * lab.n := by
  rcases hA.2 with ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [(l05nL4h_card_A5 hA hm).1 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordA (n := 5) (f := lab.n)
      (by norm_num) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [show 5 * (5 + 1) / 2 = 15 by norm_num, Nat.mul_comm] using this
  · rw [(l05nL4h_card_A5 hA hm).2 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 5) (g := lab.n)
      (by norm_num) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [show 5 * (5 + 1) / 2 = 15 by norm_num, Nat.mul_comm] using this

private theorem l05nL4h_two_part_E6 {R : Type} [Group R] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hE : GGE6DepLabel lab) (hm : MarkedModel lab R) :
    (Nat.card R).factorization 2 = 36 * lab.n := by
  have hcard := l05nL4h_card_E6 hE hm
  rcases hE with ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [hcard.1 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordE6 (f := lab.n) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [Nat.mul_comm] using this
  · rw [hcard.2 ht]
    have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedE6 (f := lab.n) hlab.1
    have := l05nL4h_factorization_two_of_profile hprof
    simpa [Nat.mul_comm] using this


theorem ggResE6Dep_two_part_ge_A5
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hperf : commutator X = ⊤)
    (hnt : Nontrivial (X ⧸ Subgroup.center X)) (hlab : LargeEvenInLambda2 lab)
    (hA : GGA5Label lab) (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    15 * lab.n ≤ (Nat.card X).factorization 2 := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  have hfacR := l05nL4h_two_part_A5 hlab hA hm
  have hZ0 : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hle : (Nat.card (X ⧸ Subgroup.center X)).factorization 2 ≤
      (Nat.card X).factorization 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
    exact (Nat.factorization_le_factorization_mul_left hZ0) 2
  rw [hfacR] at hle
  exact hle

theorem ggResE6Dep_two_part_le_E6
    {X : Type} [Group X] [Finite X] {lab : LargeEvenLabel} (hT3 : GGSchurDvdInput)
    (hperf : commutator X = ⊤) (hnt : Nontrivial (X ⧸ Subgroup.center X))
    (hlab : LargeEvenInLambda2 lab) (hE : GGE6DepLabel lab)
    (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    (Nat.card X).factorization 2 ≤ 36 * lab.n + 2 := by
  have hm := l05nL4h_markedModel hperf hnt hlab hl
  have hfacR := l05nL4h_two_part_E6 hlab hE hm
  have hZ12 : Nat.card (Subgroup.center X) ∣ 12 := hT3 X lab hperf hlab (Or.inl hE) hl
  have hZ0 : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hQ0 : Nat.card (X ⧸ Subgroup.center X) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hZfac : (Nat.card (Subgroup.center X)).factorization 2 ≤ 2 := by
    have h := ((Nat.factorization_le_iff_dvd hZ0 (by norm_num : (12 : ℕ) ≠ 0)).2 hZ12) 2
    have h12 : (12 : ℕ).factorization 2 = 2 := by
      rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num)]
      change (2 ^ 2).factorization 2 + (3 : ℕ).factorization 2 = 2
      rw [Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
    rwa [h12] at h
  have hfacX : (Nat.card X).factorization 2 =
      (Nat.card (X ⧸ Subgroup.center X)).factorization 2 +
        (Nat.card (Subgroup.center X)).factorization 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      Nat.factorization_mul hQ0 hZ0]
    rfl
  rw [hfacX, hfacR]
  omega


end CFSG.StandardType
