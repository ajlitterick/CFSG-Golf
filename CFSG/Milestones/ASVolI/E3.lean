module

public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Background.RonanE338Glue
public import CFSG.Quasithin.H13.E22CHolds

public section

open scoped Pointwise commutatorElement

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.E1 CFSG.Quasithin.A1b


theorem e3_20_fsu_elemAbelian {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hF : CFSG.Quasithin.H13.FSU G T L I) : IsElemAbelian 2 (conjClosure I T) := by
  let ambient := L ⊔ T
  let aggregate := CFSG.Quasithin.primeReducedAggregate ↥ambient 2
  obtain ⟨hNormal, _, hCenter⟩ :=
    CFSG.Quasithin.primeReducedAggregate_normal_elementaryAbelian (E := ↥ambient) 2
  have hMappedNormal : ambient ≤ Subgroup.normalizer
      (CFSG.Quasithin.H13.reducedAggregate ambient : Set G) := by
    have hSubgroup : (CFSG.Quasithin.H13.reducedAggregate ambient).subgroupOf ambient =
        aggregate := Subgroup.comap_map_eq_self_of_injective ambient.subtype_injective _
    have : ((CFSG.Quasithin.H13.reducedAggregate ambient).subgroupOf ambient).Normal := by
      rw [hSubgroup]
      exact hNormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)
  have hContained : conjClosure I T ≤ CFSG.Quasithin.H13.reducedAggregate ambient := by
    refine conjClosure_le fun element hElement generator hGenerator => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (hMappedNormal ((le_sup_right : T ≤ L ⊔ T) hElement)) generator).mp (hF.irrPlus.1 hGenerator)
  have hMem : ∀ element ∈ CFSG.Quasithin.H13.reducedAggregate ambient,
      ∃ internal : ↥ambient, internal ∈ CFSG.pCore 2 ↥ambient ∧
        (∀ other ∈ CFSG.pCore 2 ↥ambient, other * internal = internal * other) ∧
        internal ^ 2 = 1 ∧ (internal : G) = element := by
    rintro element ⟨internal, hInternal, rfl⟩
    obtain ⟨hCore, hCommute, hPower⟩ :=
      CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp (hCenter hInternal)
    exact ⟨internal, hCore, hCommute, hPower, rfl⟩
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun first second => Subtype.ext ?_⟩⟩
    obtain ⟨firstInternal, hCore, _, _, hFirst⟩ := hMem first (hContained first.2)
    obtain ⟨secondInternal, _, hCommute, _, hSecond⟩ := hMem second (hContained second.2)
    change (first : G) * (second : G) = (second : G) * (first : G)
    rw [← hFirst, ← hSecond]
    exact congrArg Subtype.val (hCommute firstInternal hCore)
  · intro element hElement
    obtain ⟨internal, _, _, hPower, rfl⟩ := hMem element (hContained hElement)
    exact congrArg Subtype.val hPower

theorem e3_20_fsu_module : CFSG.Quasithin.H13.StmtFSUModule := by
  intro G _ _ T L I hF
  refine ⟨e3_20_fsu_elemAbelian hF, sup_le ?_ (le_normalizer_conjClosure I T)⟩
  have hNormalizeI := hF.irrPlus.2.2.1
  have hNormalizeL := le_normalizer_conjClosure L T
  have hConjugate : ∀ element ∈ conjClosure L T, ∀ value ∈ conjClosure I T,
      element * value * element⁻¹ ∈ conjClosure I T := by
    intro element hElement value hValue
    induction hValue using Subgroup.closure_induction with
    | mem value hValue =>
      obtain ⟨conjugator, hConjugator, generator, hGenerator, rfl⟩ := hValue
      have hInternal : conjugator⁻¹ * element * conjugator ∈ conjClosure L T := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (hNormalizeL (T.inv_mem hConjugator)) element).mp hElement
        simpa using h
      have hGeneratorImage :
          (conjugator⁻¹ * element * conjugator) * generator *
            (conjugator⁻¹ * element * conjugator)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hNormalizeI hInternal) generator).mp hGenerator
      have hImage := mem_conjClosure hConjugator hGeneratorImage
      simpa [mul_assoc] using hImage
    | one => simp
    | mul first second _ _ hFirst hSecond =>
      simpa [mul_assoc] using (conjClosure I T).mul_mem hFirst hSecond
    | inv value _ hValue =>
      simpa [mul_assoc] using (conjClosure I T).inv_mem hValue
  intro element hElement
  rw [Subgroup.mem_normalizer_iff]
  intro value
  refine ⟨hConjugate element hElement value, fun hValue => ?_⟩
  have h := hConjugate element⁻¹ ((conjClosure L T).inv_mem hElement) _ hValue
  simpa [mul_assoc] using h


section E338


end E338


section E339


end E339


end CFSG.ASVolI
