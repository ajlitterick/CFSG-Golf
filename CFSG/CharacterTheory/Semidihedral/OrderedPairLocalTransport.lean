module

public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization
public import CFSG.CharacterTheory.Semidihedral.TwoCoverOddCore
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusionSupport

public noncomputable section

namespace CFSG.Semidihedral.OrderedPairLocalTransport

open CFSG.Open
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.TwoCoverOddCore

universe u v

variable {G : Type u} [Group G]

theorem original_ordered_pair_automorphism (t s i : G)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hcomm : Commute t s) (hne : t ≠ s)
    (hi : i = s ∨ i = t * s) :
    ∃ a : MulAut (Subgroup.closure ({t, s} : Set G)),
      (a ⟨t, Subgroup.subset_closure (by simp)⟩ : G) = i ∧
      (a ⟨s, Subgroup.subset_closure (by simp)⟩ : G) = t := by
  classical
  let V := Subgroup.closure ({t, s} : Set G)
  let : IsKleinFour V := original_four_group_isKleinFour t s ht hs hcomm hne
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hprod := mul_notMem_of_orderOf_eq_two ht hs hne
  have hi1 : i ≠ 1 := by
    rcases hi with rfl | rfl
    · exact hs1
    · intro h
      exact hprod (by simp [h])
  have hit : i ≠ t := by
    rcases hi with rfl | rfl
    · exact hne.symm
    · intro h
      exact hprod (by simp [h])
  have hiV : i ∈ V := by
    rcases hi with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem V (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  let a : V := ⟨t, Subgroup.subset_closure (by simp)⟩
  let b : V := ⟨s, Subgroup.subset_closure (by simp)⟩
  let c : V := ⟨i, hiV⟩
  have ha1 : a ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hb1 : b ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hc1 : c ≠ 1 := fun h => hi1 (congrArg Subtype.val h)
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have hac : a ≠ c := fun h => hit (congrArg Subtype.val h).symm
  let sigma : Equiv.Perm V := Equiv.swap a c * Equiv.swap b c
  have hsigma1 : sigma 1 = 1 := by
    simp only [sigma, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hb1.symm hc1.symm,
      Equiv.swap_apply_of_ne_of_ne ha1.symm hc1.symm]
  let alpha : MulAut V := IsKleinFour.mulEquiv sigma hsigma1
  refine ⟨alpha, ?_, ?_⟩
  · change (sigma a : G) = i
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac,
      Equiv.swap_apply_left]
  · change (sigma b : G) = t
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]

theorem original_ordered_pair_normalizer_conjugator [Finite G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s i : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hcomm : Commute t s) (hne : t ≠ s) (hi : i = s ∨ i = t * s) :
    ∃ g ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G),
      g * t * g⁻¹ = i ∧ g * s * g⁻¹ = t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Subgroup.closure ({t, s} : Set G)
  have hV : IsKleinFour V := original_four_group_isKleinFour t s ht hs hcomm hne
  have hVcard : Nat.card V = 4 := hV.card_four
  have hVtwo : IsPGroup 2 V := IsPGroup.of_card (n := 2) hVcard
  obtain ⟨S, hVS⟩ := hVtwo.exists_le_sylow
  let f : SemidihedralGroup n ≃* S := f0.trans (S0.equiv S)
  obtain ⟨alpha, htalpha, hsalpha⟩ :=
    original_ordered_pair_automorphism t s i ht hs hcomm hne hi
  have hrange := CFSG.Semidihedral.Local.kleinFour_normalizer_image_eq_top hn S f V hVS hV
  obtain ⟨g, hg⟩ : alpha ∈ V.normalizerMonoidHom.range := by
    rw [hrange]
    trivial
  refine ⟨g, g.property, ?_, ?_⟩
  · have h := congrArg (fun a : MulAut V =>
        (a ⟨t, Subgroup.subset_closure (by simp)⟩ : G)) hg
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, htalpha] using h
  · have h := congrArg (fun a : MulAut V =>
        (a ⟨s, Subgroup.subset_closure (by simp)⟩ : G)) hg
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, hsalpha] using h


abbrev originalSection (t : G) : Subgroup (ActualSimpleLayerLocalPackage.H t) :=
  (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)

abbrev originalLayerPreimage (t : G) : Subgroup (C t) :=
  (originalSection t).comap (nu t)

abbrev originalCentralizingResidual (t : G) : Subgroup (C t) :=
  let D := originalLayerPreimage t ⊓ Subgroup.centralizer (N t : Set (C t))
  (CFSG.perfectResidual D).map D.subtype

abbrev originalResidualOverlap (t : G) : Subgroup (C t) :=
  originalCentralizingResidual t ⊓ N t

abbrev originalSylowAmbient {r : ℕ} (t : G) (P : Sylow r (N t)) : Subgroup G :=
  ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype

@[expose] def OriginalLocalDataTransport {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) (i : G') : Prop :=
  (C t).map e.toMonoidHom = C i ∧
  ∃ (c : C t ≃* C i) (a : N t ≃* N i)
    (b : ActualSimpleLayerLocalPackage.H t ≃* ActualSimpleLayerLocalPackage.H i)
    (d : Gamma t ≃* Gamma i)
    (l : CFSG.generalizedFitting (Gamma t) ≃* CFSG.generalizedFitting (Gamma i)),
    (∀ x : C t, (c x : G') = e (x : G)) ∧
    c (tInC t) = tInC i ∧
    (∀ x : N t, (a x : C i) = c (x : C t)) ∧
    (∀ x : C t, b (nu t x) = nu i (c x)) ∧
    (∀ x : C t, d (kappa t x) = kappa i (c x)) ∧
    (∀ x : ActualSimpleLayerLocalPackage.H t,
      d (barKappa t x) = barKappa i (b x)) ∧
    (∀ x : CFSG.generalizedFitting (Gamma t), (l x : Gamma i) = d x) ∧
    (N t).map c.toMonoidHom = N i ∧
    (NZ t).map c.toMonoidHom = NZ i ∧
    (CFSG.generalizedFitting (Gamma t)).map d.toMonoidHom =
      CFSG.generalizedFitting (Gamma i) ∧
    (originalSection t).map b.toMonoidHom = originalSection i ∧
    (originalLayerPreimage t).map c.toMonoidHom = originalLayerPreimage i ∧
    (originalCentralizingResidual t).map c.toMonoidHom = originalCentralizingResidual i ∧
    (originalResidualOverlap t).map c.toMonoidHom = originalResidualOverlap i ∧
    ((N t).map (C t).subtype).map e.toMonoidHom = (N i).map (C i).subtype ∧
    ((originalLayerPreimage t).map (C t).subtype).map e.toMonoidHom =
      (originalLayerPreimage i).map (C i).subtype ∧
    ((originalCentralizingResidual t).map (C t).subtype).map e.toMonoidHom =
      (originalCentralizingResidual i).map (C i).subtype ∧
    Nat.card (N i) = Nat.card (N t)

theorem original_local_data_transport [Finite G] {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) : OriginalLocalDataTransport e t (e t) := by
  let c := PerfectLayerNormalization.originalCentralizerEquiv e t
  let a := PerfectLayerNormalization.originalOddCoreEquiv e t
  let b := PerfectLayerNormalization.originalOddQuotientEquiv e t
  let d := PerfectLayerNormalization.originalReducedQuotientEquiv e t
  let l := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  have hN := PerfectLayerNormalization.originalCentralizerEquiv_maps_oddCore e t
  have hL := PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting d
  obtain ⟨hT, hY⟩ := PerfectLayerNormalization.original_local_layer_preimages_transport e t
  obtain ⟨-, hJ, hE⟩ :=
    PerfectLayerNormalization.original_centralizing_layer_and_overlap_transport e t
  have hcomp : (C (e t)).subtype.comp c.toMonoidHom =
      e.toMonoidHom.comp (C t).subtype := rfl
  have hambient (D : Subgroup (C t)) :
      (D.map (C t).subtype).map e.toMonoidHom =
        (D.map c.toMonoidHom).map (C (e t)).subtype := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  refine ⟨PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t,
    c, a, b, d, l, fun _ => rfl,
    PerfectLayerNormalization.originalCentralizerEquiv_tInC e t,
    PerfectLayerNormalization.originalOddCoreEquiv_coe e t,
    PerfectLayerNormalization.originalOddQuotientEquiv_nu e t,
    PerfectLayerNormalization.originalReducedQuotientEquiv_kappa e t,
    PerfectLayerNormalization.original_quotient_maps_commute e t,
    ?_, hN, PerfectLayerNormalization.originalCentralizerEquiv_maps_fullKernel e t,
    hL, hT, hY, hJ, hE, ?_, ?_, ?_, (Nat.card_congr a.toEquiv).symm⟩
  · intro x
    exact MulEquiv.subgroupCongr_apply
      (PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting d)
      (((CFSG.generalizedFitting (Gamma t)).equivMapOfInjective
        d.toMonoidHom d.injective) x)
  · rw [hambient, hN]
  · rw [hambient, hY]
  · rw [hambient, hJ]

@[expose] def OriginalLayerHypotheses {G : Type} [Group G] (t : G) (p f : ℕ) : Prop :=
  IsSimpleGroup (CFSG.generalizedFitting (Gamma t)) ∧
  (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) ∧
  Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ ∧
  (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P) ∧
  p.Prime ∧ Odd p ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
  CFSG.Assembly.LowTwoRank.StatedClassicalModel (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f

theorem original_layer_hypotheses_transport [Finite G] {G' : Type} [Group G']
    (e : G ≃* G') (t : G) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    OriginalLayerHypotheses (e t) p f := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg
      (Subgroup.map (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom)
      hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  exact ⟨d.symm.isSimpleGroup,
    PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab,
    hcentral', PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc,
    hp, hpodd, hf, hq, PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel⟩

@[expose] def OriginalSylowStationarity (r : ℕ) (P : Subgroup G) : Prop :=
  ∃ P0 : Sylow r (CFSG.oddCore (Subgroup.normalizer (P : Set G))),
    ((P0 : Subgroup _).map (CFSG.oddCore (Subgroup.normalizer (P : Set G))).subtype).map
      (Subgroup.normalizer (P : Set G)).subtype = P

@[expose] def OriginalStationaryCoverAt (t s : G) (r : ℕ) (P : Sylow r (N t)) : Prop :=
  Subgroup.closure ({t, s} : Set G) ≤
    Subgroup.normalizer (originalSylowAmbient t P : Set G) ∧
  OriginalSylowStationarity r (originalSylowAmbient t P) ∧
  (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype) : Set (C t)) ⊓
    originalLayerPreimage t).map (nu t) = originalSection t

@[expose] def OriginalAllPrimeStationaryCover (t s : G) : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], r ∣ Nat.card (N t) →
    ∃ P : Sylow r (N t), OriginalStationaryCoverAt t s r P

theorem original_sylow_centralizer_restriction {r : ℕ} (t : G) (P : Sylow r (N t)) :
    (Subgroup.centralizer (originalSylowAmbient t P : Set G)).subgroupOf (C t) =
      Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype) : Set (C t)) := by
  ext x
  constructor
  · intro hx y hy
    apply Subtype.ext
    exact hx (y : G) (Subgroup.mem_map_of_mem (C t).subtype hy)
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (hx z hz)

theorem original_supplied_stationary_covered_sylow_transport [Finite G]
    {G' : Type v} [Group G'] (e : G ≃* G') {r : ℕ} (hr : r.Prime)
    (t s : G) (P : Sylow r (N t)) (hrN : r ∣ Nat.card (N t))
    (hP : OriginalStationaryCoverAt t s r P) :
    ∃ Q : Sylow r (N (e t)),
      originalSylowAmbient (e t) Q = (originalSylowAmbient t P).map e.toMonoidHom ∧
      r ∣ Nat.card (N (e t)) ∧ OriginalStationaryCoverAt (e t) (e s) r Q := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  obtain ⟨hVP, hstationary, hcover⟩ := hP
  have hstationary' : ∃ P0 : Sylow r (CFSG.pPrimeCore 2
      (Subgroup.normalizer (originalSylowAmbient t P : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (originalSylowAmbient t P : Set G))).subtype).map
        (Subgroup.normalizer (originalSylowAmbient t P : Set G)).subtype =
          originalSylowAmbient t P := by
    unfold OriginalSylowStationarity at hstationary
    rw [StationaryOddLocalization.original_oddCore_eq_twoPrimeCore] at hstationary
    exact hstationary
  have hcover' : ((Subgroup.centralizer (originalSylowAmbient t P : Set G)).subgroupOf (C t) ⊓
      originalLayerPreimage t).map (nu t) = originalSection t := by
    rw [original_sylow_centralizer_restriction]
    exact hcover
  obtain ⟨Q, hQa, hdiv, hVQ, hcov, hstat⟩ :=
    StationaryOddLocalization.actual_stationary_sylow_transport_original_groups
      e hr t s P hrN hVP hcover' hstationary'
  refine ⟨Q, hQa, hdiv, hVQ, ?_, ?_⟩
  · unfold OriginalSylowStationarity
    rw [StationaryOddLocalization.original_oddCore_eq_twoPrimeCore]
    exact hstat
  · rw [← original_sylow_centralizer_restriction]
    exact hcov

@[expose] def OriginalAllPrimeTransport {G' : Type v} [Group G']
    (e : G ≃* G') (t s : G) (i j : G') : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], r ∣ Nat.card (N i) →
    ∃ (P : Sylow r (N t)) (Q : Sylow r (N i)),
      r ∣ Nat.card (N t) ∧ OriginalStationaryCoverAt t s r P ∧
      originalSylowAmbient i Q = (originalSylowAmbient t P).map e.toMonoidHom ∧
      OriginalStationaryCoverAt i j r Q

theorem original_all_prime_stationary_cover_transport [Finite G]
    {G' : Type v} [Group G'] (e : G ≃* G') (t s : G)
    (h : OriginalAllPrimeStationaryCover t s) :
    OriginalAllPrimeTransport e t s (e t) (e s) ∧
      OriginalAllPrimeStationaryCover (e t) (e s) := by
  have htransport : OriginalAllPrimeTransport e t s (e t) (e s) := by
    intro r hr hdiv
    have hdiv' : r ∣ Nat.card (N t) := by
      rw [Nat.card_congr (PerfectLayerNormalization.originalOddCoreEquiv e t).toEquiv]
      exact hdiv
    obtain ⟨P, hP⟩ := h r hdiv'
    obtain ⟨Q, hQ, -, hQP⟩ :=
      original_supplied_stationary_covered_sylow_transport e hr.out t s P hdiv' hP
    exact ⟨P, Q, hdiv', hP, hQ, hQP⟩
  refine ⟨htransport, ?_⟩
  intro r hr hdiv
  obtain ⟨-, Q, -, -, -, hQ⟩ := htransport r hdiv
  exact ⟨Q, hQ⟩


end CFSG.Semidihedral.OrderedPairLocalTransport
