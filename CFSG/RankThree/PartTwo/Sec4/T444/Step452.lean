module

public import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.Sec4.T444.QAction
public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec4.T444.Step451

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

section General

variable {X : Type*} [Group X]

theorem isSolvable_comap_mk' {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N)
    {H : Subgroup (X ⧸ N)} (hH : Group.IsSolvable H) :
    Group.IsSolvable (H.comap (QuotientGroup.mk' N)) := by
  have hNle : N ≤ H.comap (QuotientGroup.mk' N) := fun x hx => by
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [Subgroup.mem_comap, h1]
    exact one_mem _
  set g : H.comap (QuotientGroup.mk' N) →* H :=
    ((QuotientGroup.mk' N).comp (Subgroup.subtype _)).codRestrict H (fun x => x.2) with hg
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNle) g ?_
  intro x hx
  have h1 : QuotientGroup.mk' N (x : X) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩

variable [Finite X]

theorem isSolvable_oTwoFitting : Group.IsSolvable (oTwoFitting X) := by
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  exact isSolvable_comap_mk' inferInstance inferInstance

theorem isSolvable_oTwoP (p : ℕ) [Fact p.Prime] : Group.IsSolvable (oTwoP p X) := by
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  have : Group.IsNilpotent (CFSG.pCore p (X ⧸ CFSG.pCore 2 X)) := CFSG.pCore_isPGroup.isNilpotent
  exact isSolvable_comap_mk' inferInstance inferInstance

theorem false_of_surjective_of_isCyclic_sylow {Y : Type*} [Group Y] [Finite Y] (F : X →* Y)
    (hF : Function.Surjective F) (hcyc : ∀ S : Sylow 3 X, IsCyclic S) {E : Subgroup Y}
    (hexp : Monoid.exponent E ∣ 3) (hcard : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := E.comap F with hW
  set ψ : W →* E := (F.comp W.subtype).codRestrict E (fun w => w.2) with hψ
  have hψs : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hF e
    exact ⟨⟨x, show F x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 W) := inferInstance
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have htop : ((T.mapSurjective hψs : Sylow 3 E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψs).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hT'p : IsPGroup 3 T' := T.isPGroup'.map _
  obtain ⟨S, hS⟩ := hT'p.exists_le_sylow
  have : IsCyclic S := hcyc S
  have hT'c : IsCyclic T' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom (MulEquiv.surjective _)
  have hTc : IsCyclic T :=
    isCyclic_of_surjective
      ((T : Subgroup W).equivMapOfInjective W.subtype W.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hEc : IsCyclic E := by
    refine isCyclic_of_surjective (ψ.comp (T : Subgroup W).subtype) ?_
    intro e
    have he : e ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top e
    obtain ⟨t, ht, rfl⟩ := he
    exact ⟨⟨t, ht⟩, rfl⟩
  have hexp' := IsCyclic.exponent_eq_card (α := E)
  rw [hcard] at hexp'
  rw [hexp'] at hexp
  norm_num at hexp

end General

section Exclusion


variable {X : Type} [Group X] [Finite X]


end Exclusion

section Main

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem Ctx444.le_normalizer_of_mem_thetaComponents (h45 : Item4_5) (h : Ctx444 G A M)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) : A ≤ Subgroup.normalizer (L : Set G) :=
  h45 G h.sectionFourHyp A h.isE27.isPGroup
    (Or.inr ⟨h.isE27.1, 3, le_rfl, by rw [h.isE27.2]; norm_num⟩) L hL

theorem Ctx444.three_dvd_card_of_not_le (h45 : Item4_5) (h : Ctx444 G A M) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M) : 3 ∣ Nat.card L := by
  by_contra h3
  exact hLM (h.le_of_le_normalizer (h.le_normalizer_of_mem_thetaComponents h45 hL) h3)

theorem not_map_le_centralizer_of_commutator_eq {Q L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L) (hcomm : ⁅L, Q⁆ = L) :
    ¬ Q.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  intro hle
  have hJ := isComponent_map_starQuot hL h3
  have hbot : (⁅L, Q⁆).map (starQuot G) = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [hcomm] at hbot
  have : Nontrivial (L.map (starQuot G)) := isQuasisimple_nontrivial hJ.1
  rw [hbot] at this
  exact (not_nontrivial (⊥ : Subgroup (G ⧸ CFSG.pPrimeCore 3 G))) this

theorem Ctx444.isZ3L34OrHeisSL34_map_starQuot (h434 : Item4_34Sec) (h45 : Item4_5)
    (h : Ctx444 G A M) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hQL : inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ⁅L, inSubgroup (CFSG.pPrimeCore 3) M⁆ = L) (hLM : ¬ L ≤ M) :
    IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G)) := by
  set Q := inSubgroup (CFSG.pPrimeCore 3) M with hQ
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hQ3 : ¬ 3 ∣ Nat.card Q := not_three_dvd_card_inSubgroup_pPrimeCore M
  obtain ⟨r, _, S, hAS, hSne⟩ := exists_sylow_not_le_centralizer hA3 hQ3
    h.le_normalizer_inSubgroup (not_map_le_centralizer_of_commutator_eq hL h3L hcomm)
  set R := (S : Subgroup Q).map Q.subtype with hR
  have hRQ : R ≤ Q := Subgroup.map_subtype_le _
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le hRQ))
  have hRp : IsPGroup r R := S.isPGroup'.map _
  have hs : Group.IsSolvable (A ⊔ R : Subgroup G) :=
    isSolvable_sup_of_le_normalizer (isSolvable_of_isPGroup hA3) (isSolvable_of_isPGroup hRp) hAS
  exact isZ3L34OrHeisSL34_of_item4_34Sec h434 h hL h3L hLM hAL (hRQ.trans hQL) hAS hR3 hs hSne


end Main

end CFSG.RankThree.PartTwo.Sec4
