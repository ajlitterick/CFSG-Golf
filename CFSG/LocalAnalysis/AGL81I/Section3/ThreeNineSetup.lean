module

public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)

local notation "pRank" => CFSG.Open.pRank

variable {G : Type} [Group G] [Finite G]


theorem le_gammaIn_self {k p : ℕ} {D T : Subgroup G} (hDT : D ≤ T)
    (hrank : k ≤ pRank p (D.subgroupOf T)) : D ≤ gammaIn k p D T := by
  have hself : D.subgroupOf T ≤ Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T) :=
    Subgroup.le_normalizer
  have hcore : Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T) ≤
      CFSG.Open.rankThreeGamma k p (D.subgroupOf T) :=
    CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le k p (D.subgroupOf T)
      (D.subgroupOf T) le_rfl hrank
  calc
    D = (D.subgroupOf T).map T.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDT]
    _ ≤ (Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T)).map T.subtype :=
      Subgroup.map_mono hself
    _ ≤ (CFSG.Open.rankThreeGamma k p (D.subgroupOf T)).map T.subtype :=
      Subgroup.map_mono hcore
    _ = gammaIn k p D T := rfl


theorem threeNine_D_faithful (X : Type) [Group X] [Finite X]
    (K E D X₁ : Subgroup X) (p d : ℕ)
    (_hp : p.Prime) (_hp2 : p ≠ 2)
    (_hKq : CFSG.IsQuasisimple ↥K)
    (_hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (_hKcat : CFSG.SectionRank.IsKGroupCat ↥K)
    (hKnorm : K.Normal)
    (_hrank1 : 1 < CFSG.Open.pRank p (⊤ : Subgroup X))
    (_hrank3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (_hEel : CFSG.Open.IsElemAbelian p E) (_hEcard : Nat.card E = p ^ 2)
    (hdp : d.Prime) (_hd2 : d ≠ 2) (_hdpne : d ≠ p)
    (hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (_hDne : D ≠ ⊥)
    (hX1 : X₁ < K ⊔ D)
    (_hΓE : gammaIn 1 p E (K ⊔ D) ≤ X₁)
    (hΓD : gammaIn 1 d D (K ⊔ D) ≤ X₁)
    (_hN : ∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁) :
    D ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  have hfact : Fact d.Prime := ⟨hdp⟩
  have hKN : K.Normal := hKnorm
  have hDp : IsPGroup d D := hDsyl.isPGroup
  have hNil : Group.IsNilpotent ↥D := hDp.isNilpotent
  by_contra hne
  set T : Subgroup X := K ⊔ D with hT
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  set H : Subgroup X := D ⊓ C with hH
  have hDT : D ≤ T := by rw [hT]; exact le_sup_right
  have hKT : K ≤ T := by rw [hT]; exact le_sup_left
  have hHD : H ≤ D := by rw [hH]; exact inf_le_left
  have hHne : H ≠ ⊥ := by rw [hH]; exact hne
  have hΓD' : gammaIn 1 d D T ≤ X₁ := by rw [hT]; exact hΓD
  have hX1' : X₁ < T := by rw [hT]; exact hX1
  have hCN : C.Normal := by rw [hC]; infer_instance
  have hHsubne : H.subgroupOf D ≠ ⊥ := by
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff, inf_eq_left.mpr hHD] at hbot
    exact hHne hbot
  have hHnorm : (H.subgroupOf D).Normal := by
    have hCH : H.subgroupOf D = C.subgroupOf D := by
      rw [hH]
      exact Subgroup.inf_subgroupOf_left C D
    rw [hCH]
    infer_instance
  let A : Subgroup ↥D := H.subgroupOf D ⊓ Subgroup.center (↥D)
  have hAne : A ≠ ⊥ := by
    dsimp [A]
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥D) hHsubne
  have hAp : IsPGroup d A := hDp.to_subgroup A
  let Q : Subgroup T := A.map (Subgroup.inclusion hDT)
  have hQne : Q ≠ ⊥ := by
    dsimp [Q]
    rw [Subgroup.map_eq_bot_iff_of_injective (H := A) (Subgroup.inclusion_injective hDT)]
    exact hAne
  have hQp : IsPGroup d Q := by
    dsimp [Q]
    exact hAp.of_equiv (A.equivMapOfInjective (Subgroup.inclusion hDT)
      (Subgroup.inclusion_injective hDT))
  have hQleD : Q ≤ D.subgroupOf T := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, _ha, rfl⟩ := Subgroup.mem_map.mp hq
    exact Subgroup.mem_subgroupOf.mpr a.2
  have hQdvd : d ∣ Nat.card Q :=
    hQp.card_eq_or_dvd.resolve_left fun h => hQne (Subgroup.card_eq_one.mp h)
  have hQrank : 1 ≤ pRank d Q := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) Q]
    exact CFSG.one_le_pRank_of_dvd_card hdp hQdvd
  have hAleH : A ≤ H.subgroupOf D := by dsimp [A]; exact inf_le_left
  have hAleZ : A ≤ Subgroup.center (↥D) := by dsimp [A]; exact inf_le_right
  have hQK : Q ≤ Subgroup.centralizer (K.subgroupOf T : Set T) := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    have haH : ((a : D) : X) ∈ H := hAleH ha
    have haH' : ((a : D) : X) ∈ D ⊓ C := by rwa [hH] at haH
    have haC : ((a : D) : X) ∈ Subgroup.centralizer (K : Set X) := haH'.2
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro k hk
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp haC (k : X)
      (Subgroup.mem_subgroupOf.mp hk))
  have hQD : Q ≤ Subgroup.centralizer (D.subgroupOf T : Set T) := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    have haZ : a ∈ Subgroup.center (↥D) := hAleZ ha
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro d hd
    exact Subtype.ext (congrArg (fun z : ↥D => (z : X))
      (Subgroup.mem_center_iff.mp haZ ⟨(d : X), Subgroup.mem_subgroupOf.mp hd⟩))
  have hKQT : K.subgroupOf T ≤ Subgroup.centralizer (Q : Set T) :=
    (Subgroup.le_centralizer_iff).mp hQK
  have hDQT : D.subgroupOf T ≤ Subgroup.centralizer (Q : Set T) :=
    (Subgroup.le_centralizer_iff).mp hQD
  have hTQ : (⊤ : Subgroup T) ≤ Subgroup.centralizer (Q : Set T) := by
    have hsup : K.subgroupOf T ⊔ D.subgroupOf T = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKT hDT, hT, Subgroup.subgroupOf_self]
    rw [← hsup]
    exact sup_le hKQT hDQT
  have hQnorm : Subgroup.normalizer (Q : Set T) = ⊤ :=
    eq_top_iff.mpr (hTQ.trans (Subgroup.centralizer_le_normalizer (Q : Set T)))
  have hcore : CFSG.Open.rankThreeGamma 1 d (D.subgroupOf T) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hQnorm]
    exact CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 d
      (D.subgroupOf T) Q hQleD hQrank
  have hgamma : gammaIn 1 d D T = T := by
    rw [gammaIn, hcore, Subgroup.map_top, Subgroup.range_subtype]
  have hTleX1 : T ≤ X₁ := by
    rw [← hgamma]
    exact hΓD'
  exact (ne_of_lt hX1') (le_antisymm hX1'.le hTleX1)

end CFSG.LocalAnalysis.AGL81I.Section3
