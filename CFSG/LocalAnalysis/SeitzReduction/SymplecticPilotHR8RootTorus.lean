module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR7iii

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem centralizer_ne_top_of_ne_bot_of_simple {G : Type*} [Group G] (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G} (hX : X ≠ ⊥) :
    centralizer (X : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := hnonab
  apply hX
  rcases hG.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
  · rw [eq_bot_iff, ← hZ]
    intro x hx
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (htop ▸ mem_top g) x hx).symm
  · exact absurd (mem_center_iff.mp (hZ ▸ mem_top b) a) hab

theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem prod_ne_two_one_of_two_le {n f : ℕ} (hf : 2 ≤ f) : (n, f) ≠ (2, 1) := by
  intro h
  rw [Prod.mk.injEq] at h
  omega

section RootTorus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbour_overgroup_rootTorusSp {n f : ℕ} (hcat : Sp2mCatalogueClausesAt n)
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (n + 1)) {X : Subgroup G}
    (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      NeighbourOvergroupSp2m (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) n f := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨htX, hcomp, hsyl, hstd, hnn⟩ :=
    neighbour_rootTorusSp_of_three_le hset hq (by omega : 3 ≤ n + 1) e htC ht k hX hD
  obtain ⟨-, -, -, hXcard, -, -, hDXt, -, ⟨ψ⟩, -, -⟩ :=
    neighbour_data_rootTorusSp hq hn e k htC hX hD
  have hDm : LieModel D .PSp n 2 f :=
    lieModel_of_mulEquiv_statedSp ψ hKc hn (prod_ne_two_one_of_two_le hf)
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hXcard
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_bot_of_simple hset.standardSetting.simple
      hset.standardSetting.nonab hXne
  exact ⟨htX, neighbour_overgroup_sp2m hcat hset.standardSetting.kProper hXG htX ht
    (hDXt.trans inf_le_left) hDm hcomp hsyl hstd hnn⟩


theorem neighbour_overgroup_rootTorusSp_of_three_le {m f : ℕ}
    (hcat : Sp2mCatalogueClausesAt (m - 1)) (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hm : 3 ≤ m) (e : L ≃* StatedSp m K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin m) {X : Subgroup G}
    (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      NeighbourOvergroupSp2m (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (m - 1) f := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hcat ⊢
  exact neighbour_overgroup_rootTorusSp hcat hset hKc hf (by omega) e htC ht k hX hD

end RootTorus

end CFSG.SeitzReduction.SymplecticPilot
