module

public import CFSG.Quasithin.Background.A3Structure320Radical
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A3Structure320Basic

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

@[expose] def RadicalShape (L : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card (solvRad L) ∨ (Nat.card (solvRad L) = 3 ∧ ⁅solvRad L, L⁆ = ⊥)

omit [Finite G] in
theorem zpowers_inf_radical {L : Subgroup G} {x : G} (hx : orderOf x = 3)
    (hxR : x ∉ solvRad L) {y : G} (hy : y ∈ Subgroup.zpowers x) (hyR : y ∈ solvRad L) :
    y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy1
  exact hxR ((Subgroup.zpowers_le.2 hyR) (mem_zpowers_of_mem_zpowers_prime hx hy hy1))

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem pRank_centralizer_le {L : Subgroup G} [L.Normal] (hL : L ∈ cComp (⊤ : Subgroup G))
    (hG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2) (hR : RadicalShape L)
    (h3 : 1 ≤ CFSG.Open.pRank 3 L) : CFSG.Open.pRank 3 (centralizerModSolvRad L) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (solvRad L).Normal := solvRad_normal_of_normal L
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hEC, hEel, hEcard⟩ := exists_pRank (p := 3) (by norm_num) (centralizerModSolvRad L)
  have hinfL := centralizerModSolvRad_inf_le hL
  rcases hR with hR3 | ⟨hR3, hRc⟩
  ·
    obtain ⟨X, hXL, hXel, hXcard⟩ := exists_subgroup_card_prime (p := 3) h3
    have hmain := pRank_add_le (solvRad L) hR3 hXel hEel
      (fun x hx e he => by
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ ((hEC he).2 x (hXL hx)))
      (fun x hx e he hxe => by
        have heL : e ∈ L := by
          have : e = x⁻¹ * (x * e) := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXL hx)) (solvRad_le L hxe)
        have heR : e ∈ solvRad L := hinfL ⟨hEC he, heL⟩
        have hxR : x ∈ solvRad L := by
          have : x = (x * e) * e⁻¹ := by group
          rw [this]
          exact Subgroup.mul_mem _ hxe (Subgroup.inv_mem _ heR)
        exact ⟨eq_one_of_pow_eq_one_of_not_dvd hR3 hxR (hXel.2 x hx),
          eq_one_of_pow_eq_one_of_not_dvd hR3 heR (hEel.2 e he)⟩)
      (a := 1) (b := CFSG.Open.pRank 3 (centralizerModSolvRad L)) (by simpa using hXcard) hEcard
    omega
  ·
    have hperf := perfect_of_mem_cComp hL
    have hperfL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
      A36A.top_commutator_of_mem_cComp hL
    have hZc : (solvRad L).subgroupOf L ≤ Subgroup.center ↥L := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ⁅(z : G), (g : G)⁆ ∈ (⊥ : Subgroup G) :=
        hRc ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hz) g.2
      have h2 : ⁅z, g⁆ = 1 := Subtype.ext (Subgroup.mem_bot.1 h1)
      exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
    have hZ : Nat.card ((solvRad L).subgroupOf L) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toEquiv).trans hR3
    obtain ⟨x, hx3, hxZ⟩ := exists_orderOf_eq_three_not_mem hperfL hZc hZ
    have hxR : (x : G) ∉ solvRad L := fun h => hxZ (Subgroup.mem_subgroupOf.2 h)
    have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx3
    have hxL : (x : G) ∈ L := x.2
    have hxp : (x : G) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    have hmain := pRank_add_le (⊥ : Subgroup G) (by simp) (isElemAbelian_zpowers hxp) hEel
      (fun y hy e he => by
        have hyL : y ∈ L := (Subgroup.zpowers_le.2 hxL) hy
        have h1 := centralizes_of_central_radical hperf hRc (hEC he) hyL
        rw [← commutatorElement_inv, h1, inv_one]
        exact Subgroup.one_mem _)
      (fun y hy e he hye => by
        have hye1 : y * e = 1 := Subgroup.mem_bot.1 hye
        have hyL : y ∈ L := (Subgroup.zpowers_le.2 hxL) hy
        have hye' : y = e⁻¹ := eq_inv_of_mul_eq_one_left hye1
        have heL : e ∈ L := by
          have : e = y⁻¹ := (inv_eq_of_mul_eq_one_right hye1).symm
          rw [this]
          exact Subgroup.inv_mem _ hyL
        have heR : e ∈ solvRad L := hinfL ⟨hEC he, heL⟩
        have hyR : y ∈ solvRad L := by
          rw [hye']
          exact Subgroup.inv_mem _ heR
        have hy1 := zpowers_inf_radical hxo hxR hy hyR
        rw [hy1, one_mul] at hye1
        exact ⟨hy1, hye1⟩)
      (a := 1) (b := CFSG.Open.pRank 3 (centralizerModSolvRad L))
      (by simp [Nat.card_zpowers, hxo]) hEcard
    omega


end A320

end CFSG.Quasithin
