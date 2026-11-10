module

public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum
import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Goldschmidt.Steps.ZStarLemma
import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace LemmaX

variable {G : Type} [Group G] [Finite G]

theorem four_le_card [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {U : Subgroup G} (hUS : U ≤ S) (hU1 : U ≠ ⊥) (hsq : ∀ x ∈ U, x ^ 2 = 1)
    (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) : 4 ≤ Nat.card U := by
  have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUS
  by_contra h4
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.card_eq_one.1 (by simpa using hn))
  have hn1 : n = 1 := by
    by_contra hn1
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hU2 : Nat.card U = 2 := by rw [hn, hn1, pow_one]
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have heq : ∀ y : U, y ≠ 1 → y = u := fun y hy =>
    ((Nat.card_eq_two_iff' (1 : U)).1 hU2).unique hy hu1
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : (u : G) * u = 1 := by rw [← sq]; exact hsq u u.2
  have hwc : ∀ g : G, g⁻¹ * (u : G) * g ∈ (S : Subgroup G) → g⁻¹ * (u : G) * g = u := by
    intro g hg
    have hmem : g⁻¹ * (u : G) * g ∈ U := hUcl u u.2 g hg
    have hne : (⟨_, hmem⟩ : U) ≠ 1 := by
      intro h
      apply hu1'
      have h' : g⁻¹ * (u : G) * g = 1 := congrArg Subtype.val h
      calc (u : G) = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    exact congrArg Subtype.val (heq _ hne)
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G u hu1' hu2
    (conj_eq_of_commute_of_weakClosure S hu2 hwc)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN0 | hNtop
  · have hz : (u : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hN g
      rw [hN0, Subgroup.mem_bot] at h
      calc g * (u : G) = (g * u * g⁻¹ * (u : G)⁻¹) * u * g := by group
        _ = u * g := by rw [h, one_mul]
    rw [PropHSetup.center_eq_bot hnab, Subgroup.mem_bot] at hz
    exact hu1' hz
  · rw [hNtop, Subgroup.card_top] at hNodd
    have huo : orderOf (u : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1'
    have h2 : 2 ∣ Nat.card G := huo ▸ orderOf_dvd_natCard (u : G)
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)

theorem normalizer_le_of_le (S : Sylow 2 G) {A U H E : Subgroup G} (hAS : A ≤ S)
    (hAab : IsMulCommutative A) (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hUS : U ≤ S) (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) (hUA : U ≤ A)
    (hNH : Subgroup.normalizer (U : Set G) ≤ H)
    (hCH : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) (hEU : E ≤ U)
    (hE1 : E ≠ ⊥) : Subgroup.normalizer (E : Set G) ≤ H := by
  intro g hg
  have hNA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    N3a G S U A hUS hUcl ((S.isPGroup').to_le hAS) hUA
  have hmap : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    intro y hy
    rw [mem_map_conj_inv_iff] at hy
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (g * y * g⁻¹)).1 hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h1
    exact hUS (hEU h1)
  obtain ⟨n, hnN, hn⟩ := N4b G S A E g hAS hAab hAcl (hEU.trans hUS) hmap
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have hgn : g * n⁻¹ ∈ Subgroup.centralizer ({(e : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hn e e.2
    calc g * n⁻¹ * e = g * (n⁻¹ * e * n) * n⁻¹ := by group
      _ = g * (g⁻¹ * e * g) * n⁻¹ := by rw [h1]
      _ = e * (g * n⁻¹) := by group
  have h2 := hCH e (hEU e.2) (fun h => he1 (Subtype.ext h)) hgn
  have e' : g = g * n⁻¹ * n := by group
  rw [e']
  exact H.mul_mem h2 (hNH (hNA hnN))


end LemmaX


end CFSG.Goldschmidt
