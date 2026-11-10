module

public import CFSG.Quasithin.Background.RonanE43Basic
public import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G] [Finite G] {Γ : Type} [Group Γ]

theorem card_pCoreOf_le_comap (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    (Y : Subgroup Γ) : Nat.card (pCoreOf 2 Y) ≤ Nat.card (pCoreOf 2 (Y.comap π)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Γ := Finite.of_surjective π hπ
  let e : G ⧸ π.ker ≃* Γ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  set M : Subgroup (G ⧸ π.ker) := Y.comap (e : G ⧸ π.ker →* Γ) with hM
  have hcomp : (e : G ⧸ π.ker →* Γ).comp (QuotientGroup.mk' π.ker) = π := by
    ext g
    rfl
  have hcomap : M.comap (QuotientGroup.mk' π.ker) = Y.comap π := by
    rw [hM, Subgroup.comap_comap, hcomp]
  have hMmap : M = Y.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e Y
  have h1 := CFSG.LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap (r := 2) π.ker hker hodd M
  rw [hcomap] at h1
  have h2 : Nat.card (pCoreOf 2 M) = Nat.card (pCoreOf 2 Y) := by
    rw [hMmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e.symm Y]
    exact Subgroup.card_map_of_injective e.symm.injective
  rw [← h2]
  exact (Subgroup.card_le_of_le h1).trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _))

theorem card_map_eq_of_odd_ker (π : G →* Γ) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    {T : Subgroup G} (hT : IsPGroup 2 T) : Nat.card (T.map π) = Nat.card T := by
  have hinj : Function.Injective (π.comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro t ht
    have ht1 : π (t : G) = 1 := ht
    have htk : (t : G) ∈ π.ker := ht1
    obtain ⟨n, hn⟩ := hT t
    have h1 : orderOf (t : G) ∣ Nat.card π.ker := by
      have := Subgroup.orderOf_dvd_natCard π.ker htk
      exact this
    have h2 : orderOf (t : G) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hn
      simpa using this
    have h3 : orderOf (t : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h1 hodd)) h2
    have : (t : G) = 1 := orderOf_eq_one_iff.mp h3
    exact Subtype.ext this
  have hrange : (π.comp T.subtype).range = T.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isSylowIn_map (π : G →* Γ) (hπ : Function.Surjective π)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : ¬ 2 ∣ (T.map π).index := by
  have h1 : (T.map π).index ∣ T.index := Subgroup.index_map_dvd T hπ
  have h2 : ¬ 2 ∣ T.index := by
    have := hT.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  exact fun h => h2 (h.trans h1)

variable [Finite Γ]


theorem coprime_card_center_of_pCore_bot (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥)
    {K : Subgroup G} (hK : K ≤ Subgroup.center G) : Nat.Coprime (Nat.card K) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxc : (x : G) ∈ Subgroup.center G := hK x.2
  have hord : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hp : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; simp
  haveI hNn : (Subgroup.zpowers (x : G)).Normal := ⟨fun n hn g => by
    have hnc : n ∈ Subgroup.center G := Subgroup.zpowers_le.mpr hxc hn
    have h1 : g * n * g⁻¹ = n := by
      have := Subgroup.mem_center_iff.mp hnc g
      rw [this]; group
    rw [h1]; exact hn⟩
  have hle : Subgroup.zpowers (x : G) ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (by rw [(Subgroup.normalizer_eq_top_iff).mpr hNn]) hp
  rw [hO2] at hle
  have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [hx1, orderOf_one] at hord
  omega


end CFSG.Quasithin.RonanE43
