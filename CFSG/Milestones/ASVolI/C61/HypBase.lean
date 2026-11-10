module

public import CFSG.Milestones.ASVolI.C6
public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.Quasithin.EmptyFaithful.S152Y22

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC


section General

variable {G : Type} [Group G]


theorem burnsideC56_index_pCore_eq_card {M : Subgroup G} {Y : Type} [Group Y] (φ : ↥M →* Y)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥M) :
    (CFSG.pCore 2 ↥M).index = Nat.card Y := by
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]


end General

section Finite

variable {G : Type} [Group G] [Finite G]


theorem burnsideC56_umax_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (hZ : ∀ S : Subgroup Z, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S := by
  intro S hS hSi
  have hS' : IsPGroup 2 (S.map e.toMonoidHom) := hS.map _
  have hSi' : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_eq _ e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact bot_le)]
    exact hSi
  refine burnsideC5h_p1_umax_of_surjective e.toMonoidHom e.surjective ?_ (hZ _ hS' hSi')
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact bot_le

theorem burnsideC56_uniqueMax_of_quot {H T K : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hsup : K ⊔ T = H) {Y : Type} [Group Y]
    (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K)
    (hY : ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S) :
    ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have hU : burnsideC5h_p1_UMaxIn K (T ⊓ K) :=
    burnsideC5h_p1_umaxIn_of_quotient hTK φ hφ hker hY
  have hU' : burnsideC5h_p1_UMaxIn K (K ⊓ T) := by rwa [inf_comm]
  obtain ⟨N, hN⟩ := burnsideC5h_p1_uniqueMax_sup (A := K) (B := T) (hT.1.trans hHK) hU'
  rw [hsup] at hN
  exact ⟨N, hN⟩

theorem burnsideC56_not_normal_of_quot {H T K : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {Y : Type} [Group Y] (φ : ↥K →* Y)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K) (hY2 : 2 ∣ Nat.card Y) :
    ¬ H ≤ Subgroup.normalizer (T : Set G) := by
  intro hHT
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have hnorm : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro k hk
    exact A4.mem_normalizer_inf (hHT (hKH hk)) (hHK (hKH hk))
  have hle : T ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hTK.2.1
  have hle' : (T ⊓ K).subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := hle hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hdvd : (CFSG.pCore 2 ↥K).index ∣ ((T ⊓ K).subgroupOf K).index :=
    Subgroup.index_dvd_of_le hle'
  rw [burnsideC56_index_pCore_eq_card φ hφ hker] at hdvd
  exact hTK.2.2 (hY2.trans hdvd)


end Finite

end CFSG.ASVolI
