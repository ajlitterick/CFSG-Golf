module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y5
import CFSG.ClassicalInvolution.Asc77.AscT8Y6Eng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

section Zt

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem oddCoreOf_layerJoin_le_of_zt (hs : Std8 p f Ω K J S R T W z t) {K' : Subgroup G}
    (hK' : K' ∈ omegaNbr Ω K) (hz' : IsUniqueInvolution K' (z * t)) :
    oddCoreOf (layerJoin Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have huv : z * t = t * z := mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hne : z ≠ t := ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hgu : Subgroup.centralizer ({z} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz).trans
      (normalizer_le_sigmaNorm hΩ.conjInvariant hK)
  have hgv : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.hJ.1 (hnt _ hs.hJ.1) hs.ht).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK (mem_dComp_of_mem_omegaNbr hs.hJ))
  have hguv : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK'.1 (hnt _ hK'.1) hz').trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK (mem_dComp_of_mem_omegaNbr hK'))
  refine oddCoreOf_layerJoin_le_of_good_pair hΩ hs.hz.sq hs.ht.sq huv hs.hz.ne_one hs.ht.ne_one
    hne ?_ ?_ hgu hgv hguv
  · rw [mem_cenZ_iff]
    calc z * (z * t) = z * (t * z) := by rw [huv]
      _ = (z * t) * z := by group
  · rw [mem_cenZ_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [huv]


end Zt

end T8

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_Oab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          (∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
            z' ≠ z * t) →
            oddCoreOf (T8.layerJoin Ω (z * t)) ≤ sigmaNorm Ω K

variable {p f}


theorem c27_YnE4_of_core' (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (hO : C27_Oab p f)
    (hY : C27_Ysmall p f) : C27_YnE4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hcomp := h2 G Ω K J S R T W z t hs hdisc
  have hlayer : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K := by
    by_cases hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x
    · refine T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp ?_
        (T8.dstarConnected_layerFamQ_of_abelian hD4 hs hE4 hab)
      by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G,
          IsUniqueInvolution K' z' → z' ≠ z * t
      · exact hO G Ω K J S R T W z t hs hdisc hE4 hab hE8
      · push Not at hE8
        obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
        exact T8.oddCoreOf_layerJoin_le_of_zt hs hK' (hzt ▸ hz')
    · by_cases hconn : T3.DStarConnected (T8.layerFamQ Ω (z * t))
      · exact T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp
          (T8.oddCoreOf_layerJoin_le_of_nonabelian hs hcomp hab) hconn
      · exact hY G Ω K J S R T W z t hs hdisc hE4 hab hconn
  exact (T8.rLayer_le_layerJoin hp hq hΩ hnt hx).trans hlayer

theorem c27_8_of_core' (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (hE : C27_8E4 p f)
    (hO : C27_Oab p f) (hY : C27_Ysmall p f) : C27_8 p f :=
  c27_8_of_split hE (c27_8nE4_of_c27_YnE4 (c27_YnE4_of_core' hD4 h2 hO hY))

theorem thm8A_of_core' (hD4 : Ih8D4Star p f) (h2 : C26_2 p f) (h13 : C26_13 p f)
    (hE : C27_8E4 p f) (hO : C27_Oab p f) (hY : C27_Ysmall p f) : Thm8A p f :=
  thm8A_of_c26_2_c26_13 h2 h13 (c27_4a_of_min (c27_2_of_c26_2_c26_13 h2 h13) c27_4M_proved)
    (c27_8_of_core' hD4 (c27_2_of_c26_2_c26_13 h2 h13) hE hO hY)


end Residual

end CFSG.ClassicalInvolution.Asc77
