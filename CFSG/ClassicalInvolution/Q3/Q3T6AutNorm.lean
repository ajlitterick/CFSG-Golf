module

public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.AschTight.E3StarD
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3T6AutTwo
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Action

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def normalizerToAutSL3 (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :
    Subgroup.normalizer (K : Set G) →* MulAut SL(2, ZMod 3) :=
  (MulAut.congr e).toMonoidHom.comp ((oddCoreQuotientAut K).comp (normalizerConj K))

variable (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))

theorem normalizerToAutSL3_apply (n : Subgroup.normalizer (K : Set G)) (y : K) :
    normalizerToAutSL3 e n (e (QuotientGroup.mk y)) =
      e (QuotientGroup.mk (normalizerConj K n y)) := by
  simp [normalizerToAutSL3, MulAut.congr_apply, oddCoreQuotientAut_mk]

theorem normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut (n : Subgroup.normalizer (K : Set G)) :
    normalizerToAutSL3 e n = 1 ↔ oddCoreQuotientAut K (normalizerConj K n) = 1 := by
  change MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n)) = 1 ↔ _
  rw [← map_one (MulAut.congr e)]
  exact (MulAut.congr e).injective.eq_iff

theorem normalizerToAutSL3_eq_one_iff (n : Subgroup.normalizer (K : Set G)) :
    normalizerToAutSL3 e n = 1 ↔ ∀ l ∈ K, ⁅(n : G), l⁆ ∈ Asc77.oddCoreOf K := by
  rw [normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut,
    Hall196.oddCoreQuotientAut_normalizerConj_eq_one_iff]

theorem normalizerToAutSL3_of_mem {k : G} (hk : k ∈ K) :
    normalizerToAutSL3 e ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (e (QuotientGroup.mk ⟨k, hk⟩)) :=
  Hall196.congr_oddCoreQuotientAut_of_mem e hk

theorem mem_cStar_iff_normalizerToAutSL3_eq_one (n : Subgroup.normalizer (K : Set G)) :
    (n : G) ∈ cStar K ↔ normalizerToAutSL3 e n = 1 := by
  rw [normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut]
  constructor
  · rintro ⟨n', hn', hn'n⟩
    have : n' = n := Subtype.ext hn'n
    rw [← this]
    exact hn'
  · intro h
    exact ⟨n, h, rfl⟩


end Action

section E3

variable {G : Type} [Group G] {K : Subgroup G}

theorem normalizerQuotientTwoGeneratedStar_three
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :
    NormalizerQuotientTwoGeneratedStar K := by
  intro P hP hPN
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.normalizer (K : Set G))) := hP.comap_subtype
  obtain ⟨a, b, hab⟩ :=
    sl2Three_mulAut_isPGroup_exists_closure_pair (hP'.map (normalizerToAutSL3 e))
  exact closure_pair_sup_eq_of_map (C := cStar K)
    (fun n hn => (mem_cStar_iff_normalizerToAutSL3_eq_one e n).mpr hn) hPN hab


theorem centSylow_three [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ K ∈ Ω, Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))) :
    Asc77.AscL62.CentSylow Ω := by
  intro K R V hK hR _ hVK hcomm k hk v hv
  obtain ⟨e⟩ := hΩ K hK
  have hvN : v ∈ Subgroup.normalizer (K : Set G) :=
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (hVK v hv)
  set φ : ↥K →* SL(2, ZMod 3) :=
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K →* SL(2, ZMod 3)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, ZMod 3) :=
    Sylow.mapSurjective (f := φ) hφs (Asc77.AscL62.sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, normalizerToAutSL3 e ⟨v, hvN⟩ x = x := by
    intro x hx
    have hx' : x ∈ ((Asc77.AscL62.sylowOfIsSylow2In'' hR : Subgroup ↥K)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (Asc77.AscL62.sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hαr : normalizerConj K ⟨v, hvN⟩ r = r := by
      apply Subtype.ext
      rw [normalizerConj_apply_coe, ← hcomm r hrR v hv]
      group
    show normalizerToAutSL3 e ⟨v, hvN⟩ (e (QuotientGroup.mk r)) = e (QuotientGroup.mk r)
    rw [normalizerToAutSL3_apply, hαr]
  exact (normalizerToAutSL3_eq_one_iff e ⟨v, hvN⟩).mp
    (sl2Three_mulAut_eq_one_of_fixes_sylow P _ hfix) k hk

end E3

section Hall


end Hall

section Extras


end Extras

end CFSG.ClassicalInvolution.Q3.Q3T6
