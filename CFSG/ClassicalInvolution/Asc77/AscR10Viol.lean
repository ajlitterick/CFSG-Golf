module

public import CFSG.ClassicalInvolution.Asc77.AscR10Aux
public import CFSG.ClassicalInvolution.Asc77.AscR10Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r_aViol [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({b} : Set G),
      ∃ htA : t ∈ Subgroup.centralizer ({b} : Set G),
        IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzA⟩ ∧
        Nat.card ↥(Subgroup.centralizer ({b} : Set G)) < Nat.card G ∧
        CITBelowU p e₀ (Nat.card G) ∧
        ∃ J_b : Subgroup ↥(Subgroup.centralizer ({b} : Set G)),
          AViol (conjFamily (perfectCoreIn K b)) (perfectCoreIn K b) J_b ⟨z, hzA⟩ ⟨t, htA⟩ := by
  obtain ⟨e₀, hfe, h5, hzA, hmem, hlt, hIH⟩ := d.x_sectionData c9 h8 h9 hb
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  have htA : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hb.comm_t.symm
  obtain ⟨c, hcb, hcK, hcz⟩ := d.r_exists_c c7 c9 h8 hb
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcb
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, hbv⟩ := d.r_v0 c9 h8 hb hu huo hact
  set K_b := perfectCoreIn K b with hKb
  set cY : ↥C := ⟨c, hcC⟩ with hcY
  set J_b := conjSub cY K_b with hJb
  refine ⟨e₀, hfe, h5, hzA, htA, hmem, hlt, hIH, J_b, ?_⟩
  have hzKa : z ∈ perfectResidualOf (K ⊓ C) := Subgroup.mem_subgroupOf.mp hmem.mem
  have hu₁ : IsUniqueInvolution K_b ⟨z, hzA⟩ := by
    have := d.x_isUniqueInvolution_conjSub hzA hzKa 1
    simpa [conjSub_one] using this
  have hu₂ : IsUniqueInvolution J_b ⟨t, htA⟩ := by
    have := d.x_isUniqueInvolution_conjSub hzA hzKa cY
    have e : cY * ⟨z, hzA⟩ * cY⁻¹ = ⟨t, htA⟩ := Subtype.ext hcz
    rwa [e] at this
  have hΩ₀ := d.x_hypOmegaMod_conjFamily hzA hmem
  have hJbΛ : J_b ∈ conjFamily K_b := ⟨cY, rfl⟩
  have hKbΛ : K_b ∈ conjFamily K_b := ⟨1, conjSub_one _⟩
  have hvJW : v₀ ∈ J ⊓ W := hv₀ ▸ Subgroup.mem_zpowers v₀
  have hv2C : v₀ ^ 2 ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hbv.symm
  set y₀ : ↥C := ⟨v₀ ^ 2, hv2C⟩ with hy₀
  have hv2J : v₀ ^ 2 ∈ J := J.pow_mem hvJW.1 2
  have h2v : 2 ∣ orderOf v₀ := by
    rw [hv₀o]
    exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have hy₀o : orderOf y₀ = 2 ^ k := by
    rw [hy₀, Subgroup.orderOf_mk, orderOf_pow_of_dvd (by norm_num) h2v, hv₀o, pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]
  have hy₀J : y₀ ∈ J_b := by
    have hmap : (y₀ : G) ∈ J_b.map C.subtype := by
      rw [hJb, map_conjSub_perfectCore]
      rw [mem_conjSub_iff]
      refine d.r_mem_perfectCore c9 h8 h9 hb ?_ ?_ ⟨k, ?_⟩
      · have : v₀ ^ 2 ∈ conjSub c K := hcK ▸ hv2J
        exact mem_conjSub_iff.mp this
      · have h1 : (c⁻¹ * v₀ ^ 2 * c) * b = b * (c⁻¹ * v₀ ^ 2 * c) := by
          calc c⁻¹ * v₀ ^ 2 * c * b = c⁻¹ * v₀ ^ 2 * (c * b) := by group
            _ = c⁻¹ * v₀ ^ 2 * (b * c) := by rw [hcb]
            _ = c⁻¹ * (v₀ ^ 2 * b) * c := by group
            _ = c⁻¹ * (b * v₀ ^ 2) * c := by rw [hbv]
            _ = (c⁻¹ * b) * v₀ ^ 2 * c := by group
            _ = (b * c⁻¹) * v₀ ^ 2 * c := by
              have : c⁻¹ * b = b * c⁻¹ := by
                calc c⁻¹ * b = c⁻¹ * b * c * c⁻¹ := by group
                  _ = c⁻¹ * (b * c) * c⁻¹ := by group
                  _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcb]
                  _ = b * c⁻¹ := by group
              rw [this]
            _ = b * (c⁻¹ * v₀ ^ 2 * c) := by group
        exact h1.symm
      · have h1 := conj_pow (a := c⁻¹) (b := v₀ ^ 2) (i := 2 ^ k)
        rw [inv_inv] at h1
        rw [h1, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring, ← hv₀o, pow_orderOf_eq_one]
        group
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).mp hmap
  set U : Subgroup ↥C := Subgroup.zpowers y₀ with hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := k) (by rw [hU, Nat.card_zpowers, hy₀o])
  have hUJ : U ≤ J_b := Subgroup.zpowers_le.mpr hy₀J
  have hUcard : Nat.card ↥U = 2 ^ k := by rw [hU, Nat.card_zpowers, hy₀o]
  have hU2' : IsPGroup 2 (U.subgroupOf J_b) := hU2.comap_subtype
  obtain ⟨Q, hQ⟩ := hU2'.exists_le_sylow
  set R₁ : Subgroup ↥C := (Q : Subgroup ↥J_b).map J_b.subtype with hR₁
  have hR₁Λ : R₁ ∈ RSet (conjFamily K_b) := ⟨J_b, hJbΛ, Q, rfl⟩
  have hUR₁ : U ≤ R₁ := by
    have h1 : (U.subgroupOf J_b).map J_b.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUJ
    rw [← h1]
    exact Subgroup.map_mono hQ
  have hQcard : Nat.card ↥(Q : Subgroup ↥J_b) = 2 ^ (k + 1) :=
    d.r_natCard_sylow hu huo hfe h5 (hmem.conj cY) Q
  have hR₁card : Nat.card ↥R₁ = 2 ^ (k + 1) := by
    rw [hR₁, ← hQcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ J_b.subtype_injective).toEquiv).symm
  have hrel : U.relIndex R₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R₁
    rw [inf_eq_left.mpr hUR₁, hR₁card, hUcard] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : U.relIndex R₁ * 2 ^ k = 2 * 2 ^ k := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hUstar : U ∈ USet (conjFamily K_b) :=
    ⟨R₁, hR₁Λ, hUR₁, inferInstance, hrel⟩
  have hy₀N : y₀ ∈ Subgroup.normalizer (K_b : Set ↥C) := by
    have hv2N : v₀ ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
      d.late_JW_le_N_K d.late_JW ((J ⊓ W).pow_mem hvJW 2)
    have := mem_normalizer_conjSub_of (K := K) (a := b) (1 : ↥C) y₀ (by
      rw [show (((1 : ↥C)) : G) = 1 from rfl, conjSub_one]
      exact hv2N)
    rwa [conjSub_one] at this
  have hUN : U ≤ Subgroup.normalizer (K_b : Set ↥C) :=
    (Subgroup.zpowers_le).mpr hy₀N
  have hJbne : J_b ≠ K_b := by
    intro h
    have h1 := hu₂
    rw [h] at h1
    have h2 := h1.eq hu₁
    exact d.late_ne_inv (congrArg Subtype.val h2)
  have hstar : J_b ∈ omegaStarNbr (conjFamily K_b) K_b := ⟨hJbΛ, hJbne, U, hUstar, hUJ, hUN⟩
  have hKbmap : K_b.map C.subtype = perfectResidualOf (K ⊓ C) := by
    have h1 := map_conjSub_perfectCore (K := K) (a := b) (1 : ↥C)
    rw [conjSub_one, Subgroup.coe_one, conjSub_one] at h1
    exact h1
  have hnotnbr : J_b ∉ omegaNbr (conjFamily K_b) K_b := by
    rintro ⟨-, hne, R₀, hR, hRle, hRN⟩
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8'⟩ := exists_ne_comm_of_mem_rSet d.branch.odd h5 hmem hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (1 : G) (perfectResidualOf (K ⊓ C)) ≠
        conjSub c (perfectResidualOf (K ⊓ C)) := by
      intro h
      apply hne
      apply Subgroup.map_injective C.subtype_injective
      rw [hJb, map_conjSub_perfectCore cY, hKbmap]
      simpa [conjSub_one] using h.symm
    have htw : conjSub c K ∉ twinSet (CoreAssembly.conjClass K) (conjSub (1 : G) K) := by
      rw [conjSub_one, hcK]
      exact d.late_J_not_twin
    refine d.x_false_of_le_normalizer hzKa (c₁ := (1 : G)) (c₂ := c) (Subgroup.one_mem _)
      hcC hne' htw (hR2.map C.subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _ C.subtype_injective).toEquiv]
      omega
    · rw [← map_conjSub_perfectCore cY]
      exact Subgroup.map_mono hRle
    · rw [conjSub_one, ← hKbmap]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)
  have hnoconj : ∀ g ∈ pairNormalizers K_b J_b ⟨z, hzA⟩ ⟨t, htA⟩, conjSub g K_b ≠ J_b := by
    intro g hg hgJ
    have hg1 : (g : G) ∈ pairNormalizers (K_b.map C.subtype) (J_b.map C.subtype) z t :=
      T3Typed.map_pairNormalizers_le C.subtype K_b J_b ⟨z, hzA⟩ ⟨t, htA⟩ ⟨g, hg, rfl⟩
    have hJbmap : J_b.map C.subtype = conjSub c (perfectResidualOf (K ⊓ C)) := by
      rw [hJb]
      exact map_conjSub_perfectCore cY
    have hKbK : K_b.map C.subtype ≤ K := by
      rw [hKbmap]
      exact (perfectResidualOf_le _).trans inf_le_left
    have hJbJ : J_b.map C.subtype ≤ J := by
      rw [hJbmap, ← hcK]
      exact Subgroup.map_mono ((perfectResidualOf_le _).trans inf_le_left)
    have hg2 : (g : G) ∈ pairNormalizers K J z t := r_pairNormalizers_mono hKbK hJbJ z t hg1
    have hgmap : conjSub (g : G) (perfectResidualOf (K ⊓ C)) =
        conjSub c (perfectResidualOf (K ⊓ C)) := by
      rw [← hJbmap, ← hgJ, ← hKbmap]
      exact (AscQuot.map_conjSub C.subtype g K_b).symm
    have hUG : Subgroup.zpowers (v₀ ^ 2) ≤ conjSub (g : G) K ⊓ J := by
      refine le_inf ?_ ?_
      · rw [Subgroup.zpowers_le]
        have h1 : v₀ ^ 2 ∈ conjSub c (perfectResidualOf (K ⊓ C)) := by
          rw [← hJbmap]
          exact ⟨y₀, hy₀J, rfl⟩
        rw [← hgmap] at h1
        exact Subgroup.map_mono ((perfectResidualOf_le _).trans inf_le_left) h1
      · exact Subgroup.zpowers_le.mpr hv2J
    have hK1 : conjSub (g : G) K = J := by
      by_contra hne1
      have hK1Ω : conjSub (g : G) K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
      have h4 := (d.hyp.omega4 _ hK1Ω J d.late_mem_J hne1).1
      have hdvd : 2 ^ k ∣ Nat.card ↥(conjSub (g : G) K ⊓ J) := by
        have := Subgroup.card_dvd_of_le hUG
        rwa [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) h2v, hv₀o, pow_succ,
          Nat.mul_div_cancel _ (by norm_num)] at this
      have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
      omega
    exact d.viol.no_conj (g : G) hg2 hK1
  exact ⟨hstar, hnotnbr, hu₁, hu₂, hnoconj⟩


end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
