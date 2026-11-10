module

public import CFSG.Quasithin.EmptyFaithful.S1421Surv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421Elim

variable {G : Type} [Group G]

theorem isSolvable_of_isSolvable_oTwoQuot [Finite G] {H : Subgroup G}
    (h : Group.IsSolvable (OTwoQuot H)) : Group.IsSolvable ↥H := by
  have : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have : Group.IsSolvable (CFSG.Open.pCore 2 ↥H) := by
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2).isNilpotent
    infer_instance
  have : Group.IsSolvable (↥H ⧸ CFSG.Open.pCore 2 ↥H) := h
  exact Group.isSolvable_of_subgroup_quotient (CFSG.Open.pCore 2 ↥H)


theorem isSolvable_of_le_of_isSolvable {K X : Subgroup G} (hKX : K ≤ X)
    (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥K :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKX)

theorem not_isBlock2_of_oTwoQuot_perm3 {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) : ¬ IsBlock2 L L := by
  rintro ⟨hshort, -, -⟩
  obtain ⟨e⟩ := hS3
  let φ : ↥L →* ℤˣ :=
    Equiv.Perm.sign.comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)))
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have hp : IsPGroup 2 (↥L ⧸ φ.ker) := by
    intro g
    refine ⟨1, ?_⟩
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
      exact Int.units_sq _
  have htop : φ.ker = ⊤ := hshort.1 φ.ker hp
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥L) (e.symm (Equiv.swap 0 1))
  have h1 : φ x = 1 := by
    have : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
    exact this
  have h2 : φ x = -1 := by
    simp only [φ, MonoidHom.comp_apply, hx, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.apply_symm_apply]
    exact Equiv.Perm.sign_swap (by decide)
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem eq_one_of_isL2Quot_of_perm3 (hF : ListedGroupFacts) {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) {f : ℕ} (hf : 1 ≤ f)
    (h : IsL2Quot f (OTwoQuot L)) : f = 1 := by
  by_contra hne
  exact hF.l2_ne_perm3 f (by omega) _ h hS3

theorem false_of_isL2Quot_of_perm3 (hF : ListedGroupFacts) {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) {f : ℕ} (hf : 2 ≤ f)
    (h : IsL2Quot f (OTwoQuot L)) : False :=
  hF.l2_ne_perm3 f hf _ h hS3

theorem le_normalizer_of_card_center_eq_two [Finite G] {L Z : Subgroup G}
    (hcard : Nat.card (Subgroup.center ↥(pCoreOf 2 L)) = 2) (hZ2 : Nat.card Z = 2)
    (hZP : Z ≤ pCoreOf 2 L) (hZc : Z ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) :
    L ≤ Subgroup.normalizer (Z : Set G) := by
  set P := pCoreOf 2 L with hP
  have hle : Z ≤ (Subgroup.center ↥P).map P.subtype := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hZP hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc hx g.1 g.2)
  have hcardZ : Nat.card ((Subgroup.center ↥P).map P.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]
  have hZeq : Z = (Subgroup.center ↥P).map P.subtype :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, hZ2])
  rw [hZeq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

end S1421Elim

open S1421Elim

section Elim


end Elim


end CFSG.Quasithin
