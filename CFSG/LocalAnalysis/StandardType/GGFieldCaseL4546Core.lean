module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Homocyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem mul_pow_mul_inv_pow_mem {H : Subgroup G} {w x : G} (hw : w ∈ H)
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : ∀ j : ℕ, (w * x) ^ j * (x ^ j)⁻¹ ∈ H := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : x ^ j * w * (x ^ j)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hx j) w).mp hw
    have e : (w * x) ^ (j + 1) * (x ^ (j + 1))⁻¹ =
        ((w * x) ^ j * (x ^ j)⁻¹) * (x ^ j * w * (x ^ j)⁻¹) := by
      rw [pow_succ, pow_succ, mul_inv_rev]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [e]
    exact H.mul_mem ih hc

end General

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.exists_moving_ct (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ c ∈ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∃ t ∈ L ⊓ Subgroup.normalizer (Bs : Set G),
        c * t ∈ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        c * t ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  obtain ⟨t, ht, htd⟩ := ggL45_exists_not_normalizer_zpowers hcfg.1 hcfg.2.1 hcfg.2.2.1
    hcfg.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hXN := hcfg.1.2.2.1
  have hXn := hcfg.1.2.2.2.2.1
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff.mpr hconj ht.2
  have htB₁ : t ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨ht.2, ggNormalizer_le_normalizer_centralizer X htX⟩
  have htC := ggNormalizer_le_normalizer_centralizer _ htB₁
  have hsetup := hcfg.2.2.2.2.2.2.1
  obtain ⟨c, hc, hcU⟩ :=
    exists_mul_mem_normalizer_of_maxPSubgroup htC hsetup.2.1 hsetup.1 hsetup.2.2.1
  have hcd : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_normalizer_zpowers_of_le hcfg.d_mem le_rfl hc
  refine ⟨c, hc, t, ht, ⟨hcU, mul_mem (Subgroup.centralizer_le_normalizer _ hc) htB₁⟩,
    fun h => htd ?_⟩
  have := mul_mem (inv_mem hcd) h
  rwa [inv_mul_cancel_left] at this


end Core


end CFSG.StandardType

end
