module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


section Lift

variable {G : Type*} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R)

theorem ggLAut_mk_self (k : K) :
    ggLAut K θ ⟨k, Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (θ (k : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    have h : (K.normalizerMonoidHom ⟨(k : G), Subgroup.le_normalizer k.2⟩ l : K) =
        k * l * k⁻¹ := Subtype.ext (by rw [normalizerMonoidHom_coe]; simp)
    rw [ggLAut_apply, h, MulAut.conj_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]

variable {K θ}

theorem orderOf_dvd_card_center [Finite G] {c : G} (hcK : c ∈ K)
    (hcC : c ∈ Subgroup.centralizer (K : Set G)) :
    orderOf c ∣ Nat.card (Subgroup.center K) := by
  have hcZ : (⟨c, hcK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC z z.2)
  have h := orderOf_dvd_natCard (⟨⟨c, hcK⟩, hcZ⟩ : Subgroup.center K)
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at h
  exact h

theorem commute_of_ggLAut_commute [Finite G] (hK : commutator K = ⊤) {p : ℕ}
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {k g : G} (hk : k ∈ K) (hkp : k ^ p = 1)
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hc : ggLAut K θ ⟨g, hg⟩ * ggLAut K θ ⟨k, Subgroup.le_normalizer hk⟩ =
      ggLAut K θ ⟨k, Subgroup.le_normalizer hk⟩ * ggLAut K θ ⟨g, hg⟩) :
    g * k = k * g := by
  set c : G := g * k * g⁻¹ * k⁻¹ with hcdef
  have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (mul_mem (mul_mem hg (Subgroup.le_normalizer hk)) (inv_mem hg))
      (inv_mem (Subgroup.le_normalizer hk))
  have hc1 : ggLAut K θ ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨g, hg⟩ * ⟨k, Subgroup.le_normalizer hk⟩ * (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
          (⟨k, Subgroup.le_normalizer hk⟩ : Subgroup.normalizer (K : Set G))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hcC : c ∈ Subgroup.centralizer (K : Set G) := mem_centralizer_of_ggLAut_eq_one K θ hK hc1
  have hcK : c ∈ K := by
    have h1 : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
    exact mul_mem h1 (inv_mem hk)
  have hck : Commute c k := (Subgroup.mem_centralizer_iff.mp hcC k hk).symm
  have hcp : c ^ p = 1 := by
    have h1 : (g * k * g⁻¹) ^ p = 1 := by rw [conj_pow, hkp]; group
    have h2 : g * k * g⁻¹ = c * k := by rw [hcdef]; group
    rw [h2, hck.mul_pow, hkp, mul_one] at h1
    exact h1
  have hord : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes hZ (orderOf_dvd_of_pow_eq_one hcp)
      (orderOf_dvd_card_center hcK hcC)
  have hc1' : c = 1 := orderOf_eq_one_iff.mp hord
  calc g * k = c * (k * g) := by rw [hcdef]; group
    _ = k * g := by rw [hc1', one_mul]

end Lift

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem pow_eq_self_of_mod_eq_one {M : Type*} [Monoid M] {a : M} {p m : ℕ} (ha : a ^ p = 1)
    (hm : m % p = 1) : a ^ m = a := by
  rw [← Nat.div_add_mod m p, hm, pow_add, pow_mul, ha, one_pow, one_mul, pow_one]


end Config


end CFSG.StandardType

end
