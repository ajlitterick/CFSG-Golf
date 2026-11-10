module

public import CFSG.Quasithin.Background.A3Structure313Core
public import CFSG.Quasithin.Background.A3Structure312

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

abbrev oddCoreSub {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore ↥H).map H.subtype

@[expose] def A313Statement {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ∃ p r : ℕ, p.Prime ∧ 3 < p ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L) ∧
    (∃ (N : Subgroup ↥(B ⊔ oddCoreSub L)) (_ : N.Normal),
      N = (oddCoreSub L).subgroupOf (B ⊔ oddCoreSub L) ∧
        IsSL2 r (↥(B ⊔ oddCoreSub L) ⧸ N)) ∧
    (r = p ∨ (r = 5 ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5))) ∧
    ((CFSG.IsQuasisimple ↥B ∧ IsSL2 r ↥B) ∨
      (¬ CFSG.IsQuasisimple ↥B ∧
        ((L = B ⊔ oddCoreSub L ∧ oddCoreSub B < oddCoreSub L ∧ r = 5 ∧ p = 5) ∨
         (B ⊔ oddCoreSub L < L ∧
          IsExt ↥L (fun V _ => IsElemAbelianOfRank p 2 V) (fun Y _ => IsSL2 p Y) ∧
          5 < p ∧ r = 5 ∧ oddCoreSub B = oddCoreSub L))))

namespace A313

variable {G : Type} [Group G]

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm,
    (CFSG.oddCore_eq_piCore Y).trans (CFSG.pPrimeCore_eq_piCore Y 2).symm]
  exact CFSG.pPrimeCore_map_iso 2 e


theorem imgOdd_eq_top_iff {B L : Subgroup G} (hBL : B ≤ L) :
    imgOdd (B.subgroupOf L) = ⊤ ↔ L = B ⊔ oddCoreSub L := by
  have hOLL : oddCoreSub L ≤ L := Subgroup.map_subtype_le _
  constructor
  · intro h
    refine le_antisymm (fun l hl => ?_) (sup_le hBL hOLL)
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥L) (⟨l, hl⟩ : ↥L) ∈ imgOdd (B.subgroupOf L) := by
      rw [h]
      trivial
    obtain ⟨b, hb, hbl⟩ := h1
    have h2 : b⁻¹ * ⟨l, hl⟩ ∈ CFSG.oddCore ↥L :=
      (QuotientGroup.eq (s := CFSG.oddCore ↥L)).mp hbl
    have h3 : (b : G)⁻¹ * l ∈ oddCoreSub L := ⟨b⁻¹ * ⟨l, hl⟩, h2, rfl⟩
    have : l = (b : G) * ((b : G)⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hb h3
  · intro hLB
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥L) z
    have hl' : l ∈ (↑(B ⊔ oddCoreSub L) : Set G) := by
      rw [← hLB]
      exact hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B (oddCoreSub L)
      (hBL.trans (A312.le_normalizer_oddCoreSub L))] at hl'
    obtain ⟨b, hb, o, ho, hbo⟩ := hl'
    refine ⟨⟨b, hBL hb⟩, hb, ?_⟩
    show QuotientGroup.mk (⟨b, hBL hb⟩ : ↥L) = QuotientGroup.mk ⟨l, hl⟩
    rw [QuotientGroup.eq]
    obtain ⟨y, hy, hyo⟩ := ho
    have : (⟨b, hBL hb⟩ : ↥L)⁻¹ * ⟨l, hl⟩ = y := by
      apply Subtype.ext
      show b⁻¹ * l = (y : G)
      have hyo' : (y : G) = o := hyo
      have hbo' : b * o = l := hbo
      rw [hyo', ← hbo']
      group
    rw [this]
    exact hy


theorem mod_five_of_sq {p : ℕ} (h : p ^ 2 % 5 = 1) : p % 5 = 1 ∨ p % 5 = 4 := by
  have h1 := Nat.pow_mod p 2 5
  have h2 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : p % 5 <;> simp_all


theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

end A313


end CFSG.Quasithin
