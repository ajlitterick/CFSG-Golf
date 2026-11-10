module

public import CFSG.Quasithin.Background.SimsE214Ten

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace E214S

variable {Γ : Type} [Group Γ]

theorem relIndex_sup_eq_mul {X W Z : Subgroup Γ} (hZX : Z ≤ X) (hZW : Z ≤ W)
    (hXW : X ≤ Subgroup.normalizer (W : Set Γ)) (hinf : X ⊓ W ≤ Z) :
    Z.relIndex (X ⊔ W) = Z.relIndex X * Z.relIndex W := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXW
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXW
  have e : W.relIndex (X ⊔ W) = W.relIndex X :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient X W hXW).toEquiv.symm
  have h2 : W ⊓ X = Z := le_antisymm (by rw [inf_comm]; exact hinf) (le_inf hZW hZX)
  have h3 : W.relIndex X = Z.relIndex X := by
    rw [← Subgroup.inf_relIndex_right W X, h2]
  rw [← Subgroup.relIndex_mul_relIndex Z W (X ⊔ W) hZW le_sup_right, e, h3, mul_comm]

theorem relIndex_biSup_eq_pow {r : ℕ} {I Z : Subgroup Γ} (W : Fin r → Subgroup Γ) {c : ℕ}
    (hZ : ∀ i, Z ≤ W i) (hWI : ∀ i, W i ≤ I)
    (hN : ∀ i, I ≤ Subgroup.normalizer (W i : Set Γ)) (hc : ∀ i, Z.relIndex (W i) = c)
    (hind : ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z) {s : Finset (Fin r)} (hs : s.Nonempty) :
    Z.relIndex (⨆ i ∈ s, W i) = c ^ s.card := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => rw [Finset.iSup_singleton, Finset.card_singleton, pow_one, hc a]
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iSup_insert, Finset.card_insert_of_notMem ha, pow_succ,
      sup_comm (W a), ← ih, ← hc a]
    refine relIndex_sup_eq_mul ?_ (hZ a) ?_ ?_
    · obtain ⟨b, hb⟩ := hs
      exact (hZ b).trans (le_iSup₂_of_le b hb le_rfl)
    · exact iSup₂_le fun i _ => (hWI i).trans (hN a)
    · have hle : (⨆ i ∈ s, W i) ≤ ⨆ j, ⨆ (_ : j ≠ a), W j :=
        iSup₂_le fun i hi => le_iSup₂_of_le i (ne_of_mem_of_not_mem hi ha) le_rfl
      calc (⨆ i ∈ s, W i) ⊓ W a ≤ (⨆ j, ⨆ (_ : j ≠ a), W j) ⊓ W a := inf_le_inf_right _ hle
        _ = W a ⊓ ⨆ j, ⨆ (_ : j ≠ a), W j := inf_comm _ _
        _ ≤ Z := hind a

theorem relIndex_iSup_eq_pow {r : ℕ} (hr : 0 < r) {I Z : Subgroup Γ} (W : Fin r → Subgroup Γ)
    {c : ℕ} (hZ : ∀ i, Z ≤ W i) (hWI : ∀ i, W i ≤ I)
    (hN : ∀ i, I ≤ Subgroup.normalizer (W i : Set Γ)) (hc : ∀ i, Z.relIndex (W i) = c)
    (hind : ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z) :
    Z.relIndex (⨆ i, W i) = c ^ r := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have h := relIndex_biSup_eq_pow W hZ hWI hN hc hind (Finset.univ_nonempty (α := Fin r))
  simpa using h


variable [Finite Γ]


structure Sec (I P Z J : Subgroup Γ) : Prop where
  ZP : Z ≤ P
  PI : P ≤ I
  IP : I ≤ Subgroup.normalizer (P : Set Γ)
  IZ : I ≤ Subgroup.normalizer (Z : Set Γ)
  JI : J ≤ I
  IJ : I ≤ Subgroup.normalizer (J : Set Γ)
  J2 : IsPGroup 2 J
  comm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z
  sq : ∀ x ∈ P, x ^ 2 ∈ Z
  irr : ∀ Y : Subgroup Γ, Z ≤ Y → Y ≤ P → I ≤ Subgroup.normalizer (Y : Set Γ) → Y = Z ∨ Y = P
  ne : Z ≠ P

namespace Sec

variable {I P Z J : Subgroup Γ}


variable [(Z.subgroupOf P).Normal]

noncomputable abbrev act (hS : Sec I P Z J) : ↥I →* MulAut (↥P ⧸ Z.subgroupOf P) :=
  Dih.conjSecAut P Z I hS.IP hS.IZ


end Sec

end E214S

end CFSG.Quasithin.SimsE2
