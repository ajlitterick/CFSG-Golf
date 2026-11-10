module

public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Sporadic.Recognition.McLASThreeCentral
public import Certificates.Certificate6105

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

theorem m11Check_eq_true : m11Check = true :=
  Certificates.certificate6105.1


theorem threeFacts_cert : ThreeFacts :=
  Certificates.certificate6105.2.2.1

theorem fiveOuterCheck_eq_true : fiveOuterCheck = true :=
  Certificates.certificate6105.2.2.2.1


theorem mcl_outer_involutions_of_certificate :
    (∃ σ : MulAut NativeSporadic.McL, orderOf σ = 2 ∧ σ ∉ inner NativeSporadic.McL) ∧
    (∀ σ τ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      orderOf τ = 2 → τ ∉ inner NativeSporadic.McL →
        ∃ g : NativeSporadic.McL, mclConj g * σ * (mclConj g)⁻¹ = τ) ∧
    (∀ σ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      Nonempty (↥(mclFixed σ) ≃* ↥NativeSporadic.M11)) :=
  mcl_outer_involutions m11Check_eq_true


theorem mcl_two_classes_order_three_of_certificate :
    ∃ x₁ x₂ : NativeSporadic.McL, orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧
      Nat.card ↥(centralizer ({x₁} : Set NativeSporadic.McL)) = 29160 ∧
      Nat.card ↥(centralizer ({x₂} : Set NativeSporadic.McL)) = 972 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : NativeSporadic.McL, orderOf y = 3 → IsConj y x₁ ∨ IsConj y x₂ :=
  mcl_two_classes_order_three threeFacts_cert

theorem mcl_two_classes_order_five_of_certificate :
    ∃ x₁ x₂ : NativeSporadic.McL, orderOf x₁ = 5 ∧ orderOf x₂ = 5 ∧
      Nat.card ↥(centralizer ({x₁} : Set NativeSporadic.McL)) = 750 ∧
      Nat.card ↥(centralizer ({x₂} : Set NativeSporadic.McL)) = 25 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : NativeSporadic.McL, orderOf y = 5 → IsConj y x₁ ∨ IsConj y x₂ :=
  mcl_two_classes_order_five fiveOuterCheck_eq_true


end CFSG.Sporadic.Recognition.McLAS
