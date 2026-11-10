module

public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Bridge

section LeAutSec

variable {V : Type} [CommGroup V] {X : Subgroup (MulAut V)} {C : Subgroup V}


end LeAutSec

section Equiv

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {C : Subgroup V}
  (hK : K ≤ stabSub C) (hf : K ⊓ centSec ⊤ C = ⊥)

include hK hf

theorem equiv_of_faithful_of_autSec {D : FFModel} (hD : D.Faithful)
    (h : D.Realizes (autSec K ⊤ C) ⊤ ⊥) : Nonempty (D.Gam ≃* ↥K) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(MulEquiv.ofBijective π ⟨hπ.injective_of_faithful hD, hπ.1⟩).trans
    (B5.secEquiv K (le_stabSub_top K) hK hf).symm⟩

theorem BinaryNaturalSL.equiv_of_autSec {d a : ℕ}
    (h : BinaryNaturalSL (autSec K ⊤ C) ⊤ ⊥ d a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ a ∧
      Nonempty (↥(StatedSL d F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSp4.equiv_of_autSec {a : ℕ}
    (h : BinaryNaturalSp4 (autSec K ⊤ C) ⊤ ⊥ a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ a ∧
      Nonempty (↥(StatedSp 2 F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSU3.equiv_of_autSec {a : ℕ}
    (h : BinaryNaturalSU3 (autSec K ⊤ C) ⊤ ⊥ a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ a) ^ 2 ∧
      Nonempty (↥(StatedSU 3 (2 ^ a) F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSz.equiv_of_autSec {f : ℕ} (h : BinaryNaturalSz (autSec K ⊤ C) ⊤ ⊥ f) :
    ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ f = 2 * a + 1 ∧
      Nat.card F = 2 ^ f ∧ Nonempty (↥(CFSG.Blueprint.suzukiGroup a F) ≃* ↥K) := by
  obtain ⟨a, ha, hfa, F, _, _, hc, hR⟩ := h
  exact ⟨a, F, inferInstance, inferInstance, ha, hfa, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

end Equiv

end CFSG.Quasithin.InternalSec
