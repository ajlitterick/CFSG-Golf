module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def Hn (n : ℕ) : Subgroup (AEQ n) := (aeSub n).map (mkQ n)

@[expose] def PermMembers {n : ℕ} (H : Subgroup (AEQ n)) (σ : ↥H →* ↥H) : Prop :=
  ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), ∃ (β' : Finset (Fin n)) (hβ' : β'.card = 4)
    (c' : Bool), ∀ x : ↥H, (x : AEQ n) ∈ memBar β hβ c → (σ x : AEQ n) ∈ memBar β' hβ' c'

@[expose] def AEAut (n : ℕ) : Prop :=
  ∀ (H : Subgroup (AEQ n)), H = Hn n → ∀ σ : ↥H →* ↥H, Function.Bijective σ → PermMembers H σ →
    ∃ w : Wr n, ∀ x : ↥H, (σ x : AEQ n) = mkQ n w * (x : AEQ n) * (mkQ n w)⁻¹


@[expose] def IsMember {n : ℕ} (M : Subgroup (AEQ n)) : Prop :=
  ∃ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), M = memBar β hβ c

@[expose] def IsBlock {n : ℕ} (B : Set (Subgroup (AEQ n))) : Prop :=
  (∀ M ∈ B, IsMember M) ∧ ∀ s ∈ Hn n, (fun M => M.map (MulAut.conj s).toMonoidHom) '' B = B ∨
      Disjoint ((fun M => M.map (MulAut.conj s).toMonoidHom) '' B) B

theorem memBar_le_Hn {n : ℕ} (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool) :
    memBar β hβ c ≤ Hn n := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, ?_, rfl⟩
  cases c
  · exact memKStar_le_aeSub _ hw
  · exact memK_le_aeSub _ hw


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
