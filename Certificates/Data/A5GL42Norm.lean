module

public import Certificates.Data.A5GL42

public section

open Matrix

namespace Certificates.A5GL42

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableExistsAndFinset
  Finset.decidableDExistsFinset


@[expose] def FixZero (H : Finset Mat4) : Prop :=
  ∀ v : Vec4, (∀ h ∈ H, h *ᵥ v = v) → v = 0

instance (H : Finset Mat4) : Decidable (FixZero H) := by unfold FixZero; infer_instance


@[expose, irreducible] def O2 : Finset Vec4 :=
  (([7, 11, 13, 14, 15] : List ℕ).map vecOfCode).toFinset


@[expose] def ThirdDiff (Q : Vec4 → ZMod 2) : Prop :=
  ∀ u v w : Vec4, Q (u + v + w) + Q (u + v) + Q (u + w) + Q (v + w) + Q u + Q v + Q w = 0

@[expose] def NonAdd (Q : Vec4 → ZMod 2) : Prop := ∃ u w : Vec4, Q (u + w) ≠ Q u + Q w


set_option synthInstance.maxSize 4096 in
instance (Q : Vec4 → ZMod 2) : Decidable (ThirdDiff Q) := by unfold ThirdDiff; infer_instance

instance (Q : Vec4 → ZMod 2) : Decidable (NonAdd Q) := by unfold NonAdd; infer_instance


end Certificates.A5GL42
