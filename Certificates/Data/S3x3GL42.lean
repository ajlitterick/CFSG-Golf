module

public import Certificates.Data.A5GL42

public section

open Matrix

namespace Certificates.S3x3GL42

open Certificates.A5GL42 (Mat4 Vec4)


@[expose] def RelAB (a b : Mat4) : Prop :=
  a * a * a = 1 ∧ a ≠ 1 ∧ b * b * b = 1 ∧ b ≠ 1 ∧ a * b = b * a

@[expose] def RelC (a b c : Mat4) : Prop := c * c = 1 ∧ c * a = a * a * c ∧ c * b = b * c


set_option synthInstance.maxSize 1024 in
instance (a b : Mat4) : Decidable (RelAB a b) := by unfold RelAB; infer_instance

set_option synthInstance.maxSize 1024 in
instance (a b c : Mat4) : Decidable (RelC a b c) := by unfold RelC; infer_instance

@[expose] def fixV (a : Mat4) : Finset Vec4 := Finset.univ.filter fun v => a *ᵥ v = v

@[expose] def NonSing (g : Mat4) : Prop := ∀ v : Vec4, g *ᵥ v = 0 → v = 0

instance (g : Mat4) : Decidable (NonSing g) := by unfold NonSing; infer_instance


@[expose] def TypeIFacts (a b c : Mat4) : Prop :=
  (fixV a).card = 4 ∧ (fixV b).card = 4 ∧ (∀ v ∈ fixV a, v ∈ fixV b → v = 0) ∧
    (∀ v ∈ fixV a, c *ᵥ v = v) ∧ ∀ u : Vec4, ∃ x ∈ fixV a, ∃ y ∈ fixV b, u = x + y

set_option synthInstance.maxSize 1024 in
instance (a b c : Mat4) : Decidable (TypeIFacts a b c) := by unfold TypeIFacts; infer_instance


end Certificates.S3x3GL42
