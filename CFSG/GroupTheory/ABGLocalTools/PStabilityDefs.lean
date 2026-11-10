module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.ABGQGroups.Defs

public section

open Subgroup

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion CFSG.ABGQGroups

instance solvableRadical_normal_instance {H : Type*} [Group H] : (solvableRadical H).Normal :=
  solvableRadical_normal

section Signalizers

variable {H : Type*} [Group H]

@[expose] def pSignalizers (X : Subgroup H) (p : ℕ) : Set (Subgroup H) :=
  {R | IsPGroup p R ∧ X ≤ normalizer (R : Set H) ∧ R ⊓ X = ⊥}

@[expose] def IsMaximalPSignalizer (X : Subgroup H) (p : ℕ) (R : Subgroup H) : Prop :=
  R ∈ pSignalizers X p ∧ ∀ R' ∈ pSignalizers X p, R ≤ R' → R' = R


end Signalizers

section Standing

variable (p q : ℕ) (H : Type*) [Group H]

structure QGroupStanding : Prop where
  charPower : HasQCharPower H q
  five_lt : 5 < q
  sylow : HasQDOrWreathedSylow H
  pPrimeCore_le : pPrimeCore p H ≤ solvableRadical H


end Standing

end CFSG.ABGLocalTools
