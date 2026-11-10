module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.ShultG53

structure Md (X : Type) [Group X] where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module (ZMod 2) carrier]
  [finite : Finite carrier]
  ρ : Representation (ZMod 2) X carrier

attribute [instance] Md.addCommGroup Md.module Md.finite

namespace Md

variable {X : Type} [Group X]

@[expose] def IsInv (M : Md X) (S : AddSubgroup M.carrier) : Prop :=
  ∀ g : X, ∀ m ∈ S, M.ρ g m ∈ S

@[expose] def IsIrred (M : Md X) : Prop :=
  Nontrivial M.carrier ∧ ∀ S : AddSubgroup M.carrier, M.IsInv S → S = ⊥ ∨ S = ⊤

@[expose] def Iso (M N : Md X) : Prop :=
  ∃ f : M.carrier ≃+ N.carrier, ∀ (g : X) (m : M.carrier), f (M.ρ g m) = N.ρ g (f m)

@[expose] def FixesPoint (M : Md X) (S : Set X) : Prop :=
  ∃ v : M.carrier, v ≠ 0 ∧ ∀ g ∈ S, M.ρ g v = v

@[expose] def FixesLine (M : Md X) (S : Set X) : Prop :=
  ∃ L : AddSubgroup M.carrier, Nat.card L = 4 ∧ ∀ g ∈ S, ∀ l ∈ L, M.ρ g l ∈ L

@[expose] def IsPerfect (M : Md X) : Prop :=
  AddSubgroup.closure {z : M.carrier | ∃ (g : X) (m : M.carrier), z = M.ρ g m - m} = ⊤

@[expose] def IsCovering (W V : Md X) : Prop :=
  W.IsPerfect ∧ ∃ (W₀ : AddSubgroup W.carrier) (f : W.carrier →+ V.carrier),
    (∀ w ∈ W₀, ∀ g, W.ρ g w = w) ∧ Function.Surjective f ∧
    (∀ w, f w = 0 ↔ w ∈ W₀) ∧ ∀ g w, f (W.ρ g w) = V.ρ g (f w)

@[expose] def IsUniversalCovering (U V : Md X) : Prop :=
  U.IsCovering V ∧ ∀ W : Md X, W.IsCovering V →
    ∃ π : U.carrier →+ W.carrier, Function.Surjective π ∧ ∀ g u, π (U.ρ g u) = W.ρ g (π u)

@[expose] def IsFiveDimCover (U V : Md X) : Prop :=
  U.IsUniversalCovering V ∧ Nat.card U.carrier = 2 ^ 5

end Md

@[expose] def inG (H : Subgroup (Equiv.Perm (Fin 6))) : Set ↥(alternatingGroup (Fin 6)) :=
  {g | (g : Equiv.Perm (Fin 6)) ∈ H}

section Perm

open Classical

variable {X : Type} [Group X]

@[expose] def permAct (V : Md X) (g : X) (u : V.carrier → ZMod 2) : V.carrier → ZMod 2 :=
  fun w => u (V.ρ g⁻¹ w)

@[expose] def evalZero (V : Md X) : (V.carrier → ZMod 2) →+ ZMod 2 :=
  Pi.evalAddMonoidHom (fun _ : V.carrier => ZMod 2) 0

@[expose] noncomputable def weightHom (V : Md X) : (V.carrier → ZMod 2) →+ ZMod 2 where
  toFun u := ∑ᶠ w, u w
  map_zero' := by simp
  map_add' := fun a b => by
    simpa using finsum_add_distrib (f := fun w => a w) (g := fun w => b w)
      (Set.toFinite _) (Set.toFinite _)

@[expose] def permSpace (V : Md X) : AddSubgroup (V.carrier → ZMod 2) := (evalZero V).ker

@[expose] noncomputable def permCore (V : Md X) : AddSubgroup (V.carrier → ZMod 2) :=
  (evalZero V).ker ⊓ (weightHom V).ker

@[expose] noncomputable def permOnes (V : Md X) : AddSubgroup (V.carrier → ZMod 2) :=
  AddSubgroup.closure {fun w => if w = 0 then 0 else 1}

@[expose] noncomputable def lineCompl (V : Md X) (l : AddSubgroup V.carrier) :
    V.carrier → ZMod 2 :=
  fun w => if w = 0 ∨ w ∈ l then 0 else 1

@[expose] noncomputable def perpCompl (V : Md X) (B : LinearMap.BilinForm (ZMod 2) V.carrier)
    (x : V.carrier) : V.carrier → ZMod 2 :=
  fun w => if w ≠ 0 ∧ B w x ≠ 0 then 1 else 0

@[expose] def singLines (V : Md X) (B : LinearMap.BilinForm (ZMod 2) V.carrier) :
    Set (AddSubgroup V.carrier) :=
  {S | Nat.card S = 4 ∧ ∀ x ∈ S, ∀ y ∈ S, B x y = 0}

end Perm

section Rad

variable {X A : Type} [AddCommGroup A] (act : X → A → A)

@[expose] def InvSub (S : AddSubgroup A) : Prop := ∀ g : X, ∀ a ∈ S, act g a ∈ S

@[expose] def IsMaxInvSub (N K : AddSubgroup A) : Prop :=
  K < N ∧ InvSub act K ∧ ∀ K' : AddSubgroup A, InvSub act K' → K ≤ K' → K' ≤ N → K' = K ∨ K' = N

@[expose] noncomputable def jrad (N : AddSubgroup A) : AddSubgroup A :=
  N ⊓ ⨅ (K : AddSubgroup A) (_ : IsMaxInvSub act N K), K

@[expose] noncomputable def jradPow (n : ℕ) (N : AddSubgroup A) : AddSubgroup A :=
  (jrad act)^[n] N

end Rad


end CFSG.Quasithin.ShultG53
