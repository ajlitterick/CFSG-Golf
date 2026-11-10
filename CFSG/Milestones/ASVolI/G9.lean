module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Milestones.ASVolI.G4
public import CFSG.Quasithin.Background.Harris.Holds
import CFSG.Quasithin.Background.G9A8OrthModule
import CFSG.Quasithin.Background.SzG11G94Final
import CFSG.Quasithin.Background.G92Main

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def piPrimeCore {A : Type*} [Group A] (π : Set ℕ) (H : Subgroup A) : Subgroup A :=
  sSup {N | N ≤ H ∧ (N.subgroupOf H).Normal ∧ ∀ q ∈ π, q.Prime → Nat.Coprime q (Nat.card N)}

section

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure HypG91 (G A : Subgroup (GLV V)) (m : ℕ) : Prop where
  A_le : A ≤ G
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)

@[expose] def IsOrth4Module (G' : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  ∃ (φ : ↥G' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (ψ : ↥U ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) (ZMod 2)),
    ∀ (g : ↥G') (u u' : ↥U), (u' : V) = (g : GLV V) (u : V) →
      ψ u' = ((φ g).1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ψ u *
        ((φ g).2 : Matrix (Fin 2) (Fin 2) (ZMod 2)).transpose

end


section Cases

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G93p0 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 4 ∧ Module.finrank (ZMod 2) V = 10 ∧ IsPermCoreModule H CFSG.Blueprint.NativeSporadic.M12

@[expose] def G93p1 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧
    Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m ∧ IsMathieu22CodeOrCocode H) ∨
    (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧
      Module.finrank (ZMod 2) V = 11 ∧ 5 ≤ m ∧ IsMathieu24CodeOrCocode H)


@[expose] def G93p2 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 5 ∧ Module.finrank (ZMod 2) V = 12 ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22

@[expose] def G93p3 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ 2 ∧ Module.finrank (ZMod 2) V = 4 ∧ Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def G93p4 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def G93p5 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ IsHat ↥H ↥(alternatingGroup (Fin 6))

@[expose] def G93p6 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 2 * n ∧ n ≤ m + 1 ∧
    IsNaturalMatrixModule H (StatedSL 2 (GaloisField 2 n))

@[expose] def G93p7 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ a : ℕ, Module.finrank (ZMod 2) V = 4 * a ∧ 2 * a ≤ m + 1 ∧
    Nonempty (↥H ≃* ↥(StatedSL 2 (GaloisField 2 (2 * a)))) ∧
    ∃ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) ∧
      IsNaturalMatrixModule H (StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c))

@[expose] def G93p8 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 3 * n ∧ 3 * n ≤ 2 * m + 2 ∧
    IsNaturalMatrixModule H (StatedSL 3 (GaloisField 2 n))

@[expose] def G93p9 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧
    IsNaturalMatrixModule H ⁅StatedSp 2 (GaloisField 2 n), StatedSp 2 (GaloisField 2 n)⁆

@[expose] def G93p10 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 6 * n ∧ 3 * n ≤ m + 1 ∧
    IsG2NaturalModule H
      ⁅CFSG.Open.quasithinG2 (GaloisField 2 n), CFSG.Open.quasithinG2 (GaloisField 2 n)⁆

@[expose] def G93p11 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  1 ≤ m ∧ Module.finrank (ZMod 2) V = 4 ∧ IsNaturalMatrixModule Γ (StatedSL 4 (ZMod 2))

@[expose] def G93p12 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧
    IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 3 (ZMod 2))) ∧
    Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8)))

@[expose] def G93p13 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  Nonempty (↥Γ ≃* ↥(StatedSL 5 (ZMod 2))) ∧
    ((Module.finrank (ZMod 2) V = 5 ∧ 2 ≤ m) ∨ (Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m))

@[expose] def G93p14 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 4 ∧ Module.finrank (ZMod 2) V = 9 ∧ IsL3L3TensorModule H

@[expose] def G93p15 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, 1 < n ∧ Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧
    IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 (GaloisField 2 n)))

@[expose] def G93p16 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule H

@[expose] def G93p17 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Module.finrank (ZMod 2) V = 9 * n ∧ m = 4 * n ∧
    (IsSL3 (2 ^ (2 * n)) ↥H ∨ IsPSL 3 2 (2 * n) ↥H) ∧ IsHermitianTensorModule H n

@[expose] def IsSubSD16Heis (Γ : Subgroup (GLV V)) : Prop :=
  CFSG.Quasithin.IsSubSD16Heis Γ

end Cases

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def G_9_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G A : Subgroup (GLV V)) (m : ℕ),
    HypG91 G A m →
    ∀ X : Subgroup (GLV V), X ≤ G → Group.IsNilpotent ↥X → Odd (Nat.card ↥X) →
      A ≤ Subgroup.normalizer (X : Set (GLV V)) → A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥ →
      (⁅piPrimeCore {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V ≤ 2 * m) →
        ⁅piPrimeCore {3, 5} X, A⁆ = ⊥ ∧
        ∃ (r : ℕ) (Gs : Fin r → Subgroup (GLV V)),
          (⨆ i, Gs i) ≤ X ⊔ A ∧ A ≤ ⨆ i, Gs i ∧ iSupIndep Gs ∧
          (∀ i j, i ≠ j → ∀ x ∈ Gs i, ∀ y ∈ Gs j, x * y = y * x) ∧
          (iSupIndep (fun i => commSpace (Gs i) ⊤) ∧ (⨆ i, commSpace (Gs i) ⊤) = ⊤) ∧
          (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → ∃ h : 0 < r,
            Nonempty (↥(Gs ⟨0, h⟩) ≃* DihedralGroup 5) ∧
              Module.finrank (ZMod 2) ↥(commSpace (Gs ⟨0, h⟩) ⊤) = 4) ∧
          (∀ i : Fin r, (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → 1 ≤ i.val) →
            ((Nonempty (↥(Gs i) ≃* DihedralGroup 3) ∧
                Module.finrank (ZMod 2) ↥(commSpace (Gs i) ⊤) = 2) ∨
              IsOrth4Module (Gs i) (commSpace (Gs i) ⊤))) ∧
          (⁅piPrimeCore {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V = 2 * m) ∧
          (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → Module.finrank (ZMod 2) V = 2 * (m + 1))


@[expose] def G_9_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m →
      G93p0 H m ∨ G93p1 H m ∨ G93p2 Γ m ∨ G93p3 Γ m ∨ G93p4 H m ∨ G93p5 H m ∨ G93p6 H m ∨
      G93p7 H m ∨ G93p8 H m ∨ G93p9 H m ∨ G93p10 H m ∨ G93p11 Γ m ∨ G93p12 H m ∨ G93p13 Γ m ∨
      G93p14 H m ∨ G93p15 H m ∨ G93p16 H m ∨ G93p17 H m


section as_G_9_3


end as_G_9_3

@[expose] def G_9_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A : Subgroup (GLV V)) (m : ℕ), G94PublishedHyp Γ A m →
      G94SmallConcl Γ m ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))) ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
        Nonempty (↥(normalClosure Γ A) ≃* DihedralGroup 5)) ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
        (IsGammaL24 Γ ∨ ∃ q : V → ZMod 2, IsPlusQuadForm q ∧
          pCoreOf 3 (orthogonalSubgroupOf q) ≤ Γ ∧ Γ ≤ orthogonalSubgroupOf q)) ∨
      (m = 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
        ∃ q : V → ZMod 2, IsPlusQuadForm q ∧ Γ ≤ orthogonalSubgroupOf q ∧
          Γ.relIndex (orthogonalSubgroupOf q) ≤ 2) ∨
      (m = 2 ∧ Module.finrank (ZMod 2) V = 6 ∧ ChG.IsSubSD16Heis Γ)

section SmallZero


end SmallZero


end CFSG.ASVolI
