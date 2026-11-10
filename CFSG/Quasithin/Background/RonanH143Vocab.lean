module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Monster.CodeAut.Perm
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Monster.Code.Weights

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code

abbrev P24 : Type := Equiv.Perm (Fin 24)

@[expose] def conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) : Subgroup X :=
  A.map (MulAut.conj g).toMonoidHom

@[expose] def MY {α : Type*} [MulAction P24 α] (Γ : Subgroup P24) (Y : α) : Subgroup P24 :=
  Γ ⊓ MulAction.stabilizer P24 Y

@[expose] def KY {α : Type*} [MulAction P24 α] (Γ : Subgroup P24) (Y : α) : Subgroup P24 :=
  pCoreOf 2 (MY Γ Y)

@[expose] def IsE2k (k : ℕ) (A : Subgroup P24) : Prop := IsElemAbelian 2 A ∧ Nat.card A = 2 ^ k

@[expose] def natHom (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

@[expose] def natSub (d : ℕ) (K : Type*) [Field K] (S : Subgroup (GL (Fin d) K)) :
    Subgroup (MulAut (Multiplicative (Fin d → K))) :=
  S.map (natHom d K)

@[expose] def ConjIso {X : Type*} [Group X] (G K : Subgroup X) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) (φ : ↥K ≃* A) (π : ↥G →* MulAut A) : Prop :=
  K ≤ G ∧ (∀ g, π g ∈ Γ) ∧ (∀ γ ∈ Γ, ∃ g, π g = γ) ∧ (∀ g : ↥G, π g = 1 ↔ (g : X) ∈ K) ∧
    ∀ (g : ↥G) (k k' : ↥K), (k' : X) = (g : X) * k * (g : X)⁻¹ → φ k' = π g (φ k)

@[expose] def ConjIsoModel {X : Type*} [Group X] (G K : Subgroup X) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) : Prop :=
  ∃ (φ : ↥K ≃* A) (π : ↥G →* MulAut A), ConjIso G K A Γ φ π

@[expose] def ConjSymNatural (G K : Subgroup P24) (n : ℕ) (R : Subgroup (Equiv.Perm (Fin n))) :
    Prop :=
  K ≤ G ∧ ∃ (π : ↥G →* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* P24),
    π.range = R ∧ π.ker = K.subgroupOf G ∧ β.range = K ∧ β.ker = G6.natKer n ∧
    ∀ (g : ↥G) (u : ↥(G6.coreMod n)), β (G6.coreAct n (π g) u) = (g : P24) * β u * (g : P24)⁻¹

@[expose] def M22g (a b : Fin 24) : Subgroup P24 :=
  AutPerm ⊓ MulAction.stabilizer P24 a ⊓ MulAction.stabilizer P24 b

@[expose] def M2ab (a b : Fin 24) : Subgroup P24 :=
  AutPerm ⊓ MulAction.stabilizer P24 ({a, b} : Finset (Fin 24))


end CFSG.Quasithin.RonanH143
