module

public import Mathlib
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.H11Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

open scoped commutatorElement

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def linToMulAut (F W : Type*) [Field F] [AddCommGroup W] [Module F W] :
    (W ≃ₗ[F] W) →* MulAut (Multiplicative W) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl


section Orth

variable (F : Type*) [Field F]


end Orth


section General

variable {V : Type*} [CommGroup V]


@[expose] def commOn (W : Subgroup V) (A : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {u | ∃ a ∈ A, ∃ w ∈ W, u = a w * w⁻¹}

@[expose] def conjAut (g : MulAut V) (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A.map (MulAut.conj g).toMonoidHom


@[expose] def natHom (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
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

end General

section Chief

variable {A : Type*} [Group A]

@[expose] def IsActsInv (acts : Set (A → A)) (U : Subgroup A) : Prop :=
  ∀ f ∈ acts, ∀ u ∈ U, f u ∈ U

@[expose] def IsChiefFactorUnder (acts : Set (A → A)) (X Y : Subgroup A) : Prop :=
  X < Y ∧ IsActsInv acts X ∧ IsActsInv acts Y ∧
    ∀ W : Subgroup A, X ≤ W → W ≤ Y → IsActsInv acts W → W = X ∨ W = Y

@[expose] def NoncentralChiefCount (acts : Set (A → A)) (U : Subgroup A) (c : ℕ) : Prop :=
  ∃ (k : ℕ) (S : ℕ → Subgroup A), S 0 = ⊥ ∧ S k = U ∧
    (∀ i < k, IsChiefFactorUnder acts (S i) (S (i + 1))) ∧
    Set.ncard {i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} = c

end Chief

@[expose] def actsOnModule {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) : Set (V → V) :=
  {f | ∃ y ∈ Y, f = fun v => y v}


@[expose] def glStab {K : Type*} [Field K] (S : Set (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ S ∧
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ S}
  mul_mem' {g h} hg hh v hv := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh v hv).1).1
    · rw [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg v hv).2).2
  one_mem' v hv := by
    simpa using hv
  inv_mem' {g} hg v hv := by
    refine ⟨(hg v hv).2, ?_⟩
    simpa using (hg v hv).1

@[expose] def glFix {K : Type*} [Field K] (S : Set (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) K).mulVec v = v}
  mul_mem' {g h} hg hh v hv := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh v hv, hg v hv]
  one_mem' v hv := by simp
  inv_mem' {g} hg v hv := by
    have h := hg v hv
    calc ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v
        = ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
            ((g : Matrix (Fin 3) (Fin 3) K).mulVec v) := by rw [h]
      _ = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def IsIrredOn {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  W ≠ ⊥ ∧ ∀ U : Subgroup V, U ≤ W → (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = W

@[expose] def IsConjIn {X : Type*} [Group X] (G : Subgroup X) (u v : X) : Prop :=
  ∃ g ∈ G, g * u * g⁻¹ = v


@[expose] def IsTwoCentralElt {X : Type*} [Group X] (M : Subgroup X) (a : X) : Prop :=
  ∃ S : Subgroup X, IsSylowIn 2 S M ∧ ∀ s ∈ S, s * a = a * s

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.ASVolI.ChH


end CFSG.ASVolI
