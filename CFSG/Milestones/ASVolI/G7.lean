module

public import CFSG.Milestones.ASVolI.G4
public import CFSG.Blueprint.SourceBinaryGolayCode
import CFSG.Quasithin.Background.RonanG72Sporadic
import CFSG.Quasithin.Background.RonanG73Spor
import CFSG.Quasithin.Background.RonanG73Odd
import CFSG.Quasithin.Background.RonanG73Alt7

public section

namespace CFSG.ASVolI.ChG

@[expose] def IsHyperplaneOf {A : Type*} [Group A] (p : ℕ) (P H : Subgroup A) : Prop :=
  H ≤ P ∧ H.relIndex P = p

@[expose] noncomputable def orbitLen {A : Type*} [Group A] (N H : Subgroup A) : ℕ :=
  Set.ncard {K : Subgroup A | ∃ g ∈ N, K = H.map (MulAut.conj g).toMonoidHom}

@[expose] def IsHeisenberg (p : ℕ) {A : Type*} [Group A] (P : Subgroup A) : Prop :=
  Nat.card P = p ^ 3 ∧ Monoid.exponent P = p ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a

@[expose] def IsLieTypeOddChar (X : Type) [Group X] : Prop :=
  ∃ (t : CFSG.Open.StatedLieTag) (n p f : ℕ), p ≠ 2 ∧
    (CFSG.Open.StatedClassicalModel X t n p f ∨ CFSG.Blueprint.ChevalleyExceptionalModel X t p f ∨
      CFSG.Blueprint.ReeTitsModel X t p f)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11

abbrev GolayAmbient := Fin 24 → ZMod 2

@[expose] def golayConstantLine : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun _ : Fin 24 => (1 : ZMod 2)}

@[expose] def golayPairLine (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun coordinate : Fin 24 =>
    (if coordinate = first then 1 else 0) + (if coordinate = second then 1 else 0)}

@[expose] def golayPairKernel (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient where
  carrier := {word | word first = word second}
  zero_mem' := rfl
  add_mem' := by
    intro left right left_mem right_mem
    change left first = left second at left_mem
    change right first = right second at right_mem
    change left first + right first = left second + right second
    rw [left_mem, right_mem]
  smul_mem' := by
    intro scalar word word_mem
    change word first = word second at word_mem
    change scalar • word first = scalar • word second
    rw [word_mem]

@[expose] def IsGolaySectionModule {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) {Model : Type} [Group Model]
    (small : Bool) (numerator denominator : Submodule (ZMod 2) GolayAmbient) : Prop :=
  ∃ (marking : ↥H ≃* Model) (action : Model →* Equiv.Perm (Fin 24)),
    Function.Injective action ∧
    (∀ permutation : Equiv.Perm (Fin 24),
      (∃ model : Model, action model = permutation) ↔
        (∀ word : GolayAmbient,
          word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
            permAct permutation word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (small = true → permutation 0 = 0 ∧ permutation 1 = 1)) ∧
    denominator ≤ numerator ∧
    (∀ (element : ↥H) (word : ↥numerator),
      permAct (action (marking element)) (word : GolayAmbient) ∈ numerator) ∧
    ∃ quotientMap : ↥numerator →ₗ[ZMod 2] V,
      Function.Surjective quotientMap ∧
      (∀ word : ↥numerator, quotientMap word = 0 ↔ (word : GolayAmbient) ∈ denominator) ∧
      ∀ (element : ↥H) (word image : ↥numerator),
        (image : GolayAmbient) = permAct (action (marking element)) (word : GolayAmbient) →
          quotientMap image = (element : GLV V) (quotientMap word)

@[expose] def IsMathieu24CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      CFSG.Blueprint.EvenSource.sourceGolayCode golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      (permCore 24) CFSG.Blueprint.EvenSource.sourceGolayCode

@[expose] def IsMathieu22CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (CFSG.Blueprint.EvenSource.sourceGolayCode ⊓ golayPairKernel 0 1) golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (permCore 24) (CFSG.Blueprint.EvenSource.sourceGolayCode ⊔ golayPairLine 0 1)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

@[expose] def G_7_1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (GLV V), P ≤ G → IsPGroup p P →
      (Nat.card P = p → orderOf (2 : ZMod p) ≤ d) ∧
      (IsHeisenberg p P → p * orderOf (2 : ZMod p) ≤ d) ∧
      (IsElemAbelian p P → ∀ n : ℕ,
        IsLeast {k | ∃ H, IsHyperplaneOf p P H ∧ k = orbitLen (G ⊓ Subgroup.normalizer (P : Set (GLV V))) H} n →
        n * orderOf (2 : ZMod p) ≤ d ∧
          (d = n * orderOf (2 : ZMod p) → ∀ H, IsHyperplaneOf p P H →
            (∃ v : V, v ≠ 0 ∧ ∀ h ∈ H, h v = v) →
            Nat.card ↥(fixedSpace H) = 2 ^ orderOf (2 : ZMod p)))

section G71Aux

open scoped Classical

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


private instance g71_finite_glv : Finite (GLV V) :=
  Finite.of_injective (fun e : GLV V => (e : V → V))
    fun _ _ h => LinearEquiv.ext fun x => congrFun h x

private noncomputable instance g71_fintype_glv : Fintype (GLV V) := Fintype.ofFinite _

private instance g71_finite_subgroup : Finite (Subgroup (GLV V)) :=
  Finite.of_injective (fun H : Subgroup (GLV V) => (H : Set (GLV V))) SetLike.coe_injective

private instance g71_finite_submodule : Finite (Submodule (ZMod 2) V) :=
  Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective


end G71Aux


@[expose] def G_7_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    CFSG.IsQuasisimple ↥(fStarOf G) → CFSG.SectionRank.IsSQTKCat ↥(fStarOf G) →
    IsIrr (fStarOf G) ⊤ →
      ((∃ s : TauCeti.SporadicName, IsSporadic s (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G))) →
        10 ≤ d) ∧
      (∀ p e : ℕ, p.Prime → p ≠ 2 → 9 < p ^ e → IsPSL 2 p e ↥(fStarOf G) →
        6 < d ∧ (p ^ e ≠ 17 → 8 < d)) ∧
      (∀ (ε : Bool) (p : ℕ), p.Prime → p ≠ 2 →
        (IsPSLEps3 ε p 1 ↥(fStarOf G) ∨ IsSLEps3 ε p ↥(fStarOf G)) → d ≤ 8 →
          IsPSU 3 3 1 ↥(fStarOf G) ∧ d = 6) ∧
      (IsSporadic TauCeti.SporadicName.J4 ↥(fStarOf G) → 110 ≤ d) ∧
      (IsSporadic TauCeti.SporadicName.J2 ↥(fStarOf G) → 12 ≤ d) ∧
      ((IsSporadic TauCeti.SporadicName.HS ↥(fStarOf G) ∨
          IsSporadic TauCeti.SporadicName.He ↥(fStarOf G) ∨
          IsSporadic TauCeti.SporadicName.Ru ↥(fStarOf G)) → 20 ≤ d)

section G72


end G72

@[expose] def G_7_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V)) [Finite ↥G] (d : ℕ),
    Module.finrank (ZMod 2) V = d →
    CFSG.IsQuasisimple ↥(fStarOf G) → CFSG.SectionRank.IsSQTKCat ↥(fStarOf G) →
    IsIrr (fStarOf G) ⊤ → d ≤ 2 * (CFSG.Open.twoRank ↥G + 1) →
      (IsLieTypeOddChar (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G)) →
        ((IsPSL 2 2 2 ↥(fStarOf G) ∨ IsPSL 3 2 1 ↥(fStarOf G) ∨
            Nonempty (↥(fStarOf G) ≃* ↥⁅StatedSp 2 (ZMod 2), StatedSp 2 (ZMod 2)⁆) ∨
            IsHat ↥(fStarOf G) ↥(alternatingGroup (Fin 6))) ∨
          (IsPSU 3 3 1 ↥(fStarOf G) ∧ d = 6))) ∧
      ((∃ s : TauCeti.SporadicName, IsSporadic s (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G))) →
        ((Nonempty (↥G ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12) ∧
            IsPermCoreModule (fStarOf G) CFSG.Blueprint.NativeSporadic.M12) ∨
          (Nonempty (↥(fStarOf G) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧ d = 10 ∧
            IsMathieu22CodeOrCocode (fStarOf G)) ∨
          (Nonempty (↥(fStarOf G) ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧ d = 11 ∧
            IsMathieu24CodeOrCocode (fStarOf G)) ∨
          (∃ N : Subgroup ↥G, N.Normal ∧ N.index = 2 ∧
            IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22 ∧ d = 12))) ∧
      (IsAlt 7 (↥(fStarOf G) ⧸ Subgroup.center ↥(fStarOf G)) →
        IsAlt 7 ↥(fStarOf G) ∧ (d = 4 ∨ d = 6))

section G73


end G73

end CFSG.ASVolI
