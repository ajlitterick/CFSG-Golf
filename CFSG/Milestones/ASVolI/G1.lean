module

public import CFSG.Quasithin.Background.G13Theta
public import CFSG.Quasithin.Background.G13Fam
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.G13Two

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin.G1

@[expose] def conjSub {G : Type*} [Group G] (X : Subgroup G) (g : G) : Subgroup G :=
  X.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def IsIrreducibleSub {G : Type*} [Group G] {U : Type*} [AddCommGroup U]
    [DistribMulAction G U] (X : Subgroup G) (W : AddSubgroup U) : Prop :=
  W ≠ ⊥ ∧ (∀ g ∈ X, ∀ w ∈ W, g • w ∈ W) ∧
    ∀ Y : AddSubgroup U, Y ≤ W → (∀ g ∈ X, ∀ y ∈ Y, g • y ∈ Y) → Y = ⊥ ∨ Y = W

section natural

variable {F : Type} [Field F] {n : ℕ} {U : Type} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]

@[expose] def IsSumOfNatural (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F))
    (S : Submodule F (Fin n → F)) (Y : AddSubgroup U) (s : ℕ) : Prop :=
  ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ (⨆ j, W j) = Y ∧ ∀ j,
    (∀ g ∈ X, ∀ w ∈ W j, g • w ∈ W j) ∧
    ∃ f : (Fin n → F) →+ U, Set.InjOn f S ∧ S.toAddSubgroup.map f = W j ∧
      ∀ g ∈ X, ∀ v ∈ S, f (g • v) = g • f v

@[expose] def Uij (φ : Submodule F (Fin n → F) → AddSubgroup U) (i j : Fin n) : AddSubgroup U :=
  φ (Vi F n i) ⊔ φ (Vi F n j)

@[expose] def Uhat (φ : Submodule F (Fin n → F) → AddSubgroup U) (i : Fin n) : AddSubgroup U :=
  ⨆ k : {k : Fin n // k ≠ i}, φ (Vi F n k)

@[expose] def Uhatij (φ : Submodule F (Fin n → F) → AddSubgroup U) (i j : Fin n) :
    AddSubgroup U :=
  ⨆ k : {k : Fin n // k ≠ i ∧ k ≠ j}, φ (Vi F n k)

end natural

@[expose] def IsFullFlag (F : Type) [Field F] (n : ℕ) (W : Fin (n + 1) → Submodule F (Fin n → F)) :
    Prop :=
  Monotone W ∧ ∀ i : Fin (n + 1), Module.finrank F (W i) = i

@[expose] def flagSylow (F : Type) [Field F] (n : ℕ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
  ⨆ (i : Fin n) (j : Fin n) (_ : i < j), Rij F i j

@[expose] def oTwoPrimeUpper {A : Type*} [Group A] (X : Subgroup A) : Subgroup A :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin.G1 CFSG.ASVolI.ChG

@[expose] def G_1_2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n →
    (∀ i j : Fin n, i ≠ j →
      commSub F (Lij F i j) = Vij F i j ∧ fixSub F (Lij F i j) = Vhatij F i j ∧
      Lij F i j = ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j) ∧
      Nonempty (Lij F i j ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
    Ladj F n = ⊤


@[expose] def G_1_3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          IsSumOfNatural (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) ⊤ (⊤ : AddSubgroup U) s


@[expose] def G_1_4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    (∀ W W' : Fin (n + 1) → Submodule F (Fin n → F), IsFullFlag F n W → IsFullFlag F n W' →
      ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ i, actSub g (W i) = W' i) ∧
    (∀ A₁ A₂ B₁ B₂ : Submodule F (Fin n → F), IsPoint A₁ → IsPoint A₂ → IsPoint B₁ →
      IsPoint B₂ → A₁ ≠ A₂ → B₁ ≠ B₂ →
      ∃ g : Matrix.SpecialLinearGroup (Fin n) F, actSub g A₁ = B₁ ∧ actSub g A₂ = B₂) ∧
    (IsFlag (Vi F n ⟨0, by omega⟩) (Vhat F n ⟨1, by omega⟩) ∧
      Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ =
        rootGroup (Vi F n ⟨0, by omega⟩) (Vhat F n ⟨1, by omega⟩) ∧
      ∀ A A' : Submodule F (Fin n → F), IsPoint A → IsPoint A' → A ≤ Vhat F n ⟨1, by omega⟩ →
        A' ≤ Vhat F n ⟨1, by omega⟩ → A ≠ Vi F n ⟨0, by omega⟩ → A' ≠ Vi F n ⟨0, by omega⟩ →
        ∃ g ∈ setStab F (Vi F n ⟨0, by omega⟩) ⊓ setStab F (Vhat F n ⟨1, by omega⟩),
          actSub g A = A') ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U,
        (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (A : Submodule F (Fin n → F)), IsPoint A →
          φ (actSub g A) = (φ A).map (actU g)) →
        (⨆ i : Fin n, φ (Vi F n i)) = ⊤ →
        φ (Vi F n ⟨0, by omega⟩) ⊓ φ (Vi F n ⟨1, by omega⟩) = ⊥ →
        (∀ r ∈ Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, ∀ u ∈ φ (Vi F n ⟨1, by omega⟩),
          r • u - u ∈ φ (Vi F n ⟨0, by omega⟩)) →
        φ (Vi F n ⟨0, by omega⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) →
        (∀ h : 2 < n, φ (Vi F n ⟨2, h⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) →
        G13Hyp F n U φ)

section G14

variable {F : Type} [Field F] {n : ℕ}


end G14


@[expose] def G_1_5 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    (∃ A : Submodule F (Fin 2 → F), IsPoint A ∧ R = rootGroup A A) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ →
      ∀ A : Submodule F (Fin 2 → F), IsPoint A → R = rootGroup A A →
        φ A = commU R ∧ φ A = fixU R ∧
        ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g ∉ Subgroup.normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 2) F)) →
          IsCompl (commU (U := U) R) (commU (U := U) (conjSub R g))) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (Y : AddSubgroup U),
        (∀ x ∈ Subgroup.normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 2) F)), ∀ y ∈ Y, x • y ∈ Y) → commU (U := U) R ≤ Y → Y ≤ fixU (U := U) R →
        IsCompl Y (Y.map (actU g⁻¹)) →
        ∀ A : Submodule F (Fin 2 → F), IsPoint A → R = rootGroup A A →
          ∃ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ ∧
            ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
              φ (actSub x⁻¹ A) = Y.map (actU x⁻¹)) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ((∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
          IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) ↔
        (commU (U := U) R ≤ fixU (U := U) R ∧
          ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 → Odd (orderOf x) →
            fixU (U := U) (Subgroup.zpowers x) = ⊥)) ∧
      ((∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
          IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) ↔
        (commU (U := U) R ≤ fixU (U := U) R ∧
          ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ Odd (orderOf x) ∧
            fixU (U := U) (Subgroup.zpowers x) = ⊥)))

section G15Help

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]


end G15Help


section G15Four

variable {F : Type} [Field F]


end G15Four


@[expose] def G_1_6 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], 2 < Nat.card F →
    ∀ (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      (⨆ g : Matrix.SpecialLinearGroup (Fin 2) F, (fixU (U := U) R).map (actU g)) = ⊤ →
      (∀ r ∈ R, r ≠ 1 → fixU (U := U) (Subgroup.zpowers r) = fixU (U := U) R) →
      ∃ (s : ℕ) (f : U →+ (Fin s → Fin 2 → F)), Function.Surjective f ∧
        (∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (u : U) (i : Fin s),
          f (g • u) i = g • f u i) ∧
        f.ker = fixU (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))

section G16

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]


private def g16qAct {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) →+
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
  QuotientAddGroup.map _ _ (actU g) fun c hc k _ => by
    show k • g • c = g • c
    calc k • g • c = (k * g) • c := (mul_smul k g c).symm
      _ = (g * (g⁻¹ * k * g)) • c := by congr 1; group
      _ = g • ((g⁻¹ * k * g) • c) := mul_smul _ _ _
      _ = g • c := by rw [hc (g⁻¹ * k * g) (Subgroup.mem_top _)]

private instance g16Quot {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F)
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) where
  smul g q := g16qAct g q
  one_smul q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (one_smul _ v)
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (mul_smul g h v)
  smul_zero g := map_zero (g16qAct g)
  smul_add g q r := map_add (g16qAct g) q r


private def g16Tw (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type) : Type := V

private instance g16TwAddCommGroup (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] : AddCommGroup (g16Tw g V) :=
  inferInstanceAs (AddCommGroup V)

private instance g16TwDMA (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) (g16Tw g V) where
  smul k v := ((g * k * g⁻¹) • (show V from v) : V)
  one_smul v := by
    show (g * 1 * g⁻¹) • (show V from v) = show V from v
    rw [mul_one, mul_inv_cancel, one_smul]
  mul_smul k l v := by
    show (g * (k * l) * g⁻¹) • (show V from v) =
      (g * k * g⁻¹) • ((g * l * g⁻¹) • (show V from v))
    rw [← mul_smul, show g * k * g⁻¹ * (g * l * g⁻¹) = g * (k * l) * g⁻¹ by group]
  smul_zero k := by
    show (g * k * g⁻¹) • (0 : V) = 0
    exact smul_zero _
  smul_add k v w := by
    show (g * k * g⁻¹) • ((show V from v) + (show V from w)) =
      (g * k * g⁻¹) • (show V from v) + (g * k * g⁻¹) • (show V from w)
    exact smul_add _ _ _

private instance g16TwFinite (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [Finite V] : Finite (g16Tw g V) :=
  inferInstanceAs (Finite V)

end G16

section G16Thm

open CFSG.Quasithin.SL2Model


end G16Thm

@[expose] def G_1_7 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      (∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) →
      ∃ s : ℕ, Nat.card (commU (U := U) R) = Nat.card F ^ s ∧
        IsSumOfNatural (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ⊤ (⊤ : AddSubgroup U) s


@[expose] def G_1_8 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        (⨆ i : Fin n, φ (Vi F n i)) = ⊤


@[expose] def G_1_10 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          (Disjoint (φ (Vi F n ⟨0, by omega⟩)) (φ (Vi F n ⟨1, by omega⟩)) ∧
            IsSumOfNatural (Lij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
              (Vij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
              (Uij φ ⟨0, by omega⟩ ⟨1, by omega⟩) s) ∧
          IsCompl (Uij φ ⟨0, by omega⟩ ⟨1, by omega⟩) (Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
          Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩ =
            fixU (Lij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) ∧
          (Disjoint (φ (Vi F n ⟨0, by omega⟩)) (Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
            Uhat φ ⟨1, by omega⟩ = φ (Vi F n ⟨0, by omega⟩) ⊔ Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
            Uhat φ ⟨1, by omega⟩ = fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) ∧
          IsCompl (φ (Vi F n ⟨0, by omega⟩)) (Uhat φ ⟨0, by omega⟩)


@[expose] def G_1_11 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 3 ≤ n →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        iSupIndep (fun i : Fin n => φ (Vi F n i)) ∧ (⨆ i : Fin n, φ (Vi F n i)) = ⊤


@[expose] def G_1_12 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 3 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        (φ (Vi F n ⟨0, by omega⟩) = fixU (flagSylow F n) ∧
          φ (Vi F n ⟨0, by omega⟩) =
            fixU (oTwoPrimeUpper (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))))) ∧
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ (⨆ j, W j) = φ (Vi F n ⟨0, by omega⟩) ∧
            ∀ j, IsIrreducibleSub (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))) (W j) ∧
              Nat.card (W j) = Nat.card F


end CFSG.ASVolI
