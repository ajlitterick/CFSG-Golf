module

public import CFSG.Quasithin.Background.SimsG45Sylow
public import CFSG.Quasithin.Background.SimsG48
public import CFSG.Quasithin.Background.SimsG44Nonsplit
public import CFSG.Quasithin.Background.SimsG41
public import CFSG.Quasithin.Background.SimsG49Main
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChG

open CFSG.Open

section Sp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

structure IsSymp4 (B : LinearMap.BilinForm F V) : Prop where
  finrank_eq : Module.finrank F V = 4
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

@[expose] def spGroup (B : LinearMap.BilinForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' := fun {g h} hg hh x y => by
    change B (g (h x)) (g (h y)) = B x y
    rw [hg, hh]
  one_mem' := fun x y => rfl
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm

@[expose] def IsSympBasis (B : LinearMap.BilinForm F V) (b : Module.Basis (Fin 4) F V) : Prop :=
  ∀ i j : Fin 4, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0

@[expose] def subfieldSpOf (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) :
    Set (V ≃ₗ[F] V) :=
  {g | ∀ i j, LinearMap.toMatrix b b (g : V →ₗ[F] V) i j ∈ F₀}

@[expose] def IsTransv (g : V ≃ₗ[F] V) : Prop :=
  Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = 1 ∧
    ((g : V →ₗ[F] V) - LinearMap.id) ∘ₗ ((g : V →ₗ[F] V) - LinearMap.id) = 0

@[expose] def commSpace (g : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)

@[expose] def IsMaximalSymplecticParabolic (B : LinearMap.BilinForm F V)
    (Qhat : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ isotropicSpace : Submodule F V,
    (Module.finrank F isotropicSpace = 1 ∨ Module.finrank F isotropicSpace = 2) ∧
    (∀ vector ∈ isotropicSpace, ∀ other ∈ isotropicSpace, B vector other = 0) ∧
    ∀ automorphism : V ≃ₗ[F] V,
      automorphism ∈ Qhat ↔ automorphism ∈ spGroup B ∧
        isotropicSpace.map (automorphism : V →ₗ[F] V) = isotropicSpace

@[expose] def twoPrimeResidual (H : Type*) [Group H] : Subgroup H :=
  sInf {N : Subgroup H | N.Normal ∧ Odd N.index}

@[expose] def twoPrimeResidualOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (twoPrimeResidual ↥H).map H.subtype

@[expose] def transvSet (G₀ : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V) :=
  {d | d ∈ G₀ ∧ IsTransv d}

@[expose] def transvGen (G₀ : Subgroup (V ≃ₗ[F] V)) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure (transvSet G₀)

@[expose] def transvFix (G₀ : Subgroup (V ≃ₗ[F] V)) (X : Submodule F V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {d | d ∈ transvSet G₀ ∧ ∀ x ∈ X, d x = x}

@[expose] def IsIrredOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∀ W : Submodule F V, (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsImprimitiveOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ (r : ℕ) (W : Fin r → Submodule F V), 1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧
    (⨆ i, W i) = ⊤ ∧ ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j

@[expose] def rootGroupHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {g | g ∈ spGroup B ∧ IsTransv g ∧ commSpace g = commSpace d}

@[expose] def xHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {e | e ∈ spGroup B ∧ IsTransv e ∧ e * d = d * e}

@[expose] def advSet (G₀ : Subgroup (V ≃ₗ[F] V)) (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d ≠ d * e}

@[expose] def dSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))
    (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d = d * e ∧ e ∉ rootGroupHat B d}

@[expose] def advGraph (G₀ : Subgroup (V ≃ₗ[F] V)) : SimpleGraph ↥(transvSet G₀) :=
  SimpleGraph.fromRel fun a b => (a : V ≃ₗ[F] V) * b ≠ b * a

@[expose] def invSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Set (V ≃ₗ[F] V) :=
  {i | i ∈ transvGen G₀ ∧ i ≠ 1 ∧ i * i = 1 ∧ ∃ a ∈ transvSet G₀, ∃ b ∈ dSet B G₀ a, i = a * b}

@[expose] def IsNondegLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0

@[expose] def IsTotSingLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, ∀ w' ∈ W, B w w' = 0

end Sp

section Orth

variable (K : Type) [Field K]

@[expose] def isometryGroup (q : (Fin 4 → K) → K) : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) where
  carrier := {M | ∀ v, q ((M : Matrix (Fin 4) (Fin 4) K).mulVec v) = q v}
  mul_mem' := fun {M N} hM hN v => by
    have h1 := hM ((N : Matrix (Fin 4) (Fin 4) K).mulVec v)
    have h2 := hN v
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1 ⊢
    rw [h1, h2]
  one_mem' := fun v => by simp
  inv_mem' := fun {M} hM v => by
    have h := hM (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v)
    rw [Matrix.mulVec_mulVec] at h
    have h2 : ((M : Matrix (Fin 4) (Fin 4) K) *
        ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h
    exact h.symm

@[expose] def qPlus (v : Fin 4 → K) : K := v 0 * v 1 + v 2 * v 3

@[expose] def qMinus (c : K) (v : Fin 4 → K) : K :=
  v 0 * v 1 + v 2 ^ 2 + v 2 * v 3 + c * v 3 ^ 2

@[expose] def IsO4Type (k : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qPlus (GaloisField 2 k))) ∨
    ∃ c : GaloisField 2 k, (¬ ∃ x : GaloisField 2 k, x ^ 2 + x + c = 0) ∧
      Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qMinus (GaloisField 2 k) c))

@[expose] def orthAct {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 3 → F) : Fin 3 → F :=
  let M : Matrix (Fin 2) (Fin 2) F := !![v 0, v 1; v 1, v 2]
  let N : Matrix (Fin 2) (Fin 2) F :=
    (g : Matrix (Fin 2) (Fin 2) F) * M * (g : Matrix (Fin 2) (Fin 2) F).transpose
  ![N 0 0, N 0 1, N 1 1]

end Orth

section Cases

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def fStarOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (CFSG.generalizedFitting ↥H).map H.subtype

structure HypG41 (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop where
  le_sp : G₀ ≤ spGroup B
  kgroup : CFSG.SectionRank.IsKGroupCat ↥G₀
  irred : IsIrredOnV G₀
  nonempty : (transvSet G₀).Nonempty

@[expose] def G41Factor (n : ℕ) (X : Subgroup (V ≃ₗ[F] V)) : Prop :=
  (∃ k : ℕ, k ∣ n ∧ Nonempty (↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
    ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧ Nonempty (↥X ≃* DihedralGroup m)

@[expose] def G41Case1 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      IsSympBasis B b ∧ 0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
      Nonempty (↥G₀ ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 k)))

@[expose] def G41Case2 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case2AtExponent (n k : ℕ) (B : LinearMap.BilinForm F V)
    (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case3 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  ∃ V₁ V₂ : Submodule F V, IsNondegLine B V₁ ∧ V₂ = LinearMap.BilinForm.orthogonal B V₁ ∧
    IsCompl V₁ V₂ ∧
    (∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) ∧
    (∃ t ∈ G₀, t * t = 1 ∧ V₁.map (t : V →ₗ[F] V) = V₂ ∧
      G₀ = transvGen G₀ ⊔ Subgroup.zpowers t) ∧
    (transvGen G₀ = transvFix G₀ V₂ ⊔ transvFix G₀ V₁ ∧
      transvFix G₀ V₂ ⊓ transvFix G₀ V₁ = ⊥ ∧
      ∀ a ∈ transvFix G₀ V₂, ∀ b ∈ transvFix G₀ V₁, a * b = b * a) ∧
    G41Factor n (transvFix G₀ V₂) ∧ G41Factor n (transvFix G₀ V₁)

end Cases

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChG

@[expose] def G_4_1 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        G41Case1 n B G₀ ∨ G41Case2 n B G₀ ∨ G41Case3 n B G₀

section as_G_4_1


end as_G_4_1

@[expose] def G_4_3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        pCoreOf 2 G₀ = ⊥ ∧ pCoreOf 2 (transvGen G₀) = ⊥ ∧
          ∃ a ∈ transvGen G₀, ∃ b ∈ transvGen G₀, a * b ≠ b * a


@[expose] def G_4_4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      (∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → ∀ d ∈ transvSet G₀, (advSet G₀ d).Nonempty) ∧
      ∀ d : V ≃ₗ[F] V, d ∈ spGroup B → IsTransv d →
        (∃ φ : ↥(xHat B d) →* Matrix.SpecialLinearGroup (Fin 2) F,
          Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(xHat B d) ∧
          ∃ ψ : ↥(CFSG.pCore 2 ↥(xHat B d)) ≃* Multiplicative (Fin 3 → F),
            ∀ (g : ↥(xHat B d)) (x y : ↥(CFSG.pCore 2 ↥(xHat B d))),
              g * (x : ↥(xHat B d)) * g⁻¹ = (y : ↥(xHat B d)) →
                Multiplicative.toAdd (ψ y) = orthAct (φ g) (Multiplicative.toAdd (ψ x))) ∧
        Subgroup.center ↥(xHat B d) = (rootGroupHat B d).subgroupOf (xHat B d) ∧
        (1 < n → ∀ W : Subgroup ↥(xHat B d), W ≤ CFSG.pCore 2 ↥(xHat B d) → W.Normal →
          W ⊓ Subgroup.center ↥(xHat B d) = ⊥ →
          W ⊔ Subgroup.center ↥(xHat B d) ≠ CFSG.pCore 2 ↥(xHat B d)) ∧
        ∃ Qhat : Subgroup (V ≃ₗ[F] V), IsMaximalSymplecticParabolic B Qhat ∧
          xHat B d = twoPrimeResidualOf Qhat


@[expose] def G_4_5 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        (∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, orderOf (a * b) = 2 ∨ Odd (orderOf (a * b))) ∧
        (∀ a ∈ transvSet G₀, ∀ b ∈ advSet G₀ a, IsNondegLine B (commSpace a ⊔ commSpace b)) ∧
        ∀ a ∈ transvSet G₀, ∀ b ∈ dSet B G₀ a,
          IsTotSingLine B (commSpace a ⊔ commSpace b) ∧
            IsSylowTwoOf (Subgroup.centralizer ({a * b} : Set (V ≃ₗ[F] V)) ⊓ spGroup B) (spGroup B)


@[expose] def G_4_6 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ →
        (¬ (advGraph G₀).Connected ↔
          ¬ ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, ∃ g ∈ transvGen G₀, g * a * g⁻¹ = b) ∧
        (¬ (advGraph G₀).Connected ↔ IsImprimitiveOnV G₀) ∧
        (¬ (advGraph G₀).Connected ↔ G41Case3 n B G₀)

section as_G_4_6


end as_G_4_6

@[expose] def G_4_7 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
        G₀ = transvGen G₀

section as_G_4_7


end as_G_4_7

@[expose] def G_4_8 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
      ∀ a ∈ transvSet G₀, ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ transvGen G₀ →
        a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)) → IsIrredOnV H →
      ∀ I : AddSubgroup V, I ≠ ⊥ →
        (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, g x ∈ I) →
        (∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y, g y ∈ Y) →
          Y = ⊥ ∨ Y = I) →
        ∃ F₀ : Subfield F,
          (∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) ∧
          (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) →
            (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, f (g x) = g (f x)) →
            ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
          (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) → (∀ h ∈ H, ∀ x ∈ I, f (h x) = h (f x)) →
            ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
          (∀ Y : AddSubgroup V, Y ≤ I → (∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) →
            (∀ c ∈ F₀, ∀ y ∈ Y, c • y ∈ Y) → Y = ⊥ ∨ Y = I) ∧
          (∃ β : LinearMap.BilinForm F₀ V,
            (∀ h ∈ H, ∀ x ∈ I, ∀ y ∈ I, β (h x) (h y) = β x y) ∧
            ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, β x y ≠ 0) ∧
          (Submodule.span F (I : Set V) = ⊤ ∧
            ∀ (ι : Type) [Fintype ι] (v : ι → V), (∀ i, v i ∈ I) →
              LinearIndependent F₀ v → LinearIndependent F v) ∧
          (∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b ∧
            ∀ g ∈ H ⊔ Subgroup.zpowers a, g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
          (∀ B' : LinearMap.BilinForm F V, IsSymp4 B' →
            (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x y, B' (g x) (g y) = B' x y) →
            ∃ c : F, c ≠ 0 ∧ B' = c • B)


@[expose] def G_4_9 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), Nat.card F = 2 ^ n →
    ∀ (V : Type) [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V), IsSymp4 B →
      ∀ G₀ : Subgroup (V ≃ₗ[F] V), HypG41 B G₀ → (advGraph G₀).Connected →
        (IsSimpleGroup ↥(fStarOf (transvGen G₀)) ∧
            (∃ x ∈ fStarOf (transvGen G₀), ∃ y ∈ fStarOf (transvGen G₀), x * y ≠ y * x) ∧
            (∃ i ∈ invSet B G₀, i ∈ fStarOf (transvGen G₀)) ∧
            IsIrredOnV (fStarOf (transvGen G₀))) ∨
          (∃ k : ℕ, 1 < k ∧ k ∣ n ∧
            Nonempty (↥(fStarOf (transvGen G₀)) ≃*
              (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) ×
                Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∧
            G41Case2AtExponent n k B G₀)

section as_G_4_9


end as_G_4_9

end CFSG.ASVolI
