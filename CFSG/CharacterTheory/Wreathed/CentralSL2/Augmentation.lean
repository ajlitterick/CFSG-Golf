module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.AugmentationValues
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SumZero

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Augmentation

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Field F] [Finite F] in
theorem card_omega [Finite F] : Nat.card (Omega F) = Nat.card F + 1 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]

theorem fixedPointCount_eq_card_iff (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h =
        (Nat.card F + 1 : ℂ) ↔ h ∈ (semilinearAction F b m hm heven Sigma hSigma).ker := by
  rw [fixedPointCount_semilinear, MonoidHom.mem_ker]
  constructor
  · intro hcount
    refine Equiv.ext fun x => ?_
    by_contra hx
    have hlt := Finite.card_subtype_lt (p := fun y => semilinearAction F b m hm heven Sigma hSigma
      h y = y) hx
    rw [card_omega] at hlt
    have hc : (Nat.card {x // semilinearAction F b m hm heven Sigma hSigma h x = x} : ℂ) =
        ((Nat.card F + 1 : ℕ) : ℂ) := by push_cast; exact hcount
    exact absurd (Nat.cast_injective hc) hlt.ne
  · intro h1
    simp only [h1, Equiv.Perm.one_apply]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), card_omega]
    push_cast
    rfl

theorem two_le_card_omega : 2 ≤ Nat.card (Omega F) := by
  rw [card_omega]
  have := Finite.one_lt_card (α := F)
  omega

theorem augmentation_mem_blocksIrr :
    (fun h => fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1) ∈
      BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) := by
  have h2 := semilinearExtension_isMultiplyPretransitive F b m hm heven Sigma hSigma
  have ht : MulAction.IsPretransitive (SemilinearExtension F b m hm heven Sigma hSigma)
      (Omega F) := MulAction.isPretransitive_of_is_two_pretransitive
  have : Fintype F := Fintype.ofFinite F
  exact ((permutation_character_orbit_count (SemilinearExtension F b m hm heven Sigma hSigma)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2

theorem augmentation_restrict_mem_blocksIrr :
    (fun g : matrixLayer F b m hm heven Sigma hSigma =>
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) g - 1) ∈
      BlocksIrr (matrixLayer F b m hm heven Sigma hSigma) := by
  have h2 := matrixLayer_isMultiplyPretransitive F b m hm heven Sigma hSigma
  have ht : MulAction.IsPretransitive (matrixLayer F b m hm heven Sigma hSigma)
      (Omega F) := MulAction.isPretransitive_of_is_two_pretransitive
  have : Fintype F := Fintype.ofFinite F
  have h := ((permutation_character_orbit_count (matrixLayer F b m hm heven Sigma hSigma)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2
  convert h using 2
  rfl

theorem augmentation_one :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) 1 - 1 =
      (Nat.card F : ℂ) := by
  rw [(fixedPointCount_eq_card_iff F b m hm heven Sigma hSigma 1).mpr (Subgroup.one_mem _)]
  ring

end Augmentation

section Twists

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem linearCharacter_matrixLayer (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀)
    (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma))
    (r : Fin m) (s : Fin (Nat.card Sigma)) {g : SemilinearExtension F b m hm heven Sigma hSigma}
    (hg : g ∈ matrixLayer F b m hm heven Sigma hSigma) :
    linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g = 1 := by
  rw [← psi_ker] at hg
  rw [linearCharacter, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hg, map_one]

@[expose] noncomputable def quotientLinearTwist (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) (r : Fin m) (s : Fin (Nat.card Sigma)) :
    SemilinearExtension F b m hm heven Sigma hSigma ⧸ matrixLayer F b m hm heven Sigma hSigma →*
      ℂˣ :=
  QuotientGroup.lift _ (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s)
    (fun _ hg => linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
      r s hg)

theorem quotientLinearTwist_mk (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀)
    (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma))
    (r : Fin m) (s : Fin (Nat.card Sigma)) (g : SemilinearExtension F b m hm heven Sigma hSigma) :
    quotientLinearTwist F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
        (g : SemilinearExtension F b m hm heven Sigma hSigma ⧸
          matrixLayer F b m hm heven Sigma hSigma) =
      linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g :=
  QuotientGroup.lift_mk _ _ _

theorem quotient_isMulCommutative :
    IsMulCommutative (SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) := by
  have hcyc : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  have hcommS : ∀ x y : Sigma, x * y = y * x := fun x y => IsCyclic.commGroup.mul_comm x y
  have hprod : IsMulCommutative (Multiplicative (ZMod m) × Sigma) :=
    ⟨⟨fun x y => Prod.ext (mul_comm _ _) (hcommS _ _)⟩⟩
  exact Function.Surjective.isMulCommutative
    (f := (matrixQuotientEquiv F b m hm heven Sigma hSigma).symm.toMonoidHom)
    (matrixQuotientEquiv F b m hm heven Sigma hSigma).symm.surjective hprod

end Twists


section TwistFamily

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem augmentation_twists (hb1 : b ≠ 1) (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) :
    let St : SemilinearExtension F b m hm heven Sigma hSigma → ℂ := fun h =>
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1
    let Ξ : Fin m → Fin (Nat.card Sigma) → SemilinearExtension F b m hm heven Sigma hSigma → ℂ :=
      fun r s h =>
        (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s h : ℂ) * St h
    (∀ r s, Ξ r s ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
      Ξ r s 1 = Nat.card F) ∧
    Function.Injective (fun rs : Fin m × Fin (Nat.card Sigma) => Ξ rs.1 rs.2) ∧
    (∀ η ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma),
      0 < BlocksInnerProduct (fun g : matrixLayer F b m hm heven Sigma hSigma => η g)
        (fun g : matrixLayer F b m hm heven Sigma hSigma => St g) ↔ ∃ r s, η = Ξ r s) ∧
    (∀ r s, (fun g : matrixLayer F b m hm heven Sigma hSigma => Ξ r s g) =
      fun g : matrixLayer F b m hm heven Sigma hSigma => St g) := by
  intro St Ξ
  obtain ⟨V, i₁, i₂, i₃, ρ, hirr, hρ⟩ := augmentation_mem_blocksIrr F b m hm heven Sigma hSigma
  have hρSt : ρ.character = St := hρ
  have hρM : Representation.IsIrreducible
      (ρ.comp (matrixLayer F b m hm heven Sigma hSigma).subtype) := by
    apply Wreathed.isIrreducible_of_character_mem_blocksIrr
    have hc : Representation.character
        (ρ.comp (matrixLayer F b m hm heven Sigma hSigma).subtype) =
        fun g : matrixLayer F b m hm heven Sigma hSigma => St g := by
      funext g
      exact congrFun hρSt g
    rw [hc]
    exact augmentation_restrict_mem_blocksIrr F b m hm heven Sigma hSigma
  have : IsMulCommutative (SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) :=
    quotient_isMulCommutative F b m hm heven Sigma hSigma
  obtain ⟨hmem, hinj, hiff, -⟩ :=
    Wreathed.irreducible_extension_abelian_quotient_character_twists _ ρ hρM
  set lamt := quotientLinearTwist F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd with hlamt
  have hΞ : ∀ r s, Ξ r s = Wreathed.quotientTwist (matrixLayer F b m hm heven Sigma hSigma)
      ρ.character (lamt r s) := by
    intro r s
    funext h
    change _ * St h = ρ.character h * (lamt r s (h : SemilinearExtension F b m hm heven Sigma
      hSigma ⧸ matrixLayer F b m hm heven Sigma hSigma) : ℂ)
    rw [hlamt, quotientLinearTwist_mk, hρSt, mul_comm]
  have hexh : ∀ lam : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma →* ℂˣ, ∃ r s, lamt r s = lam := by
    intro lam
    obtain ⟨r, s, hrs⟩ := linearCharacter_exhaustive F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
      hζm hζd hb1 (lam.comp (QuotientGroup.mk' _))
    refine ⟨r, s, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun h => ?_)⟩
    change lamt r s (h : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) = _
    rw [hlamt, quotientLinearTwist_mk, hrs]
  refine ⟨fun r s => ⟨by rw [hΞ]; exact hmem _, ?_⟩, ?_, ?_, ?_⟩
  · change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 : ℂ) * St 1 = _
    rw [map_one, Units.val_one, one_mul]
    exact augmentation_one F b m hm heven Sigma hSigma
  · rintro ⟨r, s⟩ ⟨r', s'⟩ h
    have h' : lamt r s = lamt r' s' := by
      apply hinj
      rw [← hΞ, ← hΞ]
      exact h
    apply linearCharacter_values_injective F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
    funext g
    have := congrArg (fun lam : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma →* ℂˣ =>
        (lam (g : SemilinearExtension F b m hm heven Sigma hSigma ⧸
          matrixLayer F b m hm heven Sigma hSigma) : ℂ)) h'
    simp only [hlamt, quotientLinearTwist_mk] at this
    exact this
  · intro η hη
    have hcoe : (fun g : matrixLayer F b m hm heven Sigma hSigma => St g) =
        fun g : matrixLayer F b m hm heven Sigma hSigma => ρ.character g := by
      rw [hρSt]
    rw [hcoe, hiff η hη]
    constructor
    · rintro ⟨lam, rfl⟩
      obtain ⟨r, s, rfl⟩ := hexh lam
      exact ⟨r, s, (hΞ r s).symm⟩
    · rintro ⟨r, s, rfl⟩
      exact ⟨lamt r s, hΞ r s⟩
  · intro r s
    funext g
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g : ℂ) * St g =
      St g
    rw [linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g.2,
      Units.val_one, one_mul]

end TwistFamily


section CommonKernel

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem mem_zpowers_of_orderOf_two {K : Type*} [Group K] {g : K} (hg : orderOf g = 2) (x : K) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, hg]
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with hk | hk
    · left; rw [hk, zpow_zero]
    · right; rw [hk, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

omit [Finite F] in
theorem orderOf_inl_cyclicGenerator_pow_m (h2 : (2 : F) ≠ 0) :
    orderOf (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
      SemilinearExtension F b m hm heven Sigma hSigma) = 2 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]
  apply orderOf_eq_prime
  · rw [← pow_mul]
    exact (cyclicGenerator_pow_eq_one_iff F b m hm heven h2 _).mpr ⟨1, by ring⟩
  · rw [Ne, cyclicGenerator_pow_eq_one_iff F b m hm heven h2]
    intro h
    have := Nat.le_of_dvd hm h
    omega


theorem linearCharacter_inl_cyclicGenerator_pow (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) (r : Fin m) (s : Fin (Nat.card Sigma)) (k : ℕ) :
    (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
      (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ k)) : ℂ) = ζm ^ (r.val * k) := by
  have h := linearCharacter_formula F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 k 0
  rw [pow_zero, mul_zero, pow_zero, mul_one] at h
  rw [← h, cyclicGenerator_pow]
  rfl


end CommonKernel


end CFSG.Wreathed.CentralSL2
