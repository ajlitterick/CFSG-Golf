module

public import CFSG.LocalAnalysis.SteinbergSFOddSymplecticRootCentralizer
public import CFSG.LocalAnalysis.SteinbergSFOddOrthogonalScalarQuotientSL2
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace OddUnitaryRoot

section Lift

open CatalogueBFixedCentralQuotient


end Lift

section Inner

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem half_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    {W F : Submodule E V} (hWs : (B.domRestrict₁₂ W W).IsSymm)
    (hWl : (B.domRestrict₁₂ W W).SeparatingLeft) (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    {Y : Subgroup (sesqUnitaryGroup B)} (hYF : ∀ y ∈ Y, ∀ w ∈ F, unitaryOp y w = w)
    (ρ : Y →* sesqUnitaryGroup (B.domRestrict₁₂ W W)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range) (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hWs hWl
  obtain ⟨hdim2, -, hρeq⟩ := eq_unitarySpecial_of_isComponent h hp hW1 hWs hWl hρc
  have hA : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr fun a ha =>
    Subtype.ext (eq_one_of_mem_sesqNormOneScalars (hAZ a ha) hF0 (hYF a a.2))
  obtain ⟨eU⟩ := OddClassSelector.nonempty_unitarySpecial_equiv h (B.domRestrict₁₂ W W)
  let ι : Y ≃* CatalogueBUnitaryIsometry.specialIsometry
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq)
      (B.domRestrict₁₂ W W) :=
    (MonoidHom.ofInjective hρi).trans ((MulEquiv.subgroupCongr hρeq).trans eU)
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hbot : A.map ι.toMonoidHom = ⊥ := by rw [hA, Subgroup.map_bot]
  obtain ⟨-, -, -, hcard, -⟩ := SteinbergBT.unitary_scalar_quotient_SL2 hp h.one_le
    h.card_eq_sq (B.domRestrict₁₂ W W) hWs hnd hdim2 hn K hK (A.map ι.toMonoidHom)
    (fun g hg => ⟨1, fun v => by
      rw [hbot, Subgroup.mem_bot] at hg
      rw [hg, one_smul]
      rfl⟩) eQ'
  rw [hbot, Subgroup.card_bot] at hcard
  omega

theorem inner_case_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn : 3 ≤ finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  rcases hN with hN | hN
  ·
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
      ⟨fun x y => hB.eq (x : V) (y : V)⟩
    rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        (isComponent_map_of_isComponent e hY₁) with h2 | h1
    · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine half_false h hp (hsymm _) hsepP (Submodule.one_le_finrank_iff.mpr hP) hM hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ A hAZ hn2 hK eQ
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
        OddClassSelector.restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine half_false h hp (hsymm _) hsepM (Submodule.one_le_finrank_iff.mpr hM) hP hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ A hAZ hn2 hK eQ
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -, -, hscal⟩ := hpaired hN
    obtain ⟨bP⟩ : Nonempty (Basis (Fin (finrank E (eigenPlus l (unitaryOp T)))) E
        (eigenPlus l (unitaryOp T))) := ⟨Module.finBasis E _⟩
    let Fm : centralizer ({T} : Set (sesqUnitaryGroup B)) ≃*
        GL (Fin (finrank E (eigenPlus l (unitaryOp T)))) E :=
      e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hq3 : 3 ≤ p ^ f := by
      have := h.prime.two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
      omega
    have hodd : Odd (Nat.card E) := by
      rw [h.card_eq_sq]
      exact ((h.prime.odd_of_ne_two hp).pow).pow
    obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
    have hA₁ : ∀ a ∈ A.map eY.symm.toMonoidHom, ∃ c : E,
        ((Fm a : GL (Fin (finrank E (eigenPlus l (unitaryOp T)))) E) :
          Matrix (Fin (finrank E (eigenPlus l (unitaryOp T))))
            (Fin (finrank E (eigenPlus l (unitaryOp T)))) E) = c • 1 := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨c, -, hc⟩ := (hscal (eY.symm a)).mp (hAZ a ha)
      refine ⟨c, ?_⟩
      change LinearMap.toMatrixAlgEquiv bP ((e (eY.symm a) : LinearMap.GeneralLinearGroup E
        (eigenPlus l (unitaryOp T))) : Module.End E (eigenPlus l (unitaryOp T))) = c • 1
      rw [hc, map_smul, map_one]
    obtain ⟨-, h5, -⟩ := gl_component_quotient hodd (by omega) Fm hY₁ _ hA₁ hn2 hK eQ₁
    rw [h.card_eq_sq] at h5
    nlinarith

end Inner

section Anti


theorem map_eq_one_of_perfect {U : Type*} [Group U] {C : Subgroup U} {H : Type*} [Group H]
    (Ψ : C ≃* H) {M : Type*} [CommGroup M] (δ : U →* M) {T : Subgroup H}
    (hT : Group.IsPerfect T) (x : T) : δ (Ψ.symm x : C) = 1 := by
  have h1 : x ∈ commutator T := by rw [hT.commutator_eq_top]; exact mem_top x
  exact Abelianization.commutator_subset_ker
    (δ.comp (C.subtype.comp (Ψ.symm.toMonoidHom.comp T.subtype))) h1


theorem sp_branch {U : Type*} [Group U] {Z C : Subgroup U} {k : Type} [Field k] [Finite k]
    (hk : Odd (Nat.card k)) {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {B' : LinearMap.BilinForm k W} (halt : B'.IsAlt) (hnd : B'.Nondegenerate)
    (hdim : 3 ≤ finrank k W) (Ψ : C ≃* CatalogueBAlternatingIsometry.isometryGroup B')
    (hZ : ∀ g : C, (g : U) ∈ Z → ∃ c : k, ∀ w,
      ((Ψ g : CatalogueBAlternatingIsometry.isometryGroup B') : W ≃ₗ[k] W) w = c • w)
    {Y : Subgroup U} (hY : CFSG.Assembly.IsComponentOf Y C) (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : U) ∈ Z) {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf C ≃* Y := Subgroup.subgroupOfEquivOfLe hY.1
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
  obtain ⟨hdim2, -, -⟩ := sp_component_quotient hk halt hnd (by omega) Ψ hY₁
    (A.map eY.symm.toMonoidHom) (by rintro _ ⟨a, ha, rfl⟩; exact hZ (eY.symm a) (hAZ a ha))
    hn2 hK eQ₁
  omega

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem exists_smul_of_restrict {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    {W : Submodule h.fixedField V} {C : Subgroup (sesqUnitaryGroup B)}
    {G : Subgroup (W ≃ₗ[h.fixedField] W)} (Ψ : C ≃* G)
    (hΨ : ∀ g w, ((((Ψ g : G) : W ≃ₗ[h.fixedField] W) w : W) : V) =
      unitaryOp (g : sesqUnitaryGroup B) w) (g : C)
    (hg : unitaryOp (g : sesqUnitaryGroup B) = 1 ∨ unitaryOp (g : sesqUnitaryGroup B) = -1) :
    ∃ c : h.fixedFieldˣ, ∀ w, ((Ψ g : G) : W ≃ₗ[h.fixedField] W) w = (c : h.fixedField) • w := by
  rcases hg with hg | hg
  · refine ⟨1, fun w => Subtype.ext ?_⟩
    rw [hΨ, hg, Units.val_one, one_smul]
    rfl
  · refine ⟨-1, fun w => Subtype.ext ?_⟩
    rw [hΨ, hg, Units.val_neg, Units.val_one, neg_one_smul, Submodule.coe_neg]
    rfl


theorem symmetric_descent (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 1 ≤ finrank E V) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀H : ∀ v w, Hf (τ₀ v) (τ₀ w) = h.bar (Hf v w)) (hsq : ∀ v, τ₀ (τ₀ v) = v) :
    finrank h.fixedField (conjFixed h τ₀) = finrank E V ∧
      Function.Bijective (LinearMap.liftBaseChange E (conjFixed h τ₀).subtype) ∧
      ∃ Bf : LinearMap.BilinForm h.fixedField (conjFixed h τ₀),
        (∀ v w, (Bf v w : E) = Hf v w) ∧ Bf.IsSymm ∧ Bf.Nondegenerate ∧
        ∃ Φ : commutingUnitary Hf τ₀ ≃* TauCeti.BilinForm.isometryGroup Bf,
          ∀ g w, (((Φ g : conjFixed h τ₀ ≃ₗ[h.fixedField] conjFixed h τ₀) w : conjFixed h τ₀) :
            V) = ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w := by
  obtain ⟨-, -, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp) hn hH hnd τ₀ hτ₀ hτ₀H 1 fun v => by
      rw [hsq, Units.val_one, one_smul]
  obtain ⟨-, hfin, hbij, hB1, -⟩ := hall 1 t (by simp [UnitaryFieldData.norm]) ht
  have h1 : ((1 : Eˣ) : E) • τ₀ = τ₀ := by rw [Units.val_one, one_smul]
  rw [h1] at hfin hbij hB1
  exact ⟨hfin, hbij, hB1 rfl⟩

end Anti

section Model

open Matrix


end Model

end OddUnitaryRoot


end CFSG.LocalAnalysis.SymplecticFourStandard
