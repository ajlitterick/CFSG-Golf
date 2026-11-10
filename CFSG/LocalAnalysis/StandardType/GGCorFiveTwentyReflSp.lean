module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut fieldSp fieldAut_proj
  coe_fieldSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace ReflSp

variable {K : Type} [Field K] {m : ℕ}


theorem exists_ringEquiv_eq_pow {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ}
    (hζo : orderOf ζ = p) : ∃ c < p, σ (ζ : K) = (ζ : K) ^ c := by
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  have h1 : (σ (ζ : K)) ^ p = 1 := by rw [← map_pow, hprim.pow_eq_one, map_one]
  obtain ⟨c, hc, hc'⟩ := hprim.eq_pow_of_pow_eq_one h1
  exact ⟨c, hc, hc'.symm⟩

theorem ringEquiv_units_pow (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c)
    (k : ℕ) : σ ((ζ ^ k : Kˣ) : K) = ((ζ ^ k : Kˣ) : K) ^ c := by
  rw [Units.val_pow_eq_pow_val, map_pow, hc, ← pow_mul, ← pow_mul, mul_comm]

theorem ringEquiv_units_inv_pow (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c)
    (k : ℕ) : σ (((ζ ^ k)⁻¹ : Kˣ) : K) = (((ζ ^ k)⁻¹ : Kˣ) : K) ^ c := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, ringEquiv_units_pow σ hc, inv_pow]

theorem fieldSp_spTorusSp {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hζ : ζ ^ p = 1)
    (hc : σ (ζ : K) = (ζ : K) ^ c) (f : Fin m → Multiplicative (ZMod p)) :
    fieldSp m K σ (spTorusSp hζ f) = spTorusSp hζ f ^ c := by
  apply Subtype.ext
  apply Units.ext
  change ((spTorusGL hζ f : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
    (((spTorusSp hζ f ^ c : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, spTorusSp_coe, spTorusGL_apply,
    TauCeti.diagGL_coe, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_pow]
  congr 1
  funext x
  rcases x with i | i
  · simp only [Pi.pow_apply, pairedUnits, Sum.elim_inl, zmodPowHom_apply]
    exact ringEquiv_units_pow σ hc _
  · simp only [Pi.pow_apply, pairedUnits, Sum.elim_inr, zmodPowHom_apply]
    exact ringEquiv_units_inv_pow σ hc _

theorem fieldAut_spTorus {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hζ : ζ ^ p = 1)
    (hc : σ (ζ : K) = (ζ : K) ^ c) (f : Fin m → Multiplicative (ZMod p)) :
    (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) (spTorus hζ f) =
      spTorus hζ f ^ c := by
  rw [spTorus, MonoidHom.comp_apply, ← map_pow]
  exact (fieldAut_proj (r := m) (K := K) σ (spTorusSp hζ f)).trans
    (congrArg (proj m K) (fieldSp_spTorusSp σ hζ hc f))

theorem exists_ne_zero_col {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) (x : ι) :
    ∃ y, (g : Matrix ι ι K) y x ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := congrFun (congrFun g.inv_mul x) x
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp [h] at h1

theorem zmodPowHom_injective {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) : Function.Injective (zmodPowHom hζ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact (zmodPowHom_eq_one_iff hζ hζo).mp ha

theorem pairedUnits_eq_of_mul_eq {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) {g : GL (Fin m ⊕ Fin m) K}
    {f f' : Fin m → Multiplicative (ZMod p)} (h : g * spTorusGL hζ f = spTorusGL hζ f' * g)
    {x y : Fin m ⊕ Fin m} (hxy : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x ≠ 0) :
    pairedUnits (fun i => zmodPowHom hζ (f i)) x =
      pairedUnits (fun i => zmodPowHom hζ (f' i)) y := by
  have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x) h
  simp only [Units.val_mul, spTorusGL_apply, TauCeti.diagGL_coe, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at e
  apply Units.ext
  rw [mul_comm] at e
  exact mul_right_cancel₀ hxy e

theorem exists_monomial_data {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (g : GL (Fin m ⊕ Fin m) K) :
    ∃ (j : Fin m → Fin m) (ε : Fin m → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f' : Fin m → Multiplicative (ZMod p), g * spTorusGL hζ f = spTorusGL hζ f' * g →
        ∀ i, Multiplicative.toAdd (f' (j i)) = ε i * Multiplicative.toAdd (f i) := by
  have key : ∀ i : Fin m, ∃ j : Fin m, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
      ∀ f f' : Fin m → Multiplicative (ZMod p), g * spTorusGL hζ f = spTorusGL hζ f' * g →
        Multiplicative.toAdd (f' j) = ε * Multiplicative.toAdd (f i) := by
    intro i
    obtain ⟨y, hy⟩ := exists_ne_zero_col g (Sum.inl i)
    rcases y with j | j
    · refine ⟨j, 1, Or.inl rfl, fun f f' h => ?_⟩
      have e := pairedUnits_eq_of_mul_eq hζ h hy
      simp only [pairedUnits, Sum.elim_inl] at e
      rw [one_mul, zmodPowHom_injective hζ hζo e]
    · refine ⟨j, -1, Or.inr rfl, fun f f' h => ?_⟩
      have e := pairedUnits_eq_of_mul_eq hζ h hy
      simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr] at e
      rw [← map_inv] at e
      rw [zmodPowHom_injective hζ hζo e, toAdd_inv, neg_one_mul, neg_neg]
  choose j ε hε hj using key
  exact ⟨j, ε, hε, fun f f' h i => hj i f f' h⟩


section Finite

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_orderOf_eq {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p := by
  have := Fact.mk hp
  exact exists_orderOf_eq_of_dvd hpq

theorem exists_eq_conj_fieldAut (hm3 : 3 ≤ m) (β' : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :
    ∃ (s : LargeEvenProj (LargeEvenSpGroup K m))
      (φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))),
      (∃ σ : K ≃+* K, φ = fieldAut m K σ) ∧ ∀ y, β' y = s * φ y * s⁻¹ := by
  obtain ⟨_, ⟨s, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := AutPSp.exists_mul_compl (K := K) hm3 β'
  exact ⟨s, fieldAut m K σ, ⟨σ, rfl⟩, fun y => rfl⟩

theorem exists_conj_spTorus [NeZero m] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hE : IsElemAbelian p E)
    (hcard : p ^ m ≤ Nat.card E) :
    ∃ x : LargeEvenProj (LargeEvenSpGroup K m), (∀ f, x * spTorus hζ f * x⁻¹ ∈ E) ∧
      ∀ e ∈ E, ∃ f, x * spTorus hζ f * x⁻¹ = e := by
  have := Fact.mk hp
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Subgroup (LargeEvenSpGroup K m),
      E₁ = E.comap (LargeEvenProjMk _) := ⟨_, rfl⟩
  have hmemE₁ : ∀ g, g ∈ E₁ ↔ LargeEvenProjMk _ g ∈ E := fun g => by
    rw [hE₁]
    rfl
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Subgroup (GL (Fin m ⊕ Fin m) K),
      E₂ = E₁.map (LargeEvenSpGroup K m).subtype := ⟨_, rfl⟩
  have hE₁ab : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hπi ?_)⟩⟩, fun a ha => hπi ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE ((hmemE₁ _).mp a.2) ((hmemE₁ _).mp b.2)
    · rw [map_pow, map_one]
      exact hE.2 _ ((hmemE₁ _).mp ha)
  have hcard₁ : Nat.card E₁ = Nat.card E := by
    have h1 : E₁.map (LargeEvenProjMk _) = E := by
      rw [hE₁]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
    rw [Nat.card_congr (E₁.equivMapOfInjective _ hπi).toEquiv, h1]
  have hcard₂ : Nat.card E₂ = Nat.card E := by
    rw [hE₂]
    exact (Nat.card_congr (E₁.equivMapOfInjective _
      (LargeEvenSpGroup K m).subtype_injective).toEquiv).symm.trans hcard₁
  obtain ⟨P, hP, hPE⟩ := exists_conj_eq_range_spTorusGL (m := m) (E := E₂) hp2
    (natCast_ne_zero_of_charTwo hp hp2) hζo hζ (by rw [hE₂]; exact Subgroup.map_subtype_le E₁)
    (by rw [hE₂]; exact TableB.isElemAbelian_map hE₁ab _) (by rw [hcard₂]; exact hcard)
  obtain ⟨P', hP'⟩ : ∃ P' : LargeEvenSpGroup K m, (P' : GL (Fin m ⊕ Fin m) K) = P :=
    ⟨⟨P, hP⟩, rfl⟩
  have hconj : ∀ f, LargeEvenProjMk _ P' * spTorus hζ f * (LargeEvenProjMk _ P')⁻¹ =
      LargeEvenProjMk _ (P' * spTorusSp hζ f * P'⁻¹) := fun f => by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine ⟨LargeEvenProjMk _ P', fun f => ?_, fun e he => ?_⟩
  · have h1 : spTorusGL hζ f ∈ E₂.map (MulAut.conj P⁻¹).toMonoidHom := by
      rw [hPE]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg₂, hg⟩ := h1
    rw [hE₂] at hg₂
    obtain ⟨g₁, hg₁, rfl⟩ := hg₂
    have h2 : P' * spTorusSp hζ f * P'⁻¹ = g₁ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, hP', ← hg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
      group
    rw [hconj, h2]
    exact (hmemE₁ g₁).mp hg₁
  · obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective _ e
    have hg₁ : g₁ ∈ E₁ := (hmemE₁ g₁).mpr he
    have h1 : (MulAut.conj P⁻¹).toMonoidHom (g₁ : GL (Fin m ⊕ Fin m) K) ∈
        E₂.map (MulAut.conj P⁻¹).toMonoidHom := by
      refine ⟨g₁, ?_, rfl⟩
      rw [hE₂]
      exact ⟨g₁, hg₁, rfl⟩
    rw [hPE] at h1
    obtain ⟨f, hf⟩ := h1
    refine ⟨f, ?_⟩
    rw [hconj]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, hf, hP']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

end Finite


end ReflSp


@[expose] def GGReflSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1


end CFSG.StandardType

end
