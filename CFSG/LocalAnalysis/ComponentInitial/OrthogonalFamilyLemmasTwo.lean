module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_partner_of_polarNondegOn {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : PolarNondegOn Q W) {e : V} (heW : e ∈ W) (he : Q e = 0) (he0 : e ≠ 0) :
    ∃ f ∈ W, Q f = 0 ∧ polar Q e f = 1 := by
  obtain ⟨v, hvW, hv⟩ := hW.exists_polar_ne_zero heW he0
  have h1 : polar Q e ((polar Q e v)⁻¹ • v) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hv]
  refine ⟨(HypPair.ofPolarEqOne he h1).f, ?_, (HypPair.ofPolarEqOne he h1).Q_f,
    (HypPair.ofPolarEqOne he h1).polar_ef⟩
  rw [HypPair.ofPolarEqOne_f]
  exact W.sub_mem (W.smul_mem _ hvW) (W.smul_mem _ heW)

theorem exists_ne_zero_of_one_le_finrank {T : Submodule K V} (hT : 1 ≤ finrank K T) :
    ∃ x ∈ T, x ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  rw [h, finrank_bot] at hT
  omega

theorem HypPair.orth_of_mem_perp {Q : QuadraticForm K V} {P₁ P₂ : HypPair Q}
    (he : P₂.e ∈ P₁.perp) (hf : P₂.f ∈ P₁.perp) : P₁.Orth P₂ := by
  rw [HypPair.mem_perp] at he hf
  exact ⟨he.1, hf.1, he.2, hf.2⟩

theorem HypPair.mem_perp_of_polar {Q : QuadraticForm K V} {P : HypPair Q} {x : V}
    (h : polar Q x P.e = 0 ∧ polar Q x P.f = 0) : x ∈ P.perp := by
  rw [HypPair.mem_perp, polar_comm Q P.e, polar_comm Q P.f]
  exact h

section HyperbolicPairs

variable [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem quadratic_two_hyperbolic_pairs (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) {e₁ : V} (he₁ : Q e₁ = 0)
    (he₁0 : e₁ ≠ 0) : ∃ P₁ P₂ : HypPair Q, P₁.e = e₁ ∧ P₁.Orth P₂ := by
  obtain ⟨T, hT2, hTs⟩ := hT
  obtain ⟨P₁, rfl⟩ := exists_hypPair hQ he₁ he₁0
  obtain ⟨T', hT'p, hT's, hT'd, -⟩ :=
    quadratic_singular_subspace_descent Q P₁.Q_e P₁.polar_ef T hTs hT2
  obtain ⟨e₂, he₂, he₂0⟩ := exists_ne_zero_of_one_le_finrank (T := T') (by omega)
  have he₂W : e₂ ∈ P₁.perp := HypPair.mem_perp_of_polar (hT'p e₂ he₂)
  obtain ⟨f₂, hf₂W, hf₂, he₂f₂⟩ := exists_partner_of_polarNondegOn
    (HypPair.polarNondegOn_perp hQ P₁) he₂W (hT's e₂ he₂) he₂0
  let P₂ : HypPair Q := ⟨e₂, f₂, hT's e₂ he₂, hf₂, he₂f₂⟩
  exact ⟨P₁, P₂, rfl, HypPair.orth_of_mem_perp he₂W hf₂W⟩

theorem quadratic_three_hyperbolic_pairs (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {e₁ : V} (he₁ : Q e₁ = 0)
    (he₁0 : e₁ ≠ 0) :
    ∃ P₁ P₂ P₃ : HypPair Q, P₁.e = e₁ ∧ P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, rfl⟩ := exists_hypPair hQ he₁ he₁0
  have hW₁ := HypPair.polarNondegOn_perp hQ P₁
  obtain ⟨T', hT'p, hT's, hT'd, -⟩ :=
    quadratic_singular_subspace_descent Q P₁.Q_e P₁.polar_ef T hTs hT3
  have hT'W : T' ≤ P₁.perp := fun x hx => HypPair.mem_perp_of_polar (hT'p x hx)
  obtain ⟨e₂, he₂, he₂0⟩ := exists_ne_zero_of_one_le_finrank (T := T') (by omega)
  have he₂W : e₂ ∈ P₁.perp := hT'W he₂
  obtain ⟨f₂, hf₂W, hf₂, he₂f₂⟩ := exists_partner_of_polarNondegOn hW₁ he₂W (hT's e₂ he₂) he₂0
  let P₂ : HypPair Q := ⟨e₂, f₂, hT's e₂ he₂, hf₂, he₂f₂⟩
  obtain ⟨T'', hT''p, hT''s, hT''d, hT''le⟩ :=
    quadratic_singular_subspace_descent Q P₂.Q_e P₂.polar_ef T' hT's rfl
  obtain ⟨e₃, he₃, he₃0⟩ := exists_ne_zero_of_one_le_finrank (T := T'') (by omega)
  have he₃W₁ : e₃ ∈ P₁.perp := by
    have h := hT''le he₃
    have hle : T' ⊔ Submodule.span K {P₂.e} ≤ P₁.perp :=
      sup_le hT'W ((Submodule.span_singleton_le_iff_mem _ _).2 he₂W)
    exact hle h
  have he₃W : e₃ ∈ P₁.perp ⊓ P₂.perp := ⟨he₃W₁, HypPair.mem_perp_of_polar (hT''p e₃ he₃)⟩
  obtain ⟨f₃, hf₃W, hf₃, he₃f₃⟩ := exists_partner_of_polarNondegOn
    (hW₁.inf_perp P₂ he₂W hf₂W) he₃W (hT''s e₃ he₃) he₃0
  let P₃ : HypPair Q := ⟨e₃, f₃, hT''s e₃ he₃, hf₃, he₃f₃⟩
  exact ⟨P₁, P₂, P₃, rfl, HypPair.orth_of_mem_perp he₂W hf₂W,
    HypPair.orth_of_mem_perp he₃W.1 hf₃W.1, HypPair.orth_of_mem_perp he₃W.2 hf₃W.2⟩

end HyperbolicPairs

section CoordinateLines

variable {Q : QuadraticForm K V}

@[expose] def hypPairSwap (P : HypPair Q) : HypPair Q :=
  ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩


end CoordinateLines

section CharTwoPlane

variable {Q : QuadraticForm K V}

theorem orthogonal_char_two_plane_vector_stabilizer [CharP K 2] (hdim : finrank K V = 2)
    (hQ : (polarBilin Q).Nondegenerate) {x : V} (hx : Q x ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgx : g x = x) :
    g = 1 ∨ g = reflect Q x := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hxx : polar Q x x = 0 := by
    rw [polar_self_eq_two_mul, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul]
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hx0
  obtain ⟨y, hxy⟩ : ∃ y, polar Q x y = 1 :=
    ⟨(polar Q x v)⁻¹ • v, by rw [polar_smul_right_eq, inv_mul_cancel₀ hv]⟩
  have hyx : polar Q y x = 1 := by rw [polar_comm, hxy]
  have hli : LinearIndependent K ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q x) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy, polar_zero_right]
      at h1
    have ht : t = 0 := by simpa using h1
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hx0, ht⟩
  have hspan : Submodule.span K (Set.range ![x, y]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  have hdec : ∀ z : V, ∃ α β : K, z = α • x + β • y := fun z => by
    have hz : z ∈ Submodule.span K (Set.range ![x, y]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hz
    exact ⟨c 0, c 1, by rw [← hc, Fin.sum_univ_two]; rfl⟩
  have hext : ∀ h : V ≃ₗ[K] V, h x = g x → h y = g y → h = g := fun h h1 h2 =>
    LinearEquiv.ext fun z => by
      obtain ⟨α, β, rfl⟩ := hdec z
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, h2]
  have hgy : ∃ c : K, g y = y + c • x := by
    obtain ⟨α, β, hαβ⟩ := hdec (g y - y)
    have h1 : polar Q x (g y - y) = 0 := by
      rw [polar_sub_right, ← hgx, polar_map_of_mem hg, hgx, sub_self]
    rw [hαβ, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy] at h1
    have hβ : β = 0 := by simpa using h1
    exact ⟨α, by rw [← sub_eq_iff_eq_add', hαβ, hβ, zero_smul, add_zero]⟩
  obtain ⟨c, hc⟩ := hgy
  have hQy : c * (c * Q x + 1) = 0 := by
    have h := map_of_mem hg y
    rw [hc, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, hyx] at h
    linear_combination h
  rcases mul_eq_zero.1 hQy with h0 | h1
  · left
    refine (hext 1 ?_ ?_).symm
    · rw [hgx]
      rfl
    · rw [hc, h0, zero_smul, add_zero]
      rfl
  · right
    have hc' : c = -(Q x)⁻¹ := by
      field_simp
      linear_combination h1
    refine (hext (reflect Q x) ?_ ?_).symm
    · rw [hgx, reflect_apply hx, hxx, zero_div, zero_smul, sub_zero]
    · rw [hc, reflect_apply hx, hxy, hc', neg_smul, ← sub_eq_add_neg, one_div]

end CharTwoPlane

section Anisotropic


end Anisotropic

end CFSG.LocalAnalysis.ComponentInitial
