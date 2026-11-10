module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Fact

variable {K : Type*} [Group K] {k : Type*} [Field k]


@[expose] def ToralShortRootFact (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → k → K)
    (𝒯 : Set K) : Prop :=
  ∀ t ∈ 𝒯, (∀ i, ∃ b : kˣ, ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b) ∧
    ∀ i (b : kˣ), ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b → b = 1 →
      ∃ Q₀ : Subgroup K, rankOne D.rootGroup i ≤ Q₀ ∧
        IsComponentOf Q₀ (Subgroup.centralizer ({t} : Set K))

end Fact

section Transport

variable {K : Type*} [Group K] {X : Type*} [Group X] {k : Type*} [Field k]
  {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}


theorem eq_one_of_centralizes_actsDiagonallyOnSimple (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a)
    (hc : ∀ r ∈ rankOneImage D ψ g (Pi.single i 1), e * r = r * e) : a = 1 := by
  have hmem : ψ (g * x (Pi.single i 1) 1 * g⁻¹) ∈ rankOneImage D ψ g (Pi.single i 1) := by
    rw [rankOneImage_eq_pairGroup hX ψ g (single_mem_roots D i)]
    exact Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have h1 := hc _ hmem
  have hh : e * ψ (g * x (Pi.single i 1) 1 * g⁻¹) * e⁻¹ =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := he.1 1
  have h2 : ψ (g * x (Pi.single i 1) 1 * g⁻¹) =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := by
    rw [← hh, eq_comm, mul_inv_eq_iff_eq_mul]
    exact h1
  have h3 : ψ (g * x (Pi.single i 1) ((a : k) * 1 - 1) * g⁻¹) = 1 := by
    have h4 := map_conj_x_add hX ψ g (single_mem_roots D i) ((a : k) * 1 - 1) 1
    rw [sub_add_cancel, ← h2] at h4
    exact mul_eq_right.mp h4.symm
  have h5 := eq_zero_of_ker_le_center_simple hX hker g i _ h3
  have h6 : (a : k) = 1 := by linear_combination h5
  exact Units.ext (by rw [h6, Units.val_one])


theorem fixedGroup_conj_eq_centralizer (t : K) :
    fixedGroup (MulAut.conj t) = Subgroup.centralizer ({t} : Set K) := by
  ext y
  rw [mem_fixedGroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem actsDiagonallyOnSimple_of_actsAsConj (ψ : K →* X) (g : K) (e : X) {t : K}
    (hconj : ∀ y : K, e * ψ y * e⁻¹ = ψ (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) {j : Fin D.rank}
    {a : kˣ} (ha : ActsDiagonallyOnSimple x (MonoidHom.id K) 1 j t a) :
    ActsDiagonallyOnSimple x ψ g j e a := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [hconj]
    have h := ha.1 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]
  · rw [hconj]
    have h := ha.2 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (-Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (-Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]

theorem inComponentOfCentralizer_of_toralShortRootFact {𝒯 : Set K}
    (hfact : ToralShortRootFact D x 𝒯) {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K)
    {t : K} (ht : t ∈ 𝒯) {e : X}
    (he : ∀ y : K, e * ψ y * e⁻¹ = ψ (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) {i : Fin D.rank}
    {b : kˣ} (hb : ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b) (hb1 : b = 1) :
    InComponentOfCentralizer ψ.range (rankOneImage D ψ g (Pi.single i 1)) e := by
  obtain ⟨Q₀, hRQ, hQ⟩ := (hfact t ht).2 i b hb hb1
  have hδ : ∀ y : K, e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * MulAut.conj t y * g⁻¹) := by
    intro y
    rw [he]
    congr 1
    simp only [MulAut.conj_apply]
    group
  rw [← fixedGroup_conj_eq_centralizer] at hQ
  rw [rankOneImage_eq_map ψ g (Pi.single i 1)]
  exact inComponentOfCentralizer_of_fixedGroup hker g e (MulAut.conj t) hδ hQ hRQ

end Transport

section Provider


end Provider

end CFSG.ClassicalInvolution.Balance
