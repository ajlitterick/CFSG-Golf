module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortModel

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Param

variable {K : Type*} [Group K] {X : Type} [Group X] {k : Type*} [Field k]

structure SimpleParam (D : UniversalRootDatum K) (k : Type*) [Field k]
    (x : (Fin D.rank → ℤ) → k → K) : Prop where
  param : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
    D.rootGroup x
  inj_central : ∀ {X : Type} [Group X] (ψ : K →* X), ψ.ker ≤ Subgroup.center K →
    ∀ (g : K) (i : Fin D.rank) (c : k), ψ (g * x (Pi.single i 1) c * g⁻¹) = 1 → c = 0

variable {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}

theorem SimpleParam.of_chevalleyExtras
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hX : ChevalleyExtras D k x C O) : SimpleParam D k x :=
  ⟨hX.param, fun _ hker g i c h => eq_zero_of_ker_le_center_simple hX hker g i c h⟩

theorem SimpleParam.rankOneImage_eq_pairGroup (hP : SimpleParam D k x) (ψ : K →* X) (g : K)
    (i : Fin D.rank) :
    rankOneImage D ψ g (Pi.single i 1) =
      pairGroup (fun c => ψ (g * x (Pi.single i 1) c * g⁻¹))
        (fun c => ψ (g * x (-Pi.single i 1) c * g⁻¹)) := by
  have hγ : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots D i
  have hγ' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ
  have h1 : (D.rootGroup (Pi.single i 1) : Set K) = Set.range (x (Pi.single i 1)) := by
    ext y
    exact (hP.param _ hγ).1 y
  have h2 : (D.rootGroup (-Pi.single i 1) : Set K) = Set.range (x (-Pi.single i 1)) := by
    ext y
    exact (hP.param _ hγ').1 y
  have h3 : D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) =
      Subgroup.closure (Set.range (x (Pi.single i 1)) ∪ Set.range (x (-Pi.single i 1))) := by
    rw [Subgroup.closure_union, ← h1, ← h2, Subgroup.closure_eq, Subgroup.closure_eq]
  unfold rankOneImage rankOneRoot pairGroup
  rw [h3, Subgroup.map_map, MonoidHom.map_closure, Set.image_union, ← Set.range_comp,
    ← Set.range_comp]
  rfl

theorem SimpleParam.map_conj_x_add (hP : SimpleParam D k x) (ψ : K →* X) (g : K) (i : Fin D.rank)
    (c d : k) :
    ψ (g * x (Pi.single i 1) (c + d) * g⁻¹) =
      ψ (g * x (Pi.single i 1) c * g⁻¹) * ψ (g * x (Pi.single i 1) d * g⁻¹) := by
  rw [(hP.param _ (single_mem_roots D i)).2.1, ← map_mul]
  congr 1
  group


theorem SimpleParam.indexTwoCentralizes_rankOneImage_simple (hP : SimpleParam D k x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {Ē : Subgroup X}
    (hĒ2 : ∀ y ∈ Ē, y * y = 1)
    (hdiag : ∀ e ∈ Ē, ∃ a : kˣ, ActsDiagonallyOnSimple x ψ g i e a) :
    IndexTwoCentralizes Ē (rankOneImage D ψ g (Pi.single i 1)) := by
  rw [hP.rankOneImage_eq_pairGroup ψ g i]
  exact indexTwoCentralizes_pairGroup_of_scalar hĒ2
    (fun c d => hP.map_conj_x_add ψ g i c d) (fun c h => hP.inj_central ψ hker g i c h) hdiag

theorem SimpleParam.eq_one_of_centralizes_actsDiagonallyOnSimple (hP : SimpleParam D k x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a)
    (hc : ∀ r ∈ rankOneImage D ψ g (Pi.single i 1), e * r = r * e) : a = 1 := by
  have hmem : ψ (g * x (Pi.single i 1) 1 * g⁻¹) ∈ rankOneImage D ψ g (Pi.single i 1) := by
    rw [hP.rankOneImage_eq_pairGroup ψ g i]
    exact Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have h1 := hc _ hmem
  have hh : e * ψ (g * x (Pi.single i 1) 1 * g⁻¹) * e⁻¹ =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := he.1 1
  have h2 : ψ (g * x (Pi.single i 1) 1 * g⁻¹) =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := by
    rw [← hh, eq_comm, mul_inv_eq_iff_eq_mul]
    exact h1
  have h3 : ψ (g * x (Pi.single i 1) ((a : k) * 1 - 1) * g⁻¹) = 1 := by
    have h4 := hP.map_conj_x_add ψ g i ((a : k) * 1 - 1) 1
    rw [sub_add_cancel, ← h2] at h4
    exact mul_eq_right.mp h4.symm
  have h5 := hP.inj_central ψ hker g i _ h3
  have h6 : (a : k) = 1 := by linear_combination h5
  exact Units.ext (by rw [h6, Units.val_one])


end Param

section Provider


end Provider

end CFSG.ClassicalInvolution.Balance
