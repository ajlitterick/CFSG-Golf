module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit

universe u v w

variable {G : Type u} [Group G]

theorem derived_bound_of_injective {B : Type v} {C : Type w} [Group B] [Group C]
    (f : B →* C) (hf : Function.Injective f) (d : Nat)
    (hC : derivedSeries C d = ⊥) : derivedSeries B d = ⊥ := by
  apply ((derivedSeries B d).map_eq_bot_iff_of_injective hf).mp
  exact le_bot_iff.mp ((map_derivedSeries_le_derivedSeries f d).trans hC.le)

theorem symmetric_second_derived_eq_bot (X : Type v) [Finite X]
    (hX : Nat.card X ≤ 3) : derivedSeries (Equiv.Perm X) 2 = ⊥ := by
  classical
  let _ := Fintype.ofFinite X
  let _ := alternatingGroup.isMulCommutative_of_card_le_three hX
  have hsign : derivedSeries (Equiv.Perm X) 1 ≤ alternatingGroup X :=
    Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm X →* ℤˣ)
  exact le_bot_iff.mp ((Subgroup.commutator_mono hsign hsign).trans_eq
    (Subgroup.commutator_self_eq_bot_iff.mpr inferInstance))


theorem derived_bound_of_kernel_le_range {B : Type v} {C : Type w}
    [Group B] [Group C] (f : B →* G) (g : G →* C) (hfg : g.ker ≤ f.range)
    (d n : Nat) (hB : derivedSeries B d = ⊥) (hC : derivedSeries C n = ⊥) :
    derivedSeries G (n + d) = ⊥ := by
  have hsteps : ∀ m : Nat, derivedSeries G (n + m) ≤ (derivedSeries B m).map f := by
    intro m
    induction m with
    | zero =>
      simpa only [Nat.add_zero, derivedSeries_zero, ← MonoidHom.range_eq_map] using
        ((derivedSeries G n).map_eq_bot_iff.mp
          (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans hC.le))).trans hfg
    | succ m ih => exact Subgroup.commutator_le_map_commutator ih ih
  exact le_bot_iff.mp ((hsteps d).trans_eq (hB ▸ Subgroup.map_bot f))

@[expose] noncomputable def kernelFamilyHom (H : Subgroup G) :
    KernelOuter H →* FamilyOuter H :=
  QuotientGroup.map (kernelInner H) (familyInner H)
    (Subgroup.inclusion (orbitKernel_le_familyStabilizer H)) (fun _ hx => hx)


theorem kernelFamilyHom_injective (H : Subgroup G) :
    Function.Injective (kernelFamilyHom H) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (kernelInner H) x
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff alpha).mpr
  exact (QuotientGroup.eq_one_iff
    (Subgroup.inclusion (orbitKernel_le_familyStabilizer H) alpha)).mp hx

theorem kernelOuter_derived_eq_bot (H : Subgroup G) (d : Nat)
    (hA : derivedSeries (FamilyOuter H) d = ⊥) :
    derivedSeries (KernelOuter H) d = ⊥ :=
  derived_bound_of_injective (kernelFamilyHom H) (kernelFamilyHom_injective H) d hA

@[expose] noncomputable def familyOuterHom (H : Subgroup G) :
    FamilyOuter H →* OuterAutomorphisms.Outer G :=
  QuotientGroup.map (familyInner H) (OuterAutomorphisms.inner G)
    (familyStabilizer H).subtype (fun _ hx => hx)


theorem familyOuterHom_injective (H : Subgroup G) :
    Function.Injective (familyOuterHom H) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (familyInner H) x
  apply Subgroup.mem_bot.mpr
  exact (QuotientGroup.eq_one_iff alpha).mpr ((QuotientGroup.eq_one_iff alpha.val).mp hx)

@[expose] noncomputable def outerOrbitAction (H : Subgroup G) :
    OuterAutomorphisms.Outer G →* Equiv.Perm (FamilyOrbit H) :=
  QuotientGroup.lift (OuterAutomorphisms.inner G) (familyOrbitAction H)
    (inner_le_orbitKernel H)


@[expose] noncomputable def kernelOuterHom (H : Subgroup G) :
    KernelOuter H →* OuterAutomorphisms.Outer G :=
  QuotientGroup.map (kernelInner H) (OuterAutomorphisms.inner G) (orbitKernel H).subtype
    (fun _ hx => hx)


theorem outerOrbitAction_kernel_eq_range (H : Subgroup G) :
    (outerOrbitAction H).ker = (kernelOuterHom H).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (OuterAutomorphisms.inner G) x
    have hkernel : alpha ∈ orbitKernel H := hx
    exact ⟨(QuotientGroup.mk' (kernelInner H)) ⟨alpha, hkernel⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (kernelInner H) y
    exact alpha.property


end CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
