module

public import CFSG.LieType.Chevalley.E7Three.Multiplicity
public import CFSG.LieType.Chevalley.E7Three.CoordinateActions

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.FourCube

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SectionRank
  CFSG.RankThree.PartOne.KA5L
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.Multiplicity
  CFSG.LieType.Chevalley.E7Three.CoordinateActions

abbrev Four := D × Multiplicative (ZMod 3)

variable {K : Type} [Field K] [CharP K 2]

theorem scalar_multiplicity_commute (ζ : Kˣ) :
    Commute (scalarWord ζ) (multiplicityWord ζ) := by
  rw [scalarWord, multiplicityWord]
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  exact torusElement_commute i j _ _

theorem paired_multiplicity_commute (ζ : Kˣ) :
    Commute (pairedWord ζ) (multiplicityWord ζ) := by
  rw [pairedWord, multiplicityWord]
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  exact torusElement_commute i j _ _

theorem cyclic_multiplicity_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Commute (cyclic (K := K)) (multiplicityWord ζ) := by
  change cyclic * multiplicityWord ζ = multiplicityWord ζ * cyclic
  apply Subtype.ext
  change (cyclic (K := K) : ModGL .E7 K) * (multiplicityWord ζ : ModGL .E7 K) =
    (multiplicityWord ζ : ModGL .E7 K) * (cyclic (K := K) : ModGL .E7 K)
  rw [multiplicityWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) =
    rootDiagUnit .E7 (cubeChar ζ multiplicityExp) * canonicalRep (coxeterSystem .E7) K gamma
  exact mul_inv_eq_iff_eq_mul.mp (gamma_conj_multiplicity ζ hζ)

@[expose] def fourthHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (ZMod 3) →* adjointGroup .E7 K :=
  zmodPowHom (multiplicityWord ζ) (multiplicityWord_pow_three ζ hζ)

theorem cube_fourth_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (f : D)
    (t : Multiplicative (ZMod 3)) : Commute (cubeHom ζ hζ f) (fourthHom ζ hζ t) := by
  rw [cubeHom_apply]
  change Commute
    (scalarWord ζ ^ (Multiplicative.toAdd (f 0)).val *
      pairedWord ζ ^ (Multiplicative.toAdd (f 1)).val *
      (cyclic (K := K)) ^ (Multiplicative.toAdd (f 2)).val)
    (multiplicityWord ζ ^ (Multiplicative.toAdd t).val)
  exact (((scalar_multiplicity_commute ζ).pow_pow _ _).mul_left
    ((paired_multiplicity_commute ζ).pow_pow _ _)).mul_left
      ((cyclic_multiplicity_commute ζ hζ).pow_pow _ _)

@[expose] def fourCubeHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Four →* adjointGroup .E7 K :=
  MonoidHom.noncommCoprod (cubeHom ζ hζ) (fourthHom ζ hζ) (cube_fourth_commute ζ hζ)

theorem fourCubeHom_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (p : Four) :
    fourCubeHom ζ hζ p = cubeHom ζ hζ p.1 *
      multiplicityWord ζ ^ (Multiplicative.toAdd p.2).val := rfl

theorem fourCubeHom_inl (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (f : D) :
    fourCubeHom ζ hζ (f, 1) = cubeHom ζ hζ f := by
  rw [fourCubeHom_apply]
  simp


theorem cube_range_le_fourCube_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (cubeHom ζ hζ).range ≤ (fourCubeHom ζ hζ).range := by
  rintro x ⟨f, rfl⟩
  exact ⟨(f, 1), fourCubeHom_inl ζ hζ f⟩

end CFSG.LieType.Chevalley.E7Three.FourCube
