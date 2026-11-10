module

public import CFSG.ClassicalInvolution.Asc77.AscC25W16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (mat_longInv_rev)
open scoped MatrixGroups

namespace Sp

variable {F : Type} [Field F]


@[expose] noncomputable def swapSp : StatedSp 2 F :=
  ofSymplecticMat (spIncl (K := F) (Fin.rev : Fin 2 → Fin 2)) (by
    rw [spIncl_transpose_mul_gram, Matrix.mul_assoc, spIncl_transpose_mul Fin.rev_injective,
      Matrix.mul_one])

theorem swapSp_mul (g : StatedSp 2 F) :
    swapSp * g = spEmbed (Fin.rev : Fin 2 → Fin 2) Fin.rev_injective g * swapSp := by
  apply mat_injective
  rw [map_mul, map_mul]
  change spIncl (K := F) Fin.rev * mat 2 F g =
    spEmbedMat Fin.rev (mat 2 F g) * spIncl (K := F) Fin.rev
  rw [spEmbedMat, add_mul, one_mul, Matrix.mul_assoc (spIncl (K := F) Fin.rev * (mat 2 F g - 1)),
    spIncl_transpose_mul Fin.rev_injective, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem swapSp_conj (g : StatedSp 2 F) :
    swapSp * g * swapSp⁻¹ = spEmbed (Fin.rev : Fin 2 → Fin 2) Fin.rev_injective g := by
  rw [swapSp_mul]
  group

theorem swapSp_conj_longBlock (l : Fin 2) (A : SL(2, F)) :
    swapSp * longBlock F 2 l A * swapSp⁻¹ = longBlock F 2 (Fin.rev l) A := by
  rw [swapSp_conj, spEmbed_longBlock]

theorem swapSp_conj_longInv (l : Fin 2) :
    swapSp * longInv F 2 l * swapSp⁻¹ = longInv F 2 (Fin.rev l) :=
  swapSp_conj_longBlock l (-1)

theorem map_conj_swapSp (k : Fin 2) :
    (longRootSp2 F 2 k).map (MulAut.conj (swapSp : StatedSp 2 F)).toMonoidHom =
      longRootSp2 F 2 (Fin.rev k) := by
  ext x
  constructor
  · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, (swapSp_conj_longBlock k A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨longBlock F 2 k A, ⟨A, rfl⟩, swapSp_conj_longBlock k A⟩


theorem map_conjSub_of_hom {G H : Type*} [Group G] [Group H] (ψ : G →* H) (g : G)
    (R : Subgroup G) : (conjSub g R).map ψ = conjSub (ψ g) (R.map ψ) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨ψ r, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨g * r * g⁻¹, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩


end Sp

section ModelFact


end ModelFact


end CFSG.ClassicalInvolution.Asc77.C25V
