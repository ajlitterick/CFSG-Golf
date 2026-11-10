module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}


@[expose] noncomputable def commForm (q : QuadraticForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) :
    LinearMap.BilinForm (ZMod 2) V :=
  q.polarBilin ∘ₗ ((t : V →ₗ[ZMod 2] V) - 1)

theorem commForm_apply (t : V ≃ₗ[ZMod 2] V) (x y : V) :
    commForm q t x y = polar q (t x - x) y := by
  simp [commForm]

namespace OrthoF2

theorem le_orthogonal_of_totallySingular {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0) :
    U ≤ LinearMap.BilinForm.orthogonal q.polarBilin U := by
  intro u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have h := hU (n + u) (Submodule.add_mem _ hn hu)
  rw [map_add_eq, hU n hn, hU u hu, zero_add, zero_add] at h
  rwa [polarBilin_apply_apply]


end OrthoF2


end CFSG.LargeExtraspecial
