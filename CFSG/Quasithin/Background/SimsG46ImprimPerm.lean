module

public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG4Core

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

noncomputable def sumPerm {r : ℕ} (W : Fin r → Submodule F V) (g : V ≃ₗ[F] V) (i : Fin r) :
    Fin r := by
  classical
  exact if h : ∃ j, (W i).map (g : V →ₗ[F] V) = W j then h.choose else i

section Summands

variable {r : ℕ} {W : Fin r → Submodule F V} {G₀ : Subgroup (V ≃ₗ[F] V)}


theorem map_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) (i : Fin r) :
    (W i).map (g : V →ₗ[F] V) = W (sumPerm W g i) := by
  have h := hmap g hg i
  unfold sumPerm
  rw [dif_pos h]
  exact h.choose_spec

theorem apply_mem_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {i : Fin r} {x : V} (hx : x ∈ W i) :
    g x ∈ W (sumPerm W g i) := by
  rw [← map_sumPerm hmap hg i]
  exact Submodule.mem_map_of_mem hx

theorem sumPerm_mul (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g h : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (hh : h ∈ G₀) (i : Fin r) :
    sumPerm W (g * h) i = sumPerm W g (sumPerm W h i) := by
  apply hW
  rw [← map_sumPerm hmap (G₀.mul_mem hg hh) i, ← map_sumPerm hmap hg (sumPerm W h i),
    ← map_sumPerm hmap hh i, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
    Submodule.map_comp]

theorem sumPerm_one (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (i : Fin r) :
    sumPerm W 1 i = i := by
  apply hW
  rw [← map_sumPerm hmap G₀.one_mem i, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]

theorem sumPerm_inv_sumPerm (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (i : Fin r) : sumPerm W g⁻¹ (sumPerm W g i) = i := by
  rw [← sumPerm_mul hW hmap (G₀.inv_mem hg) hg, inv_mul_cancel, sumPerm_one hW hmap]

theorem sumPerm_sumPerm_inv (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (i : Fin r) : sumPerm W g (sumPerm W g⁻¹ i) = i := by
  rw [← sumPerm_mul hW hmap hg (G₀.inv_mem hg), mul_inv_cancel, sumPerm_one hW hmap]

theorem sumPerm_injective (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) : Function.Injective (sumPerm W g) := fun i j h => by
  rw [← sumPerm_inv_sumPerm hW hmap hg i, h, sumPerm_inv_sumPerm hW hmap hg j]


end Summands


end G46Imprim

end CFSG.Quasithin.SimsG4
