module

public import CFSG.Quasithin.Background.SimsG46ImprimPerm
import CFSG.Quasithin.Background.SimsG46ImprimFin4
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

structure IsTranspOn {r : ℕ} (W : Fin r → Submodule F V) (d : V ≃ₗ[F] V) (p q : Fin r) :
    Prop where
  ne : p ≠ q
  map_left : ∀ x ∈ W p, d x ∈ W q
  map_right : ∀ x ∈ W q, d x ∈ W p
  fix : ∀ t, t ≠ p → t ≠ q → ∀ x ∈ W t, d x = x

section Transp

variable {r : ℕ} {W : Fin r → Submodule F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {d : V ≃ₗ[F] V}
  {p q : Fin r}

theorem IsTranspOn.symm (h : IsTranspOn W d p q) : IsTranspOn W d q p :=
  ⟨h.ne.symm, h.map_right, h.map_left, fun t htq htp => h.fix t htp htq⟩

theorem IsTranspOn.conj (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {h : V ≃ₗ[F] V} (hh : h ∈ G₀)
    (hd : IsTranspOn W d p q) :
    IsTranspOn W (h * d * h⁻¹) (sumPerm W h p) (sumPerm W h q) := by
  have hinv := G₀.inv_mem hh
  have back : ∀ {i : Fin r} {x : V}, x ∈ W (sumPerm W h i) → h⁻¹ x ∈ W i := by
    intro i x hx
    have h1 := apply_mem_sumPerm hmap hinv hx
    rwa [sumPerm_inv_sumPerm hW hmap hh] at h1
  refine ⟨fun e => hd.ne (sumPerm_injective hW hmap hh e), fun x hx => ?_, fun x hx => ?_,
    fun t htp htq x hx => ?_⟩
  · simpa only [LinearEquiv.mul_apply] using
      apply_mem_sumPerm hmap hh (hd.map_left _ (back hx))
  · simpa only [LinearEquiv.mul_apply] using
      apply_mem_sumPerm hmap hh (hd.map_right _ (back hx))
  · have h1 : h⁻¹ x ∈ W (sumPerm W h⁻¹ t) := apply_mem_sumPerm hmap hinv hx
    have hne1 : sumPerm W h⁻¹ t ≠ p := fun e =>
      htp (by rw [← e, sumPerm_sumPerm_inv hW hmap hh])
    have hne2 : sumPerm W h⁻¹ t ≠ q := fun e =>
      htq (by rw [← e, sumPerm_sumPerm_inv hW hmap hh])
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hd.fix _ hne1 hne2 _ h1, mul_inv_apply]


end Transp


section Lines


end Lines


section Four


end Four

end G46Imprim

end CFSG.Quasithin.SimsG4
