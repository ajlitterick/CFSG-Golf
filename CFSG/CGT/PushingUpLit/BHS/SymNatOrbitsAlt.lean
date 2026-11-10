module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsCount
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

variable {n : ℕ}

theorem setStab_le_normalizer_altOn (S : Finset (Fin n)) :
    setStab S ≤ Subgroup.normalizer (altOn S : Set (Equiv.Perm (Fin n))) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_altOn, mem_altOn, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
    mul_right_comm, Int.units_mul_self, one_mul]
  refine and_congr_left fun _ => ⟨fun h1 x hx => ?_, fun h1 x hx => ?_⟩
  · have hx' : y⁻¹ x ∉ S := by
      intro h'
      have h2 := (mem_setStab.1 hy (y⁻¹ x)).2 h'
      rw [perm_apply_inv_self] at h2
      exact hx h2
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1 _ hx', perm_apply_inv_self]
  · have hx' : y x ∉ S := fun h' => hx ((mem_setStab.1 hy x).1 h')
    have h2 := h1 (y x) hx'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self] at h2
    exact y.injective h2

theorem three_le_card_movFin {F : Subgroup (Equiv.Perm (Fin n))} (hF : opResidual 2 F = F)
    {x₀ : Fin n} (hx₀ : ∃ f ∈ F, f x₀ ≠ x₀) : 3 ≤ (movFin F).card := by
  obtain ⟨f, hf, hfx⟩ := hx₀
  obtain ⟨g, hg, hgx, hgf⟩ := exists_third_of_opResidual hF hf hfx
  have hmem : ∀ h ∈ F, h x₀ ≠ x₀ → h x₀ ∈ movFin F := fun h hh hhx =>
    mem_movFin.2 ⟨h⁻¹, F.inv_mem hh, by rw [perm_inv_apply_self]; exact hhx.symm⟩
  exact Finset.two_lt_card_iff.2 ⟨x₀, f x₀, g x₀, mem_movFin.2 ⟨f, hf, hfx⟩, hmem f hf hfx,
    hmem g hg hgx, hfx.symm, hgx.symm, hgf.symm⟩


end CFSG.CGT.PushingUpLit.BHS
