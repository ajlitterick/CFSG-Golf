module

public import CFSG.Quasithin.Background.RonanH143Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin

theorem exists_labAct {G α : Type*} [Group G] [MulAction G α] {n : ℕ} (X : Fin n → α)
    (hX : Function.Injective X) (H : Subgroup G) (hH : ∀ g ∈ H, ∀ i, ∃ j, g • X i = X j) :
    ∃ π : ↥H →* Equiv.Perm (Fin n), ∀ (g : ↥H) (i : Fin n), X (π g i) = (g : G) • X i := by
  have hc : ∀ g : ↥H, ∀ i, ∃ j, (g : G) • X i = X j := fun g i => hH (g : G) g.2 i
  choose f hf using hc
  have hmul : ∀ g h : ↥H, ∀ i, f (g * h) i = f g (f h i) := by
    intro g h i
    apply hX
    rw [← hf (g * h) i, ← hf g (f h i), ← hf h i, Subgroup.coe_mul, mul_smul]
  have hone : ∀ i, f 1 i = i := by
    intro i
    apply hX
    rw [← hf 1 i, Subgroup.coe_one, one_smul]
  have hinv : ∀ g : ↥H, ∀ i, f g⁻¹ (f g i) = i := by
    intro g i
    apply hX
    rw [← hf g⁻¹ (f g i), ← hf g i, Subgroup.coe_inv, inv_smul_smul]
  have hinv' : ∀ g : ↥H, ∀ i, f g (f g⁻¹ i) = i := by
    intro g i
    apply hX
    rw [← hf g (f g⁻¹ i), ← hf g⁻¹ i, Subgroup.coe_inv, smul_inv_smul]
  refine ⟨{ toFun := fun g =>
              { toFun := f g
                invFun := f g⁻¹
                left_inv := hinv g
                right_inv := hinv' g }
            map_one' := Equiv.ext hone
            map_mul' := fun g h => Equiv.ext (hmul g h) }, fun g i => (hf g i).symm⟩


end CFSG.Quasithin.RonanH143
