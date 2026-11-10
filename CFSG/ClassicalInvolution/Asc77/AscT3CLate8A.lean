module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwap
import CFSG.ClassicalInvolution.Asc77.AscT3CLate8BEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexMain

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Elem

variable {G : Type} [Group G]

theorem late_exists_pow_invol {b : G} (hb : IsPGroup 2 ↥(Subgroup.zpowers b)) (hb1 : b ≠ 1) :
    ∃ n : ℕ, b ^ n * b ^ n = 1 ∧ b ^ n ≠ 1 := by
  exact late_exists_pow_involE hb hb1

end Elem

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

omit [Finite G] in
theorem late_mem_cmo {H L : Subgroup G} {x : G} :
    x ∈ centralizerModOdd H L ↔ x ∈ H ∧ x ∈ Subgroup.normalizer (L : Set G) ∧
      x ∈ Subgroup.normalizer (oddCoreOf L : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oddCoreOf L := Iff.rfl

private theorem Std20.late_toG (d : Std20 p f K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }


theorem Std20.late_inv_W (d : Std20 p f K K' J S R R' W V z t) :
    ∀ w ∈ W, w * w = 1 → w = 1 ∨ w = z ∨ w = t ∨ w = z * t := by
  exact d.late_toG.late_inv_W


theorem Std20.late_stepA (d : Std20 p f K K' J S R R' W V z t)
    (hc7 : centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) : x ∈ R' := by
  exact d.late_toG.late_stepA hc7 hx

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
