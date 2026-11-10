module

public import CFSG.Quasithin.Background.RonanH154Base
public import CFSG.Quasithin.Background.RonanH163Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf


theorem act10_mem_combos_of (a : Array ℕ) {l : List ℕ} (h : ∀ x ∈ l, act10 a x ∈ combos l) :
    ∀ m ∈ combos l, act10 a m ∈ combos l :=
  mem_of_combos (fun x => act10 a x ∈ combos l)
    (by
      show act10 a 0 ∈ combos l
      rw [XorLin.map_zero (xorLin_act10 a)]
      exact zero_mem_combos l)
    (fun x y hx hy => by
      show act10 a (x ^^^ y) ∈ combos l
      rw [xorLin_act10 a x y]
      exact xor_mem_combos l hx hy)
    l h


theorem g1_inv_w1 : ∀ x ∈ w1, act10 g1Arr x ∈ combos w1 := by decide +kernel

theorem g1_inv_w2 : ∀ x ∈ w2, act10 g1Arr x ∈ combos w2 := by decide +kernel

theorem g1_inv_w6 : ∀ x ∈ w6, act10 g1Arr x ∈ combos w6 := by decide +kernel

theorem g2_inv_w1 : ∀ x ∈ w1, act10 g2Arr x ∈ combos w1 := by decide +kernel

theorem g2_inv_w2 : ∀ x ∈ w2, act10 g2Arr x ∈ combos w2 := by decide +kernel

theorem g2_inv_w6 : ∀ x ∈ w6, act10 g2Arr x ∈ combos w6 := by decide +kernel

theorem nq2_inv_w1 : ∀ u < 32, ∀ x ∈ w1, act10 (nq2Arr u) x ∈ combos w1 := by decide +kernel

theorem nq2_inv_w2 : ∀ u < 32, ∀ x ∈ w2, act10 (nq2Arr u) x ∈ combos w2 := by decide +kernel

theorem nq2_inv_w6 : ∀ u < 32, ∀ x ∈ w6, act10 (nq2Arr u) x ∈ combos w6 := by decide +kernel


@[expose] noncomputable def stabPWc (l : List ℕ) : Subgroup P24 :=
  ((stabSub (maskSub 10 l)).comap Rc).map mog22plus.subtype

theorem coe_mem_stabPWc {l : List ℕ} (x : ↥mog22plus) (hx : Rc x ∈ stabSub (maskSub 10 l)) :
    (x : P24) ∈ stabPWc l := by
  unfold stabPWc
  exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem Rc_mem_of_mem_stabPWc {l : List ℕ} {x : ↥mog22plus} (hx : (x : P24) ∈ stabPWc l) :
    Rc x ∈ stabSub (maskSub 10 l) := by
  unfold stabPWc at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  exact hz


theorem inv_gen_maskc (l : List ℕ)
    (h1 : ∀ x ∈ l, act10 g1Arr x ∈ combos l) (h2 : ∀ x ∈ l, act10 g2Arr x ∈ combos l)
    (hn : ∀ u < 32, ∀ x ∈ l, act10 (nq2Arr u) x ∈ combos l) :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ maskSub 10 l, g u ∈ maskSub 10 l := by
  have stab_g1 : Rc g1Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_g1 m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of g1Arr h1 m hm))
  have stab_g2 : Rc g2Elt ∈ stabSub (maskSub 10 l) := by
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_g2 m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of g2Arr h2 m hm))
  have stab_nq2 : ∀ u : Fin 32, Rc (nq2Elt u) ∈ stabSub (maskSub 10 l) := by
    intro u
    apply mem_stabSub_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hv
    exact (congrArg (fun w => w ∈ maskSub 10 l) (Rc_nq2 u m)).mpr
      (toW_mem_maskSub (act10_mem_combos_of _ (hn u.1 u.2) m hm))
  have hgen : Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) ≤ stabPWc l := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨u, rfl⟩ := hx
      exact coe_mem_stabPWc (nq2Elt u) (stab_nq2 u)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact coe_mem_stabPWc g1Elt stab_g1
      · exact coe_mem_stabPWc g2Elt stab_g2
  have hMY : MY mog22plus Qstd ≤ stabPWc l := le_trans MQ_le_closure hgen
  intro g hg u hu
  obtain ⟨y, hy, rfl⟩ :=
    Subgroup.mem_map.1 (show g ∈ Subgroup.map Rc ((MY mog22plus Qstd).subgroupOf mog22plus) from hg)
  have hyR := Rc_mem_of_mem_stabPWc (hMY (Subgroup.mem_subgroupOf.1 hy))
  exact (mem_stabSub.1 hyR u).2 hu

theorem inv_X1 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X1, g u ∈ X1 :=
  inv_gen_maskc w1 g1_inv_w1 g2_inv_w1 nq2_inv_w1

theorem inv_X2 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X2, g u ∈ X2 :=
  inv_gen_maskc w2 g1_inv_w2 g2_inv_w2 nq2_inv_w2

theorem inv_X6 :
    ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ X6, g u ∈ X6 :=
  inv_gen_maskc w6 g1_inv_w6 g2_inv_w6 nq2_inv_w6


end CFSG.Quasithin.RonanH154
