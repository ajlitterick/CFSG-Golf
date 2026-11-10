module

public import CFSG.Sporadic.J4.StabSpec
public import CFSG.Sporadic.J4.LocalOrder
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Suborbits
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

theorem isPreprimitive_of_labels {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X →
      S = {lab x} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive G X := by
  classical
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclosed : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by
      rw [hH h hh]
      exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin k) := (Finset.univ.filter (· ∈ B)).image lab
  have hmemS : ∀ p, lab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem lab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => lab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS,
      ← Nat.card_eq_fintype_card]
    exact hB.ncard_dvd_card ⟨x, hxB⟩
  rcases hdiv S ((hmemS x).mpr hxB) hdvd with hS | hS
  · left
    have hx : ∀ r ∈ B, r = x := by
      intro r hr
      have hr' : lab r ∈ S := (hmemS r).mpr hr
      rw [hS, Finset.mem_singleton] at hr'
      obtain ⟨h, hh, hhr⟩ := horb x r hr'.symm
      rw [← hhr, hH h hh]
    intro p hp q hq
    rw [hx p hp, hx q hq]
  · right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (lab p)


@[expose] def subSizesF : Fin 7 → ℕ := ![1, 32643072, 82575360, 54405120, 3400320, 15180, 28336]

theorem subSizesF_blocks (S : Finset (Fin 7)) (h0 : (0 : Fin 7) ∈ S)
    (hd : (∑ i ∈ S, subSizesF i) ∣ 173067389) : S = {0} ∨ S = Finset.univ := by
  rw [← Finset.univ_inter S, ← Finset.sum_ite_mem, Fin.sum_univ_seven] at hd
  simp only [subSizesF, h0, ite_true] at hd
  split_ifs at hd with h1 h2 h3 h4 h5 h6
  all_goals first | (exfalso; norm_num at hd; done) | skip
  · right
    exact Finset.eq_univ_of_forall fun i => by fin_cases i <;> assumption
  · left
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨h0, fun i hi => by fin_cases i <;> simp_all⟩


section Facts

variable (hF : J4NativeFacts)
include hF


theorem reps_eq : L0.reps = subReps := beq_iff_eq.mp hF.reps


end Facts

end CFSG.Sporadic.J4
