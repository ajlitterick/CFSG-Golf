module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Data.CFSGNative.SectionRank.LocalDet

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.SectionRank.Native LocalWitness
open scoped Matrix commutatorElement

namespace LocalWitness

variable {G : Type*} [Group G]

noncomputable def treeElt (par lab : Array ℕ) (g : ℕ → G) : ℕ → G
  | 0 => 1
  | i + 1 =>
    if _ : par[i + 1]! < i + 1 then treeElt par lab g par[i + 1]! * g lab[i + 1]! else 1
termination_by i => i

theorem treeElt_zero (par lab : Array ℕ) (g : ℕ → G) : treeElt par lab g 0 = 1 := by
  rw [treeElt]

theorem treeElt_of_lt (par lab : Array ℕ) (g : ℕ → G) {i : ℕ} (hi : 0 < i)
    (hp : par[i]! < i) : treeElt par lab g i = treeElt par lab g par[i]! * g lab[i]! := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [zero_add] at hp ⊢
  rw [treeElt, dite_eq_left hp]

end LocalWitness

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem enum_spec [Inhabited M] [Inhabited V] (hWF : ∀ X : M, Sp.WF X)
    {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} {K1 K2 : M} {k1 k2 : Sˣ}
    (f1 : valHom S k1 = Sp.toMat K1) (f2 : valHom S k2 = Sp.toMat K2) {o1 o2 : ℕ}
    (ho1 : o1 ≠ 0) (ho2 : o2 ≠ 0) (hk1 : k1 ^ o1 = 1) (hk2 : k2 ^ o2 = 1) {n t : ℕ}
    {E : Array M} {par lab : Array ℕ} {cl : Array (Array ℕ)}
    (h : O.enumOK #[K1, K2] n t E par lab cl = true) :
    ∃ e : ℕ → Sˣ, (∀ i < n, valHom S (e i) = Sp.toMat E[i]!) ∧
      (∀ i < n, e i ∈ Subgroup.closure ({k1, k2} : Set Sˣ)) ∧
      (∀ u ∈ Subgroup.closure ({k1, k2} : Set Sˣ), ∃ i < n, u = e i) ∧
      (∀ i < n, ∀ j < n, e i = e j → i = j) := by
  unfold Ops.enumOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, -⟩, -⟩, -⟩, hn⟩, h0⟩, htree⟩, hcl⟩, hdist⟩ := h
  rw [List.all_eq_true] at htree hcl
  set g : ℕ → Sˣ := fun s => if s = 0 then k1 else k2
  set gens : Array M := #[K1, K2]
  have fg : ∀ s < 2, valHom S (g s) = Sp.toMat gens[s]! := by
    intro s hs
    interval_cases s
    · exact f1
    · exact f2
  set e := treeElt par lab g
  have he0 : e 0 = 1 := treeElt_zero par lab g
  have hes : ∀ i, 0 < i → par[i]! < i → e i = e par[i]! * g lab[i]! :=
    fun i => treeElt_of_lt par lab g
  have hmat : ∀ i < n, valHom S (e i) = Sp.toMat E[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [he0, map_one, Sp.toMat_eq (hWF _) Sp.one_wf h0, Sp.toMat_one]
      · have := htree i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
        rcases this with h1 | ⟨⟨hp, hl⟩, heq⟩
        · omega
        · rw [hes i hpos hp, map_mul, ih _ hp (by omega),
            Sp.toMat_eq (hWF _) (hWF _) heq, Sp.toMat_mul (hWF _) (hWF _), fg _ hl]
  have hmem : ∀ i < n, e i ∈ Subgroup.closure ({k1, k2} : Set Sˣ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [he0]; exact Subgroup.one_mem _
      · have := htree i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
        rcases this with h1 | ⟨⟨hp, hl⟩, -⟩
        · omega
        · rw [hes i hpos hp]
          refine Subgroup.mul_mem _ (ih _ hp (by omega)) (Subgroup.subset_closure ?_)
          simp only [g]
          split_ifs
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
  have hright : ∀ i < n, ∀ s < 2, ∃ j < n, e i * g s = e j := by
    intro i hi s hs
    have := List.all_eq_true.1 (hcl i (List.mem_range.2 hi)) s (List.mem_range.2 hs)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    refine ⟨_, this.1, valHom_injective S ?_⟩
    rw [map_mul, hmat i hi, fg s hs, hmat _ this.1, ← Sp.toMat_mul (hWF _) (hWF _)]
    exact Sp.toMat_eq (hWF _) (hWF _) this.2
  have hpow : ∀ s < 2, ∀ m, ∀ i < n, ∃ j < n, e i * g s ^ m = e j := by
    intro s hs m
    induction m with
    | zero => intro i hi; exact ⟨i, hi, by rw [pow_zero, mul_one]⟩
    | succ m ih =>
      intro i hi
      obtain ⟨j, hj, hje⟩ := ih i hi
      obtain ⟨j', hj', hj'e⟩ := hright j hj s hs
      exact ⟨j', hj', by rw [pow_succ, ← mul_assoc, hje, hj'e]⟩
  have hgen : ∀ s ∈ ({k1, k2} : Set Sˣ), ∃ t < 2, g t = s ∧ ∃ o, o ≠ 0 ∧ s ^ o = 1 := by
    rintro s (rfl | rfl)
    · exact ⟨0, by norm_num, by simp [g], o1, ho1, hk1⟩
    · exact ⟨1, by norm_num, by simp [g], o2, ho2, hk2⟩
  have hall : ∀ u ∈ Subgroup.closure ({k1, k2} : Set Sˣ), ∃ i < n, u = e i := by
    intro u hu
    induction hu using Subgroup.closure_induction_right with
    | one => exact ⟨0, hn, by rw [he0]⟩
    | mul_right u _ s hs ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨t', ht, rfl, -⟩ := hgen s hs
      obtain ⟨j, hj, hje⟩ := hright i hi t' ht
      exact ⟨j, hj, hje⟩
    | mul_inv_cancel u _ s hs ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨t', ht, rfl, o, ho, hso⟩ := hgen s hs
      have hinv : (g t')⁻¹ = g t' ^ (o - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel
          (Nat.pos_of_ne_zero ho), hso]
      obtain ⟨j, hj, hje⟩ := hpow t' ht (o - 1) i hi
      exact ⟨j, hj, by rw [hinv, hje]⟩
  refine ⟨e, hmat, hmem, hall, fun i hi j hj hij => ?_⟩
  by_contra hne
  have hsz : (E.map fun X => O.vmul (O.unit t) X).size = n := by simp [hE]
  apply Sp.toVec_ne_of_distinctOK hdist (by rw [hsz]; exact hi) (by rw [hsz]; exact hj) hne
  rw [getElem!_pos _ i (by rw [hsz]; exact hi), getElem!_pos _ j (by rw [hsz]; exact hj),
    Array.getElem_map, Array.getElem_map, Sp.toVec_vmul (Sp.unit_wf _) (hWF _),
    Sp.toVec_vmul (Sp.unit_wf _) (hWF _), ← getElem!_pos E i (by rw [hE]; exact hi),
    ← getElem!_pos E j (by rw [hE]; exact hj), ← hmat i hi, ← hmat j hj, hij]

theorem memOK_spec [Inhabited M] (hWF : ∀ X : M, Sp.WF X) {E : Array M} {X : M}
    (h : O.memOK E X = true) : ∃ j < E.size, Sp.toMat X = Sp.toMat E[j]! := by
  obtain ⟨j, hj, hjx⟩ := List.any_eq_true.1 h
  exact ⟨j, List.mem_range.1 hj, Sp.toMat_eq (hWF _) (hWF _) hjx⟩


end OpsSpec

end CFSG.SectionRank
