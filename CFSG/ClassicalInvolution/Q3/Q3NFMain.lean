module

public import CFSG.ClassicalInvolution.Q3.Q3NFGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3NSFF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NS
open scoped commutatorElement


section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}


theorem pairData3_of_fuzzyFrame {J : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hJ : ∀ i, J i ∈ Ω ∧ IsClassicalMember3 (J i) (z i))
    (hAdef : A = Subgroup.closure (Set.range z)) (hAe : IsElemAbelian 2 A)
    (hAt : ∀ i, A ≤ trivialOnQuot (J i)) {a : G} (haA : a ∈ A) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω a) a) (localFamily (exactFamily3 Ω a) a))
    {p q : Fin 3} (hzpq : z p ≠ z q) :
    PairData3 (exactFamily3 Ω a) A a (exactCore3 a (J p)) (exactCore3 a (J q)) (z p) (z q) := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mem_isElemAbelian3 hAe haA
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hAe hg haA)
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have htq : ∀ i, J i ∈ tqMembers3 Ω a := fun i => ⟨(hJ i).1, hAt i haA⟩
  have hKY : ∀ i, exactCore3 a (J i) ≤ exactLayer3 Ω a := fun i => exactCore3_le_exactLayer3 (htq i)
  have hKΦ : ∀ i, exactCore3 a (J i) ∈ centralizingMembers (exactFamily3 Ω a) {a} := fun i =>
    ⟨exactCore3_mem_exactFamily3 (htq i), exactCore3_le_centralizer a (J i)⟩
  have hIn : ∀ i, IsClassicalMember3In (centralizingLayer (exactFamily3 Ω a) {a})
      (exactCore3 a (J i)) (z i) := fun i =>
    isClassicalMember3In_exactCore3 (hJ i).2 hc2 (hAt i haA) (hKY i)
      (exactLayer3_le_centralizer Ω a)
  have hcross : ∀ u v : Fin 3, ∀ x ∈ exactCore3 a (J v),
      ⁅z u, x⁆ ∈ oddCoreIn (centralizingLayer (exactFamily3 Ω a) {a}) := by
    intro u v x hx
    have hsec := FuzzyFrame3.isSectionMember3_exactCore3 hAe haA (hJ v).2 (hAt v)
    have hfam : modOddIn (centralizingLayer (exactFamily3 Ω a) {a}) (exactCore3 a (J v)) ∈
        localFamily (exactFamily3 Ω a) a :=
      ⟨(exactCore3 a (J v)).subgroupOf _, ⟨exactCore3 a (J v), hKΦ v, hKY v, rfl⟩, rfl⟩
    have hcard : Nat.card (modOddIn (centralizingLayer (exactFamily3 Ω a) {a})
        (exactCore3 a (J v))) = Nat.card (↥(exactCore3 a (J v)) ⧸
          classicalInvolutionOddCore ↥(exactCore3 a (J v))) := by
      rw [D.card_eq _ hfam]
      obtain ⟨e⟩ := hsec.nonempty_equiv
      rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
    have hO := oddCoreIn_le_of_card_modOddIn (hKY v) hcard
    have htv : A ≤ trivialOnQuot (exactCore3 a (J v)) :=
      FuzzyFrame3.le_trivialOnQuot_exactCore3 hAe haA (hJ v).2 (hAt v) le_rfl hAC
    exact hO ((htv (hzA u)).2 x hx)
  exact
    { memK := hKΦ p
      memK' := hKΦ q
      clsK := hIn p
      clsK' := hIn q
      memA := hzA p
      memA' := hzA q
      sq := (hJ p).2.isCentralInvolution.sq
      sq' := (hJ q).2.isCentralInvolution.sq
      ne_one := (hJ p).2.ne_one
      ne_one' := (hJ q).2.ne_one
      ne := hzpq
      comm := comm_of_mem_elemAbelian hAe (hzA p) (hzA q)
      central := fun x hx => (hJ p).2.isCentralInvolution.central x (exactCore3_le_left a (J p) hx)
      central' := fun x hx =>
        (hJ q).2.isCentralInvolution.central x (exactCore3_le_left a (J q) hx)
      cross := hcross p q
      cross' := hcross q p }

theorem fuzzy_independent {z : Fin 3 → G} (hsq : ∀ i, z i * z i = 1)
    (hcomm : ∀ i j, z i * z j = z j * z i)
    (hcard : Nat.card (Subgroup.closure (Set.range z)) = 8) :
    (∀ i j : Fin 3, i ≠ j → z i ≠ z j) ∧ z 0 * z 1 ≠ z 2 := by
  have hrange : Set.range z = ({z 0, z 1, z 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hdep : ¬ (z 0 = z 1 ∨ z 0 = z 2 ∨ z 1 = z 2 ∨ z 0 * z 1 = z 2) := fun hd => by
    have := card_closure_triple_le_four (hsq 0) (hsq 1) (hsq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2) hd
    rw [← hrange, hcard] at this
    omega
  refine ⟨fun i j hij => ?_, fun e => hdep (Or.inr (Or.inr (Or.inr e)))⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact fun e => hdep (Or.inl e)
    | exact fun e => hdep (Or.inr (Or.inl e))
    | exact fun e => hdep (Or.inr (Or.inr (Or.inl e)))
    | exact fun e => hdep (Or.inl e.symm)
    | exact fun e => hdep (Or.inr (Or.inl e.symm))
    | exact fun e => hdep (Or.inr (Or.inr (Or.inl e.symm)))

end Vertex

section Frame


end Frame

section NT


end NT

end CFSG.ClassicalInvolution.Q3.Q3NF
