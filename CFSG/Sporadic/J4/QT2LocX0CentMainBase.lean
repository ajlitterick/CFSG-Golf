
module

public import CFSG.Sporadic.J4.QT2LocX0MainBase
public import CFSG.Sporadic.J4.QT2LocScanNative
public import CFSG.Sporadic.J4.QT2LocFixMainBase
public import CFSG.Sporadic.J4.QT2LocX0KNative

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

set_option maxRecDepth 100000


theorem enum_facts {nl m : ℕ} {R : Array (Array V2)} {O : MOrb} {w : Array V2}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl w O m = true) :
    O.mats.size = m ∧ 0 < m ∧ O.mats[0]! = w ∧
      ∀ q < m, oOrbAt (fun M g => mulRows M (R[g]!)) nl O q = true := by
  unfold oOrbOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
  exact ⟨h1, h4, eqRows_iff.1 h5, h6⟩

theorem enum_closure_sub {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    ∀ g ∈ Subgroup.closure (G '' {i | i < nl}), ∃ q < m, Mx g = rowsMatrix (O.mats[q]!) := by
  obtain ⟨hsz, hm0, hroot, hat⟩ := enum_facts hok
  have hstep : ∀ g : J, (∃ q < m, Mx g = rowsMatrix (O.mats[q]!)) → ∀ i < nl,
      ∃ q < m, Mx (g * G i) = rowsMatrix (O.mats[q]!) := by
    rintro g ⟨q, hq, hgq⟩ i hi
    obtain ⟨-, -, hstep, -⟩ := oOrbAt_facts (hat q hq)
    obtain ⟨e, he0, hesz, hee⟩ := hstep i hi
    refine ⟨e - 1, by omega, ?_⟩
    rw [hee, map_mul, hgq, hR i hi]
    exact (rowsMatrix_mulRows _ _).symm
  have hone : ∃ q < m, Mx (1 : J) = rowsMatrix (O.mats[q]!) :=
    ⟨0, hm0, by rw [hroot, map_one, rowsMatrix_idRows]⟩
  have hmul : ∀ k ∈ Submonoid.closure (G '' {i | i < nl}), ∀ g : J,
      (∃ q < m, Mx g = rowsMatrix (O.mats[q]!)) →
        ∃ q < m, Mx (g * k) = rowsMatrix (O.mats[q]!) := by
    intro k hk
    induction hk using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact fun g hg => hstep g hg i hi
    | one => intro g hg; simpa using hg
    | mul x y _ _ hx hy => intro g hg; rw [← mul_assoc]; exact hy _ (hx g hg)
  intro g hg
  have hg' : g ∈ (Subgroup.closure (G '' {i | i < nl})).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  have := hmul g hg' 1 hone
  rwa [one_mul] at this

theorem enum_of_lt {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    ∀ q < m, ∃ g ∈ Subgroup.closure (G '' {i | i < nl}), Mx g = rowsMatrix (O.mats[q]!) := by
  obtain ⟨hsz, hm0, hroot, hat⟩ := enum_facts hok
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    obtain ⟨-, -, -, hpar⟩ := oOrbAt_facts (hat q hq)
    rcases hpar with h0 | ⟨hp, hl, hst⟩
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      subst h0
      rw [hroot, map_one, rowsMatrix_idRows]
    · obtain ⟨g, hg, hgM⟩ := ih _ hp (lt_trans hp hq)
      refine ⟨g * G (O.lab[q]!), Subgroup.mul_mem _ hg (Subgroup.subset_closure ⟨_, hl, rfl⟩), ?_⟩
      rw [← hst, map_mul, hgM, hR _ hl]
      exact (rowsMatrix_mulRows _ _).symm

theorem enum_inj {nl m : ℕ} {R : Array (Array V2)} {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true)
    {q q' : ℕ} (hq : q < m) (hq' : q' < m)
    (h : rowsMatrix (O.mats[q]!) = rowsMatrix (O.mats[q']!)) : q = q' := by
  obtain ⟨-, -, -, hat⟩ := enum_facts hok
  obtain ⟨hw, hf, -⟩ := oOrbAt_facts (hat q hq)
  obtain ⟨hw', hf', -⟩ := oOrbAt_facts (hat q' hq')
  have := eq_of_rowsMatrix_eq hw hw' h
  rw [this] at hf
  omega

theorem card_enum {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    Nat.card (Subgroup.closure (G '' {i | i < nl})) = m := by
  let f : Fin m → Subgroup.closure (G '' {i | i < nl}) := fun q =>
    ⟨(enum_of_lt hR hok q q.2).choose, (enum_of_lt hR hok q q.2).choose_spec.1⟩
  have hspec : ∀ q : Fin m, Mx (f q : J) = rowsMatrix (O.mats[q.val]!) := fun q =>
    (enum_of_lt hR hok q q.2).choose_spec.2
  have hbij : Function.Bijective f := by
    constructor
    · intro q q' h
      have h1 : Mx (f q : J) = Mx (f q' : J) := by rw [h]
      rw [hspec, hspec] at h1
      exact Fin.ext (enum_inj hok q.2 q'.2 h1)
    · intro g
      obtain ⟨q, hq, hgq⟩ := enum_closure_sub hR hok g g.2
      refine ⟨⟨q, hq⟩, ?_⟩
      apply Subtype.ext
      apply Mx_injective
      rw [hspec]
      exact hgq.symm
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp

@[expose] noncomputable def kGen (i : ℕ) : J :=
  if i < 6 then QT2A.el5 (kWords.getD i []) else (QT2A.el5 (kWords.getD (i - 6) []))⁻¹

@[expose] noncomputable def KSub : Subgroup J := Subgroup.closure (kGen '' {i | i < 12})

@[expose] noncomputable def q1Row : Row := toRow x0Q1.toVec


theorem fiveElt_smul_pts
    (hM : MatFacts) {p : Row} (hp : p ∈ x0PtSet) : fiveElt • p = p := by
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_pts hM hp
  have hc : fiveElt * g = g * fiveElt :=
    (Subgroup.mem_centralizer_singleton_iff.1 (X0Sub_le_centralizer hM hg)).symm
  rw [← mul_smul, hc, mul_smul, smul_root_of_mem_Hj hM fiveElt_mem_Hj]

theorem w₀_mem_pts (hM : MatFacts) : w₀ ∈ x0PtSet := by
  have := smul_mem_pts hM (X0Sub.one_mem : (1 : J) ∈ X0Sub)
  rwa [one_smul] at this


end CFSG.Sporadic.J4.QT2
