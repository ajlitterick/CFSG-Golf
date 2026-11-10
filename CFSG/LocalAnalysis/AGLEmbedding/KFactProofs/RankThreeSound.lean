module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeLemmas
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness

@[expose] def actMat (p : ℕ) (g : Act) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  fun k i => ((g.mat.getD (3 * k.val + i.val) 0 : ℕ) : ZMod p)

theorem mem_nonzeroTriples {p : ℕ} {v : ℕ × ℕ × ℕ} :
    v ∈ nonzeroTriples p ↔
      v.1 < p ∧ v.2.1 < p ∧ v.2.2 < p ∧ ¬(v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0) := by
  obtain ⟨a, b, c⟩ := v
  simp only [nonzeroTriples, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', ha', b', hb', c', hc', rfl, rfl, rfl⟩, hne⟩
    refine ⟨ha', hb', hc', ?_⟩
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hne
    tauto
  · rintro ⟨ha, hb, hc, hne⟩
    refine ⟨⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩, ?_⟩
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem fixes_of_invariant {p : ℕ} [Fact p.Prime] (g : Act) (u : Fin 3 → ZMod p)
    (h : (actMat p g).transpose * alt3 u * actMat p g = alt3 u) :
    g.fixes p (u 0).val (u 1).val (u 2).val = true := by
  have key : ∀ (i j : Fin 3), ((actMat p g).transpose * alt3 u * actMat p g) i j = alt3 u i j :=
    fun i j => by rw [h]
  have e01 := key 0 1
  have e02 := key 0 2
  have e12 := key 1 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, alt3_00, alt3_01,
    alt3_02, alt3_10, alt3_11, alt3_12, alt3_20, alt3_21, alt3_22, actMat, Fin.val_zero,
    Fin.val_one, Fin.val_two, Nat.reduceMul, Nat.reduceAdd, mul_zero, zero_add,
    add_zero] at e01 e02 e12
  have dv : ∀ x : ℤ, ((x : ℤ) : ZMod p) = 0 → x % (p : ℤ) = 0 := fun x hx =>
    Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 hx)
  unfold Act.fixes Act.formEntry
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨dv _ ?_, dv _ ?_⟩, dv _ ?_⟩
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e01
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e02
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e12


theorem noAlt_of_entries {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n m : ℕ} (hn : n = 3)
    (M : Fin m → Matrix (Fin n) (Fin n) (ZMod p)) (acts : List Act)
    (hMe : ∀ g ∈ acts, ∃ j : Fin m, ∀ k i : Fin n,
      M j k i = ((g.mat.getD (3 * k.val + i.val) 0 : ℕ) : ZMod p))
    (hNA : ∀ u : Fin 3 → ZMod p,
      (∀ g ∈ acts, (actMat p g).transpose * alt3 u * actMat p g = alt3 u) → u = 0) :
    ∀ B : Matrix (Fin n) (Fin n) (ZMod p), B.transpose = -B →
      (∀ j, (M j).transpose * B * M j = B) → B = 0 := by
  subst hn
  refine noAlt_three hp2 M fun u hu => hNA u fun g hg => ?_
  obtain ⟨j, hj⟩ := hMe g hg
  have : M j = actMat p g := by ext k i; exact hj k i
  rw [← this]
  exact hu j

section Chain

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert}

theorem hasOrd_of_chain {p : ℕ} (l : List Pc) (hl : ∀ q ∈ l, ∀ f ∈ q.facts p, f ∈ C.facts)
    {w : Word} (hw : w.all (fun a => l.any (·.reg == a.1)) = true) : HasOrd C w := by
  intro a ha
  obtain ⟨q, hq, hqa⟩ := List.any_eq_true.1 (List.all_eq_true.1 hw a ha)
  refine ⟨q.ord, hl q hq _ ?_⟩
  simp only [beq_iff_eq] at hqa
  rw [← hqa]
  simp [Pc.facts]

variable (hC : mcertCheck O sA sB C = true) {p : ℕ}

theorem wordUnit_mem_chain (l : List Pc) {w : Word}
    (hw : w.all (fun a => l.any (·.reg == a.1)) = true) :
    wordUnit Sp hC w ∈ Subgroup.closure {u | ∃ q ∈ l, u = regUnit Sp hC q.reg} := by
  refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ w fun a ha => ?_
  obtain ⟨q, hq, hqa⟩ := List.any_eq_true.1 (List.all_eq_true.1 hw a ha)
  simp only [beq_iff_eq] at hqa
  exact Subgroup.subset_closure ⟨q, hq, by rw [hqa]⟩

theorem chain_isPGroup [Fact p.Prime] :
    ∀ l : List Pc, pcWf l = true → (∀ q ∈ l, ∀ f ∈ q.facts p, f ∈ C.facts) →
      IsPGroup p (Subgroup.closure {u | ∃ q ∈ l, u = regUnit Sp hC q.reg})
  | [], _, _ => by
    have : {u | ∃ q ∈ ([] : List Pc), u = regUnit Sp hC q.reg} = ∅ := by
      ext u; simp
    rw [this, Subgroup.closure_empty]
    intro g
    exact ⟨0, Subtype.ext (by simpa using Subgroup.mem_bot.1 g.2)⟩
  | q :: rest, hwf, hfacts => by
    have hrest : ∀ r ∈ rest, ∀ f ∈ r.facts p, f ∈ C.facts :=
      fun r hr => hfacts r (List.mem_cons_of_mem _ hr)
    have hq := hfacts q List.mem_cons_self
    simp only [pcWf, Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨hpw, hcj⟩, hall⟩, hwfrest⟩ := hwf
    have ih := chain_isPGroup rest hwfrest hrest
    set s : Set (certMonoid c d sA sB)ˣ := {u | ∃ r ∈ rest, u = regUnit Sp hC r.reg} with hs
    have hins : {u | ∃ r ∈ q :: rest, u = regUnit Sp hC r.reg} =
        insert (regUnit Sp hC q.reg) s := by
      ext u
      simp only [Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff, hs]
      constructor
      · rintro ⟨r, rfl | hr, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r, hr, rfl⟩
      · rintro (rfl | ⟨r, hr, rfl⟩)
        · exact ⟨q, Or.inl rfl, rfl⟩
        · exact ⟨r, Or.inr hr, rfl⟩
    have hqord : MFact.ord q.reg q.ord ∈ C.facts := hq _ (by simp [Pc.facts])
    have hwordrest : ∀ {w : Word}, w.all (fun a => rest.any (·.reg == a.1)) = true →
        HasOrd C w := fun hw => hasOrd_of_chain rest hrest hw
    rw [hins]
    refine isPGroup_closure_insert ih ?_ ?_
    · have hf : MFact.eq [(q.reg, p)] q.pw ∈ C.facts := hq _ (by simp [Pc.facts])
      have hu : HasOrd C [(q.reg, p)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨q.ord, hqord⟩
      have := regUnit_eq Sp hC hf hu (hwordrest hpw)
      have e : wordUnit Sp hC [(q.reg, p)] = regUnit Sp hC q.reg ^ p := by simp [wordUnit]
      rw [e] at this
      rw [this]
      exact wordUnit_mem_chain Sp hC rest hpw
    · rintro x ⟨r, hr, rfl⟩
      obtain ⟨cc, hcc, hcr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hall r hr)
      simp only [beq_iff_eq] at hcr
      have hcc' := List.all_eq_true.1 hcj cc hcc
      simp only [Bool.and_eq_true] at hcc'
      have hf : MFact.conj q.reg [(cc.1, 1)] cc.2 ∈ C.facts :=
        hq _ (by
          simp only [Pc.facts, List.mem_append, List.mem_map]; exact Or.inr ⟨cc, hcc, rfl⟩)
      have hu : HasOrd C [(cc.1, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha
        rw [ha]
        obtain ⟨r', hr', hrr'⟩ := List.any_eq_true.1 hcc'.1
        simp only [beq_iff_eq] at hrr'
        exact ⟨r'.ord, hrest r' hr' _ (by rw [← hrr']; simp [Pc.facts])⟩
      have := regUnit_conj Sp hC hf hqord hu (hwordrest hcc'.2)
      have e : wordUnit Sp hC [(cc.1, 1)] = regUnit Sp hC r.reg := by
        simp [wordUnit, hcr]
      rw [e] at this
      rw [this]
      exact wordUnit_mem_chain Sp hC rest hcc'.2

end Chain

section Module

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true) {p : ℕ}

omit [Inhabited M] in
theorem basis_ord (m : Mod) (hf : ∀ f ∈ m.facts p, f ∈ C.facts) (i : Fin 3) :
    MFact.ord (m.basis i) p ∈ C.facts := by
  apply hf
  fin_cases i <;> simp [Mod.facts, Mod.basis]

include Sp hC in
theorem exists_moduleSpec_core [Fact p.Prime] (m : Mod)
    (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    (hindep : ∀ v ∈ nonzeroTriples p, ∃ q ∈ m.indep, q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2) :
    ∃ DS : ModuleSpec (certMonoid c d sA sB)ˣ p, DS.n = 3 ∧
      (∀ g ∈ m.acts, ∃ j : Fin DS.m, DS.g j = regUnit Sp hC g.reg ∧
        ∀ k i : Fin DS.n, DS.M j k i = ((g.mat.getD (3 * k.val + i.val) 0 : ℕ) : ZMod p)) ∧
      DS.span = Subgroup.closure (Set.range fun i : Fin 3 => regUnit Sp hC (m.basis i)) := by
  have hb0 : MFact.ord m.b0 p ∈ C.facts := hf _ (by simp [Mod.facts])
  have hb1 : MFact.ord m.b1 p ∈ C.facts := hf _ (by simp [Mod.facts])
  have hb2 : MFact.ord m.b2 p ∈ C.facts := hf _ (by simp [Mod.facts])
  have hBasisOrd : ∀ w : Word, (∀ q ∈ w, q.1 = m.b0 ∨ q.1 = m.b1 ∨ q.1 = m.b2) → HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h | h
    · exact ⟨p, h ▸ hb0⟩
    · exact ⟨p, h ▸ hb1⟩
    · exact ⟨p, h ▸ hb2⟩
  have hpowb : ∀ i : Fin 3, regUnit Sp hC (m.basis i) ^ p = 1 := fun i =>
    regUnit_pow Sp hC (basis_ord m hf i)
  have f01 : MFact.eq [(m.b0, 1), (m.b1, 1)] [(m.b1, 1), (m.b0, 1)] ∈ C.facts :=
    hf _ (by simp [Mod.facts])
  have f02 : MFact.eq [(m.b0, 1), (m.b2, 1)] [(m.b2, 1), (m.b0, 1)] ∈ C.facts :=
    hf _ (by simp [Mod.facts])
  have f12 : MFact.eq [(m.b1, 1), (m.b2, 1)] [(m.b2, 1), (m.b1, 1)] ∈ C.facts :=
    hf _ (by simp [Mod.facts])
  have c01 : regUnit Sp hC m.b0 * regUnit Sp hC m.b1 = regUnit Sp hC m.b1 * regUnit Sp hC m.b0 := by
    have := regUnit_eq Sp hC f01 (hBasisOrd _ (by simp)) (hBasisOrd _ (by simp))
    simpa [wordUnit] using this
  have c02 : regUnit Sp hC m.b0 * regUnit Sp hC m.b2 = regUnit Sp hC m.b2 * regUnit Sp hC m.b0 := by
    have := regUnit_eq Sp hC f02 (hBasisOrd _ (by simp)) (hBasisOrd _ (by simp))
    simpa [wordUnit] using this
  have c12 : regUnit Sp hC m.b1 * regUnit Sp hC m.b2 = regUnit Sp hC m.b2 * regUnit Sp hC m.b1 := by
    have := regUnit_eq Sp hC f12 (hBasisOrd _ (by simp)) (hBasisOrd _ (by simp))
    simpa [wordUnit] using this
  have hacts : ∀ g ∈ m.acts, MFact.ord g.reg g.ord ∈ C.facts ∧
      ∀ i : Fin 3, MFact.conj g.reg [(m.basis i, 1)] (m.col g i) ∈ C.facts := by
    intro g hg
    refine ⟨hf _ ?_, fun i => hf _ ?_⟩
    · simp only [Mod.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨g, hg, by simp⟩
    · simp only [Mod.facts, List.mem_append, List.mem_flatMap]
      refine Or.inr ⟨g, hg, ?_⟩
      fin_cases i <;> simp
  refine ⟨{ n := 3
            m := m.acts.length
            a := fun i => regUnit Sp hC (m.basis i)
            g := fun j => regUnit Sp hC (m.acts.get j).reg
            M := fun j => actMat p (m.acts.get j)
            comm := ?_
            pow := hpowb
            indep := ?_
            act := ?_ }, rfl, ?_, rfl⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 |
        exact c12.symm
  · intro cc hcc
    by_contra hne
    have hv : ((cc 0).val, (cc 1).val, (cc 2).val) ∈ nonzeroTriples p := by
      rw [mem_nonzeroTriples]
      refine ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ?_⟩
      rintro ⟨h0, h1, h2⟩
      apply hne
      ext k
      fin_cases k
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1
      · exact (ZMod.val_eq_zero _).1 h2
    obtain ⟨q, hq, hq0, hq1, hq2⟩ := hindep _ hv
    have hfne : MFact.ne (m.word q.1 q.2.1 q.2.2.1) [] q.2.2.2 ∈ C.facts :=
      hf _ (by
        simp only [Mod.facts, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨q, hq, rfl⟩))
    have := regUnit_ne Sp hC hfne (hBasisOrd _ (by simp [Mod.word])) (hasOrd_nil C)
    apply this
    rw [wordUnit_nil, Mod.word, hq0, hq1, hq2]
    simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    simp only [List.finRange_succ, List.map_cons, List.prod_cons, List.finRange_zero, List.map_nil,
      List.prod_nil, mul_one] at hcc
    simpa [Mod.basis, mul_assoc] using hcc
  · intro j i
    obtain ⟨hord, hconjs⟩ := hacts (m.acts.get j) (List.get_mem _ _)
    have hu : HasOrd C [(m.basis i, 1)] := hBasisOrd _ (by
      intro q hq
      simp only [List.mem_singleton] at hq
      rw [hq]
      fin_cases i <;> simp [Mod.basis])
    have hw : HasOrd C (m.col (m.acts.get j) i) := hBasisOrd _ (by simp [Mod.col])
    have h := regUnit_conj Sp hC (hconjs i) hord hu hw
    simp only [wordUnit, Mod.col, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, pow_one] at h
    have key : ∀ (k : Fin 3) (e : ℕ), regUnit Sp hC (m.basis k) ^ e =
        regUnit Sp hC (m.basis k) ^ ((e : ZMod p).val) := by
      intro k e
      rw [ZMod.val_natCast]
      exact pow_eq_pow_mod e (hpowb k)
    refine h.trans ?_
    have hl : ∀ f : Fin 3 → (certMonoid c d sA sB)ˣ,
        ((List.finRange 3).map f).prod = f 0 * (f 1 * f 2) := by
      intro f; simp [List.finRange_succ]
    rw [hl]
    simp only [actMat, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add, mul_one,
      Nat.reduceMul]
    have e0 := key 0 ((m.acts.get j).mat.getD i.val 0)
    have e1 := key 1 ((m.acts.get j).mat.getD (3 + i.val) 0)
    have e2 := key 2 ((m.acts.get j).mat.getD (6 + i.val) 0)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
    exact congrArg₂ (· * ·) e0 (congrArg₂ (· * ·) e1 e2)
  · intro g hg
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
    exact ⟨j, rfl, fun k i => rfl⟩


end Module

section Main


end Main

end CFSG.AGLEmbedding.R3
