module

public import Certificates.Data.Kernel.EvenSporM22.M22StdDefs
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Check
public import CFSG.Certificates.Kernel.LocalQTCovEqns

import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.LocalQTCovGe
import CFSG.Certificates.Kernel.LocalQTBaseWProved

namespace CFSG.KC.M22S.Pf

open CFSG.KC.LQT CFSG.KC.LQT.Cov CFSG.KC.M22S CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.QuasithinUnique.Ch1.TitsCover (formOf reduceF gePivots)
open CFSG.Monster.B.Co2 (Rep rep_compA rep_idA eqA_iff allLt_iff)
open CFSG.Monster.B.Co2.Native (eqA compA idA allLt isInvA invCand)
open CFSG.Sporadic.Mathieu (m22gA m22gB)
open CFSG.EvenSporadicStandard.M22Std

theorem getK_eq {α : Type} (l : List α) (i : ℕ) (d : α) :
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d := Perm.sgetK_eq l i d

theorem memL_iff (c : ℕ) : ∀ l : List ℕ, CFSG.KC.LQT.S.memL c l = true ↔ c ∈ l
  | [] => by simp [CFSG.KC.LQT.S.memL]
  | x :: l => by
    change CFSG.KC.Ord.orB (Nat.beq c x) (CFSG.KC.LQT.S.memL c l) = true ↔ _
    rw [CFSG.KC.LQT.P.orB_iff, Nat.beq_eq, memL_iff c l, List.mem_cons]

theorem iffB_iff (a b : Bool) : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem xorK_eq (F : List ℕ) : ∀ ks : List ℕ,
    xorK F ks = ks.foldr (fun k acc => F.getD k 0 ^^^ acc) 0
  | [] => rfl
  | k :: ks => by
    change Nat.xor (CFSG.KC.LQT.Syl.getK F k 0) (xorK F ks) = _
    rw [getK_eq, xorK_eq F ks, List.foldr_cons]
    rfl

theorem allBs_cons (b : Bool) (l : List Bool) :
    CFSG.KC.LQT.S.allBs (b :: l) = (b && CFSG.KC.LQT.S.allBs l) :=
  CFSG.KC.LQT.BW.Pf.allBs_cons b l

structure Parsed (cs : List Char) (D : CD) : Prop where
  pd : parseData (String.ofList cs) = Eqns.ofCD D
  xw : D.xw.length = 3
  wl : D.words.length = D.nV
  w3 : ∀ w ∈ D.words, ∀ l ∈ w, l < 3

theorem parsed {cs : List Char} {D : CD} (hp : parseCov cs = some D) : Parsed cs D := by
  obtain ⟨hxw, hwl, hw3, hpd⟩ := Parse.parseCov_sound hp
  exact ⟨hpd, hxw, hwl, hw3⟩

variable {cA cB : ℕ} {D : CD}

noncomputable abbrev elD (D : CD) (v : ℕ) : Equiv.Perm (Fin 22) :=
  (Eqns.ofCD D).tab.el (Eqns.ofCD D).x v

theorem codeE (hA : P.code m22gA = cA) (hB : P.code m22gB = cB) (hxw : D.xw.length = 3)
    (hwl : D.words.length = D.nV) {v : ℕ} (hv : v < D.nV) :
    CFSG.KC.LQT.Syl.getK (eltsOf cA cB D) v 0 = P.code (elD D v) := by
  rw [getK_eq]
  exact Perm.codes_E (d := Eqns.ofCD D) hA hB hxw rfl rfl rfl rfl hwl v hv

theorem codeX (hA : P.code m22gA = cA) (hB : P.code m22gB = cB) (hxw : D.xw.length = 3)
    {i : ℕ} (hi : i < 3) :
    CFSG.KC.LQT.Syl.getK (gensOf cA cB D) i (CFSG.KC.LQT.P.one 22) =
      P.code ((Eqns.ofCD D).x (fo i)) := by
  have h := Perm.genX_code (d := Eqns.ofCD D) hA hB hxw rfl rfl rfl i
  rw [Nat.mod_eq_of_lt hi] at h
  exact h

theorem rep_elD {v : ℕ} (hv : v < D.nV) : Rep 22 ((Eqns.ofCD D).elaTab[v]!) (elD D v) :=
  (Eqns.ofCD D).rep_el (fun i => (Eqns.ofCD D).xa_rep i) hv

theorem mulc (σ τ : Equiv.Perm (Fin 22)) : CFSG.KC.LQT.P.mul 22 (P.code σ) (P.code τ) = P.code (σ * τ) :=
  P.code_mul (by omega) σ τ


theorem beqc (σ τ : Equiv.Perm (Fin 22)) : Nat.beq (P.code σ) (P.code τ) = true ↔ σ = τ :=
  P.beq_code (by omega) σ τ

theorem beq1 (σ : Equiv.Perm (Fin 22)) :
    Nat.beq (P.code σ) (CFSG.KC.LQT.P.one 22) = true ↔ σ = 1 := by
  rw [P.code_one, beqc]


theorem contains_iff {v : ℕ} {l : List ℕ} : l.contains v = true ↔ v ∈ l := by
  simp


theorem posK_map (W : List ℕ) : (posK W).map (fun l => (fo l.1, l.2)) = posW (W.map fo) := by
  simp only [posK, posW, List.map_map, Function.comp_def]

theorem invWK_map (W : List ℕ) : (invWK W).map (fun l => (fo l.1, l.2)) = invW (W.map fo) := by
  simp only [invWK, invW, List.map_map, Function.comp_def, List.map_reverse]

theorem word_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (k : ℕ) :
    ∀ l ∈ CFSG.KC.LQT.Syl.getK D.words k [], l < 3 := by
  intro l hl
  rw [getK_eq, List.getD_eq_getElem?_getD] at hl
  cases h : D.words[k]? with
  | none => simp [h] at hl
  | some w =>
    rw [h, Option.getD_some] at hl
    exact hw w (List.mem_of_getElem? h) l hl

theorem sqWK_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (v₁ v₂ : ℕ) :
    ∀ l ∈ sqWK D v₁ v₂, l.1 < 3 := by
  intro l hl
  simp only [sqWK, List.append_eq, List.mem_append, posK, invWK, List.mem_map,
    List.mem_reverse] at hl
  rcases hl with ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩ <;>
    exact word_lt hw _ x hx

theorem sqWK_map (v₁ v₂ : ℕ) :
    (sqWK D v₁ v₂).map (fun l => (fo l.1, l.2)) = sqWalk (Eqns.ofCD D) v₁ v₂ := by
  simp only [sqWK, sqWalk, List.append_eq, List.map_append, posK_map, invWK_map,
    Eqns.tab_word_ofCD, getK_eq]

theorem walk_sq (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (v₁ v₂ : ℕ) :
    walkK D 0 (sqWK D v₁ v₂) =
      (formOf ((Eqns.ofCD D).tab.walkEdges 0 (sqWalk (Eqns.ofCD D) v₁ v₂)),
        (Eqns.ofCD D).tab.walkEnd 0 (sqWalk (Eqns.ofCD D) v₁ v₂)) := by
  rw [Eqns.walkK_ofCD D 0 _ (sqWK_lt hw v₁ v₂), sqWK_map]

theorem forms_split (d : CovData) : d.forms = forms0 d ++ d.free.map (Eqn.form d ∘ Eqn.free) := by
  rw [CovData.forms, eqns_eq_eqns0_append, List.map_append, List.map_map, forms0]

theorem hint_sound (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) {ks : List ℕ} {t : ℕ}
    (hf : formsK D (formsOf D) = true) (hh : hintK D (formsOf D) ks t = true) :
    reduceF (gePivots ((Eqns.ofCD D).M + 5) (Eqns.ofCD D).M (forms0 (Eqns.ofCD D)))
      ((Eqns.ofCD D).M + 5) t = 0 := by
  have hF : formsOf D = (Eqns.ofCD D).forms := Eqns.eqnsK_forms hw
  rw [hintK, CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.allL_iff, Nat.beq_eq, xorK_eq] at hh
  obtain ⟨hks, hx⟩ := hh
  rw [formsK, CFSG.KC.LQT.P.allL_iff] at hf
  have hlen : (formsOf D).length = (forms0 (Eqns.ofCD D)).length + D.free.length := by
    rw [hF, forms_split, List.length_append, List.length_map]
    rfl
  have hget : ∀ k ∈ ks, (formsOf D).getD k 0 = (forms0 (Eqns.ofCD D)).getD k 0 := by
    intro k hk
    have := hks k hk
    rw [Nat.blt_eq, Perm.slenK_eq, Perm.slenK_eq, Nat.sub_eq] at this
    rw [hF, forms_split, List.getD_append _ _ _ _ (by omega)]
  have hx' : ks.foldr (fun k acc => (forms0 (Eqns.ofCD D)).getD k 0 ^^^ acc) 0 = t := by
    rw [← hx]
    clear hx
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      simp only [List.foldr_cons]
      rw [hget k List.mem_cons_self, ih (fun k' h => hks k' (List.mem_cons_of_mem _ h))
        (fun k' h => hget k' (List.mem_cons_of_mem _ h))]
  rw [← hx']
  refine Ge.reduceF_gePivots_xor (fun f hf0 => ?_) (by omega) ks
  have hmem : f ∈ formsOf D := by rw [hF, forms_split]; exact List.mem_append_left _ hf0
  have := hf f hmem
  rw [Nat.blt_eq, Perm.slenK_eq] at this
  have hM : (Eqns.ofCD D).M = 3 * D.nV + 32 * D.blocks.length := by
    simp [CovData.M, Eqns.ofCD]
  rw [hM]
  exact this

end CFSG.KC.M22S.Pf

public section

namespace CFSG.KC.M22S

open CFSG.KC.LQT CFSG.KC.LQT.Cov CFSG.KC.M22S.Pf CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.QuasithinUnique.Ch1.TitsCover (formOf reduceF gePivots)
open CFSG.Monster.B.Co2 (Rep rep_compA rep_idA eqA_iff allLt_iff)
open CFSG.Monster.B.Co2.Native (eqA compA idA allLt isInvA invCand)
open CFSG.Sporadic.Mathieu (m22gA m22gB)
open CFSG.EvenSporadicStandard.M22Std

theorem sqHK_sound {cA cB : ℕ} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    {cs : List Char} {H : List ℕ} {v₁ v₂ : ℕ} (h : sqHK cA cB cs H v₁ v₂ = true) :
    sqCheck (parseData (String.ofList cs)) v₁ v₂ = true := by
  rw [sqHK] at h
  cases hp : parseCov cs with
  | none =>
    rw [hp] at h
    exact absurd h Bool.false_ne_true
  | some D =>
    rw [hp] at h
    change sqD cA cB H v₁ v₂ D = true at h
    obtain ⟨hpd, hxw, hwl, hw3⟩ := parsed hp
    rw [hpd]
    rw [sqD, CFSG.KC.LQT.P.letB_eq] at h
    simp only [allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true] at h
    obtain ⟨hend, hf, hh, hv, hsq, hne⟩ := h
    rw [walk_sq hw3] at hend hh
    rw [Nat.blt_eq] at hv
    rw [codeE hA hB hxw hwl hv, mulc, mulc, beq1] at hsq
    rw [codeE hA hB hxw hwl hv, mulc, CFSG.KC.LQT.P.notB_iff, beq1] at hne
    have hr := rep_elD (D := D) hv
    unfold sqCheck
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
    refine ⟨⟨⟨⟨Nat.beq_eq.mp hend, hint_sound hw3 hf hh⟩, hv⟩,
      (eqA_iff (rep_compA (rep_compA hr hr) (rep_compA hr hr)) rep_idA).2 hsq⟩, ?_⟩
    cases he : eqA 22 (compA 22 (Eqns.ofCD D).elaTab[v₁]! (Eqns.ofCD D).elaTab[v₁]!) (idA 22)
    · rfl
    · exact absurd ((eqA_iff (rep_compA hr hr) rep_idA).1 he) hne

theorem twHK_sound {cA cB : ℕ} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    {cs : List Char} {H : List (List ℕ)} (h : twHK cA cB cs H = true) :
    twCheck (parseData (String.ofList cs)) = true := by
  rw [twHK] at h
  cases hp : parseCov cs with
  | none =>
    rw [hp] at h
    exact absurd h Bool.false_ne_true
  | some D =>
    rw [hp] at h
    change CFSG.KC.LQT.P.letB _ _ = true at h
    obtain ⟨hpd, hxw, hwl, hw3⟩ := parsed hp
    rw [hpd]
    rw [CFSG.KC.LQT.P.letB_eq, twD] at h
    simp only [allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true] at h
    obtain ⟨hinv, hcen, hroot, hf, -, hwalk, h79, hzz, hz1, hzc⟩ := h
    rw [Nat.blt_eq] at h79
    have hx : ∀ i, Rep 22 ((Eqns.ofCD D).xa i) ((Eqns.ofCD D).x i) := fun i => (Eqns.ofCD D).xa_rep i
    have hE : ∀ {v}, v < D.nV → CFSG.KC.LQT.Syl.getK (eltsOf cA cB D) v 0 = P.code (elD D v) :=
      fun hv => codeE hA hB hxw hwl hv
    have hX : ∀ {i}, i < 3 → CFSG.KC.LQT.Syl.getK (gensOf cA cB D) i (CFSG.KC.LQT.P.one 22) =
        P.code ((Eqns.ofCD D).x (fo i)) := fun hi => codeX hA hB hxw hi
    have hz : Rep 22 (compA 22 (Eqns.ofCD D).elaTab[79]! (Eqns.ofCD D).elaTab[79]!)
        (elD D 79 * elD D 79) := rep_compA (rep_elD h79) (rep_elD h79)
    simp only [hE h79, mulc] at hzz hz1 hzc hcen hroot
    unfold twCheck
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    ·
      unfold twInv
      rw [allLt_iff]
      intro i hi
      have := (Perm.allLtK_iff _ _).1 hinv i hi
      rw [hX hi, mulc, beq1] at this
      exact (eqA_iff (rep_compA (hx _) (hx _)) rep_idA).2 this
    ·
      unfold twCenter
      rw [allLt_iff]
      intro v hv
      have := (Perm.allLtK_iff _ _).1 hcen v hv
      rw [CFSG.KC.LQT.P.letB_eq, hE hv, CFSG.KC.LQT.P.orB_iff, CFSG.KC.LQT.P.orB_iff,
        CFSG.KC.LQT.P.notB_iff, Perm.allLtK_iff, beq1, beqc] at this
      have hr := rep_elD (D := D) hv
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true', eqA_iff hr rep_idA, eqA_iff hr hz]
      rcases this with hn | h1 | hz'
      · left
        left
        rw [Bool.eq_false_iff]
        intro hall
        apply hn
        intro i hi
        rw [hX hi, mulc, mulc, beqc]
        exact (eqA_iff (rep_compA hr (hx _)) (rep_compA (hx _) hr)).1 (allLt_iff.1 hall i hi)
      · left
        right
        exact h1
      · right
        exact hz'
    ·
      unfold twRoots
      rw [allLt_iff]
      intro v hv
      have := (Perm.allLtK_iff _ _).1 hroot v hv
      rw [CFSG.KC.LQT.P.letB_eq, hE hv, mulc, iffB_iff, beqc, memL_iff] at this
      have hr := rep_elD (D := D) hv
      rw [beq_iff_eq, Bool.eq_iff_iff, eqA_iff (rep_compA hr hr) hz, contains_iff]
      exact this
    ·
      unfold twWalks
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      intro v hv
      have hv' : v ∈ aVK := hv
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hv'
      have hj' : j < (CFSG.KC.LQT.Syl.lenK aVK) := by rw [Perm.slenK_eq]; exact hj
      have := (Perm.allLtK_iff _ _).1 hwalk j hj'
      rw [twWalkD, getK_eq aVK j 0, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj, Option.getD_some] at this
      simp only [allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true,
        Nat.blt_eq] at this
      obtain ⟨hvn, hend, hh⟩ := this
      rw [walk_sq hw3] at hend hh
      exact ⟨⟨hvn, Nat.beq_eq.mp hend⟩, hint_sound hw3 hf hh⟩
    ·
      unfold twZ
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      rw [beq1] at hzz
      rw [CFSG.KC.LQT.P.notB_iff, beq1] at hz1
      refine ⟨⟨⟨h79, (eqA_iff (rep_compA hz hz) rep_idA).2 hzz⟩, ?_⟩, ?_⟩
      · cases he : eqA 22 (compA 22 (Eqns.ofCD D).elaTab[79]! (Eqns.ofCD D).elaTab[79]!) (idA 22)
        · rfl
        · exact absurd ((eqA_iff hz rep_idA).1 he) hz1
      · rw [allLt_iff]
        intro v hv
        have := (Perm.allLtK_iff _ _).1 hzc v hv
        rw [CFSG.KC.LQT.P.letB_eq, hE hv, mulc, mulc, beqc] at this
        have hr := rep_elD (D := D) hv
        exact (eqA_iff (rep_compA hz hr) (rep_compA hr hz)).2 this


end CFSG.KC.M22S

end
