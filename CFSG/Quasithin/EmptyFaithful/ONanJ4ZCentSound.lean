module

public import Certificates.Certificate9685
public import Certificates.Certificate9686

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.ZCent
open CFSG.Sporadic.J4.QT (Mx Mx_injective)
open CFSG.Quasithin.J4M2 (gE gmats gmats_size M2 cE Kgrp Qgrp rho sigPerm phiRN Mx_gE gE_mem_M2
  rowsMatrix_inv_of_mul rho_gE_perm)
open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat (p5Gens)
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat (RN rawIsEnc closedH elts eqCert
  closure_eq_of_eqCert card_closure_of_closedH mem_closure_iff_H)
open scoped commutatorElement

theorem r0Facts_spec : R0Facts :=
  Certificates.certificate9685

theorem b0Facts_spec : B0Facts :=
  Certificates.certificate9686

@[expose] def SD : Setup := setup gmats


theorem g0W_ok : ∀ w ∈ g0W, WordOK 32 w := by
  unfold WordOK
  decide

theorem rW_ok : ∀ w ∈ rW, WordOK 16 w := by
  unfold WordOK
  decide

theorem tW_ok : ∀ w ∈ tW, WordOK 16 w := by
  unfold WordOK
  decide


theorem getD_ok {k : ℕ} {L : List (List ℤ)} (h : ∀ w ∈ L, WordOK k w) (i : ℕ) :
    WordOK k (L.getD i []) := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro l hl
    simp at hl

theorem b0El_mem {i : ℕ} (hi : i < 16) : b0El i ∈ B0 :=
  Subgroup.subset_closure (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem evalW_b0El_mem {w : List ℤ} (hw : WordOK 16 w) : evalW b0El w ∈ B0 :=
  mem_of_evalW b0El (fun _ hn => b0El_mem hn) hw


theorem R0_le_B0 : R0 ≤ B0 := by
  rw [R0, Subgroup.closure_le]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact evalW_b0El_mem (getD_ok rW_ok j)


section Generators

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb


end Generators


section Generators2

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb


end Generators2


section Words2

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb


end Words2


section RProd

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb


end RProd


theorem tEl_zero : tEl 0 = 1 := rfl


section R0

variable (hR : R0Facts)
include hR

theorem card_R0 : Nat.card R0 = 2 ^ 15 := hR.card_R0

end R0

section Normal

variable (hR : R0Facts)
include hR

theorem B0_le_normalizer_R0 : B0 ≤ Subgroup.normalizer (R0 : Set J) := fun _ hb =>
  Subgroup.mem_normalizer_fintype fun r hr => hR.normal _ hb r hr


theorem B0_subset_TR : ∀ x ∈ B0, ∃ i < 60, ∃ r ∈ R0, x = tEl i * r := hR.cover

theorem card_B0_le : Nat.card B0 ≤ 60 * 2 ^ 15 := by
  have h : ∀ x : B0, ∃ p : Fin 60 × R0, (x : J) = tEl p.1 * (p.2 : J) := by
    intro x
    obtain ⟨i, hi, r, hr, hxr⟩ := B0_subset_TR hR x x.2
    exact ⟨(⟨i, hi⟩, ⟨r, hr⟩), hxr⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [hf x, hf y, hxy]
  calc Nat.card B0 ≤ Nat.card (Fin 60 × R0) := Nat.card_le_card_of_injective f hinj
    _ = 60 * 2 ^ 15 := by
      rw [Nat.card_prod, card_R0 hR]
      simp

theorem center_R0 {x : J} (hx : x ∈ R0) (hc : ∀ r ∈ R0, x * r = r * x) :
    ∀ b ∈ B0, x * b = b * x :=
  hR.center x hx hc

end Normal


section Perfect

variable (hM : MatFacts) (hb : chkBase gmats SD = true) (hP : chkPerf SD = true)
include hM hb hP


end Perfect


section KNorm

variable (hM : MatFacts) (hb : chkBase gmats SD = true) (hK : chkK gmats SD = true)
include hM hb hK


end KNorm

theorem evalW_congr {G : Type*} [Group G] {g₁ g₂ : ℕ → G} {k : ℕ} (h : ∀ n < k, g₁ n = g₂ n)
    {w : List ℤ} (hw : WordOK k w) : evalW g₁ w = evalW g₂ w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalW_cons, evalW_cons, ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    have hl := hw l List.mem_cons_self
    unfold letterOf
    split_ifs
    · rw [h _ (by omega)]
    · rw [h _ (by omega)]

section Rho

variable
  (hF : J4Facts)

@[expose] noncomputable def rhoJ (x : J) : Equiv.Perm (Fin 77) := by
  classical
  exact if h : x ∈ M2 then rho hF ⟨x, h⟩ else 1

theorem rhoJ_of_mem {x : J} (h : x ∈ M2) : rhoJ hF x = rho hF ⟨x, h⟩ := by
  unfold rhoJ
  simp only [h, ↓reduceDIte]

theorem rhoJ_mul {x y : J} (hx : x ∈ M2) (hy : y ∈ M2) :
    rhoJ hF (x * y) = rhoJ hF x * rhoJ hF y := by
  rw [rhoJ_of_mem hF (Subgroup.mul_mem _ hx hy), rhoJ_of_mem hF hx, rhoJ_of_mem hF hy,
    ← map_mul]
  rfl

theorem rhoJ_inv {x : J} (hx : x ∈ M2) : rhoJ hF x⁻¹ = (rhoJ hF x)⁻¹ := by
  rw [rhoJ_of_mem hF (Subgroup.inv_mem _ hx), rhoJ_of_mem hF hx, ← map_inv]
  rfl

theorem rhoJ_one : rhoJ hF 1 = 1 := by
  rw [rhoJ_of_mem hF (Subgroup.one_mem _)]
  exact map_one _

theorem rhoJ_evalW {gens : ℕ → J} {k : ℕ} (hg : ∀ n < k, gens n ∈ M2) {w : List ℤ}
    (hw : WordOK k w) : evalW gens w ∈ M2 ∧ rhoJ hF (evalW gens w) = evalW (rhoJ hF ∘ gens) w := by
  induction w with
  | nil => exact ⟨Subgroup.one_mem _, by simp [evalW_nil, rhoJ_one]⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hl := hw l List.mem_cons_self
    have hlm : letterOf gens l ∈ M2 := letterOf_mem gens hg hl.1 hl.2
    have hlr : rhoJ hF (letterOf gens l) = letterOf (rhoJ hF ∘ gens) l := by
      unfold letterOf
      by_cases h : 0 < l
      · simp only [h, ↓reduceIte, Function.comp]
      · simp only [h, ↓reduceIte, Function.comp]
        exact rhoJ_inv hF (hg _ (by omega))
    refine ⟨?_, ?_⟩
    · rw [evalW_cons]
      exact Subgroup.mul_mem _ hlm ih1
    · rw [evalW_cons, evalW_cons, rhoJ_mul hF hlm ih1, ih2, hlr]

end Rho

section RhoGens

theorem gE_mem_M2_of_lt
    (hM : MatFacts) {n : ℕ} (hn : n < 32) : gE n ∈ M2 := gE_mem_M2 hM hn

theorem rhoJ_gE
    (hF : J4Facts) {n : ℕ} (hn : n < 32) :
    rhoJ hF (gE n) = sigPerm n := by
  rw [rhoJ_of_mem hF (gE_mem_M2 hF.mat hn)]
  exact rho_gE_perm hF hn

theorem g0W_pos : ∀ w ∈ g0W, ∀ l ∈ w, 0 < l := by decide

theorem b0Perm_eq (i : ℕ) : b0Perm i = evalW sigPerm (g0W.getD i []) := by
  have hpos : ∀ l ∈ g0W.getD i [], 0 < l := by
    by_cases hi : i < g0W.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact g0W_pos _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      intro l hl
      simp at hl
  have hmap : (g0W.getD i []).map (fun l => sigPerm (l.toNat - 1)) =
      (g0W.getD i []).map (letterOf sigPerm) :=
    List.map_congr_left fun l hl => by
      unfold letterOf
      simp only [hpos l hl, ↓reduceIte]
  unfold b0Perm evalW
  exact congrArg List.prod hmap

theorem b0El_mem_M2
    (hM : MatFacts) (i : ℕ) : b0El i ∈ M2 :=
  mem_of_evalW gE (fun _ hn => gE_mem_M2_of_lt hM hn) (getD_ok g0W_ok i)

theorem rhoJ_b0El
    (hF : J4Facts) (i : ℕ) : rhoJ hF (b0El i) = b0Perm i := by
  have h := (rhoJ_evalW hF (gens := gE) (k := 32) (fun _ hn => gE_mem_M2_of_lt hF.mat hn)
    (getD_ok g0W_ok i)).2
  rw [b0Perm_eq]
  unfold b0El
  rw [h]
  exact evalW_congr (fun n hn => rhoJ_gE hF hn) (getD_ok g0W_ok i)

theorem rhoJ_evalW_b0El
    (hF : J4Facts) {w : List ℤ} (hw : WordOK 16 w) :
    evalW b0El w ∈ M2 ∧ rhoJ hF (evalW b0El w) = wordPerm w := by
  have h := rhoJ_evalW hF (gens := b0El) (k := 16) (fun n _ => b0El_mem_M2 hF.mat n) hw
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hc : evalW (rhoJ hF ∘ b0El) w = evalW b0Perm w := by
    refine evalW_congr (fun n hn => ?_) hw
    exact rhoJ_b0El hF n
  rw [hc]
  rfl

end RhoGens

section RhoGroups

variable (hρ : B0Facts)
include hρ

theorem closure_b0Perms_eq : Subgroup.closure {p | p ∈ b0Perms} = LamP := hρ.closure_b0

theorem card_LamP : Nat.card LamP = 960 := hρ.card_LamP

theorem tPerm_not_mem_P2 {i : ℕ} (hi : i < 60) (hi0 : i ≠ 0) : tPerm i ∉ P2 :=
  hρ.tPerm_not i hi hi0

end RhoGroups

section RhoB0

variable
  (hF : J4Facts)
include hF

omit
  hF in
theorem B0_le_M2 (hM : MatFacts) : B0 ≤ M2 := by
  rw [B0, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact b0El_mem_M2 hM i

omit
  hF in
theorem R0_le_M2 (hM : MatFacts) : R0 ≤ M2 := R0_le_B0.trans (B0_le_M2 hM)

theorem rhoJ_tEl (i : ℕ) : rhoJ hF (tEl i) = tPerm i :=
  (rhoJ_evalW_b0El hF (getD_ok tW_ok i)).2

theorem tEl_mem_M2 (i : ℕ) : tEl i ∈ M2 := (rhoJ_evalW_b0El hF (getD_ok tW_ok i)).1

theorem rhoJ_mem_closure_b0Perms {x : J} (hx : x ∈ B0) :
    rhoJ hF x ∈ Subgroup.closure {p | p ∈ b0Perms} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    rw [rhoJ_b0El hF]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨i, hi, rfl⟩)
  | one => rw [rhoJ_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rw [rhoJ_mul hF (B0_le_M2 hF.mat hx) (B0_le_M2 hF.mat hy)]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    rw [rhoJ_inv hF (B0_le_M2 hF.mat hx)]
    exact Subgroup.inv_mem _ ih

theorem rhoJ_mem_P2 {x : J} (hx : x ∈ R0) : rhoJ hF x ∈ P2 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hj' : j < rW.length := by simpa [rW] using List.mem_range.1 hj
    have h := (rhoJ_evalW_b0El hF (getD_ok rW_ok j)).2
    show rhoJ hF (evalW b0El (rW.getD j [])) ∈ P2
    rw [h]
    refine Subgroup.subset_closure (List.mem_map.2 ⟨rW.getD j [], ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  | one => rw [rhoJ_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rw [rhoJ_mul hF (R0_le_M2 hF.mat hx) (R0_le_M2 hF.mat hy)]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    rw [rhoJ_inv hF (R0_le_M2 hF.mat hx)]
    exact Subgroup.inv_mem _ ih

end RhoB0

section RhoB

variable
  (hF : J4Facts)

@[expose] noncomputable def rhoB (H : Subgroup J) : Subgroup (Equiv.Perm (Fin 77)) :=
  (H.subgroupOf M2).map (rho hF)

theorem mem_rhoB {H : Subgroup J} {p : Equiv.Perm (Fin 77)} :
    p ∈ rhoB hF H ↔ ∃ x ∈ H, ∃ hx : x ∈ M2, rho hF ⟨x, hx⟩ = p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, y.2, rfl⟩
  · rintro ⟨x, hx, hxM, rfl⟩
    exact ⟨⟨x, hxM⟩, hx, rfl⟩

include hF

theorem rhoB_B0 (hρ : B0Facts) : rhoB hF B0 = LamP := by
  rw [← closure_b0Perms_eq hρ]
  apply le_antisymm
  · intro p hp
    obtain ⟨x, hx, hxM, rfl⟩ := (mem_rhoB hF).1 hp
    rw [← rhoJ_of_mem hF hxM]
    exact rhoJ_mem_closure_b0Perms hF hx
  · rw [Subgroup.closure_le]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    refine (mem_rhoB hF).2 ⟨b0El i, b0El_mem (List.mem_range.1 hi), b0El_mem_M2 hF.mat i, ?_⟩
    rw [← rhoJ_of_mem hF (b0El_mem_M2 hF.mat i), rhoJ_b0El hF]

theorem mem_R0_of_rhoJ_eq_one (hρ : B0Facts) (hR : R0Facts) {x : J}
    (hx : x ∈ B0) (h1 : rhoJ hF x = 1) : x ∈ R0 := by
  obtain ⟨i, hi, r, hr, rfl⟩ := B0_subset_TR hR x hx
  rw [rhoJ_mul hF (tEl_mem_M2 hF i) (R0_le_M2 hF.mat hr), rhoJ_tEl hF] at h1
  have hP : tPerm i ∈ P2 := by
    have : tPerm i = (rhoJ hF r)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ (rhoJ_mem_P2 hF hr)
  by_cases hi0 : i = 0
  · subst hi0
    rw [tEl_zero, one_mul]
    exact hr
  · exact absurd hP (tPerm_not_mem_P2 hρ hi hi0)

end RhoB

end CFSG.Quasithin.J4ZCent
