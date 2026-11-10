module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AFix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.J4Loc (z0)

theorem burnsideJ4NP_orbits_eq : orbits = [orbits.getD 0 (1, [], []), orbits.getD 1 (3, [], [])] :=
  rfl

theorem burnsideJ4NP_orbit_root_zero : (orbits.getD 0 (1, [], [])).1 = 1 := rfl

theorem burnsideJ4NP_orbit_root_one : (orbits.getD 1 (3, [], [])).1 = 3 := rfl

theorem burnsideJ4NP_mem_zMasks_or_isConj (hF : J4Facts) {n : ℕ}
    (hn : n < 2048) (hn0 : n ≠ 0) : n ∈ zMasks ∨ IsConj (eta uJ 11 1) (eta uJ 11 n) := by
  obtain ⟨o, ho, p, hp, rfl⟩ := orbit_cover n (by simpa using hn) hn0
  have ho' := ho
  rw [burnsideJ4NP_orbits_eq, List.mem_cons, List.mem_singleton] at ho'
  rcases ho' with rfl | rfl
  · right
    have h := eta_conj_orbit hF ho hp
    rwa [burnsideJ4NP_orbit_root_zero] at h
  · left
    exact List.mem_map_of_mem hp

theorem burnsideJ4NP_isConj_eta_three (hF : J4Facts) {n : ℕ}
    (hn : n ∈ zMasks) : IsConj (eta uJ 11 3) (eta uJ 11 n) := by
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (orbits.getD 1 (3, [], [])).2.1, p.1 = n := by
    simpa [zMasks] using hn
  have ho : orbits.getD 1 (3, [], []) ∈ orbits := by
    rw [burnsideJ4NP_orbits_eq]; simp
  have h := eta_conj_orbit hF ho hp
  rwa [burnsideJ4NP_orbit_root_one] at h

theorem burnsideJ4NP_mem_zMasks_1131 :
    (1131 : ℕ) ∈ zMasks := by
  rcases burnsideJ4NP_mem_zMasks_or_isConj j4Facts (n := 1131) (by norm_num) (by norm_num) with
    h | h
  · exact h
  · exact absurd h burnsideJ4NP_not_isConj_eta_one_z0

theorem burnsideJ4NP_isConj_z0_iff
    {n : ℕ} (hn : n < 2048) (hn0 : n ≠ 0) :
    IsConj (eta uJ 11 n) z0 ↔ n ∈ zMasks := by
  have hF := j4Facts
  constructor
  · intro h
    rcases burnsideJ4NP_mem_zMasks_or_isConj hF hn hn0 with h1 | h1
    · exact h1
    · exact absurd (h1.trans h) burnsideJ4NP_not_isConj_eta_one_z0
  · intro h
    exact (burnsideJ4NP_isConj_eta_three hF h).symm.trans
      (burnsideJ4NP_isConj_eta_three hF burnsideJ4NP_mem_zMasks_1131)

theorem burnsideJ4NP_Kel_zero : Kel 0 = 1 := by
  unfold Kel
  rw [show pcSeq 0 = [] by decide]
  rfl

theorem burnsideJ4NP_tabE_zero : tabE 0 = idT := by
  unfold tabE
  rw [show pcSeq 0 = [] by decide]
  rfl

theorem burnsideJ4NP_tabE_ne_idT {e : ℕ} (he : e < 1024)
    (he0 : e ≠ 0) : tabE e ≠ idT := by
  intro h
  have hnd := tabL_nodup
  unfold tabL at hnd
  have h0 : seqT (pcSeq e) = seqT (pcSeq 0) := by
    have h' : tabE e = tabE 0 := by rw [h, burnsideJ4NP_tabE_zero]
    exact h'
  exact he0 (List.inj_on_of_nodup_map hnd (List.mem_range.2 he) (List.mem_range.2 (by norm_num)) h0)

theorem burnsideJ4NP_conj_class_rep
    (hF : J4Facts) {c e r m : ℕ} (he : e < 1024) (hm : m < 2048)
    (hmy : m ^^^ actT (tabE e) m = c ^^^ r) :
    eta uJ 11 m * (eta uJ 11 c * Kel e) * (eta uJ 11 m)⁻¹ = eta uJ 11 r * Kel e := by
  have hM := hF.mat
  have hK := Acts_Kel hM he
  have hηinv : (eta uJ 11 m)⁻¹ = eta uJ 11 m :=
    inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) m)
  rw [hηinv]
  have hKm : Kel e * eta uJ 11 m = eta uJ 11 (actT (tabE e) m) * Kel e := by
    have := hK.2 m (by simpa using hm)
    rwa [mul_inv_eq_iff_eq_mul] at this
  calc eta uJ 11 m * (eta uJ 11 c * Kel e) * eta uJ 11 m
      = eta uJ 11 m * eta uJ 11 c * (Kel e * eta uJ 11 m) := by group
    _ = eta uJ 11 m * eta uJ 11 c * (eta uJ 11 (actT (tabE e) m) * Kel e) := by rw [hKm]
    _ = (eta uJ 11 m * eta uJ 11 c * eta uJ 11 (actT (tabE e) m)) * Kel e := by group
    _ = eta uJ 11 (m ^^^ c ^^^ actT (tabE e) m) * Kel e := by
      rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
    _ = eta uJ 11 r * Kel e := by
      have : m ^^^ c ^^^ actT (tabE e) m = r := by
        have h1 : m ^^^ c ^^^ actT (tabE e) m = c ^^^ (m ^^^ actT (tabE e) m) := by
          rw [Nat.xor_comm m c, Nat.xor_assoc]
        rw [h1, hmy, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [this]

theorem burnsideJ4NP_isConj_of_class
    (hF : J4Facts) {c e : ℕ} (he : e < 1024)
    (hsq : (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e) = 1)
    {x : ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)} (hx : x ∈ invData) (hxe : x.1 = e)
    {y : ℕ × ℕ × ℕ × ℕ} (hy : y ∈ x.2.2) {m : ℕ} (hm : m < 2048)
    (hmy : m ^^^ actT (tabE e) m = c ^^^ y.1) :
    IsConj (eta uJ 11 y.2.2.1) (eta uJ 11 c * Kel e) ∧ 0 < y.2.2.1 ∧ y.2.2.1 < 2048 := by
  have hM := hF.mat
  obtain ⟨-, -, -, -, hfuse⟩ := invOKT_spec (invAllOK_spec x hx)
  set r := eta uJ 11 c * Kel e with hre
  have hconj : eta uJ 11 m * r * (eta uJ 11 m)⁻¹ = eta uJ 11 y.1 * Kel e :=
    burnsideJ4NP_conj_class_rep hF he hm hmy
  have hyf := hfuse y hy
  rw [hxe] at hyf
  obtain ⟨hg3, hn0, hn, hodd, hpow⟩ := fuseOKT_spec hyf
  have hR2 : (eta uJ 11 y.1 * Kel e) * (eta uJ 11 y.1 * Kel e) = 1 := by
    rw [← hconj]
    calc eta uJ 11 m * r * (eta uJ 11 m)⁻¹ * (eta uJ 11 m * r * (eta uJ 11 m)⁻¹)
        = eta uJ 11 m * (r * r) * (eta uJ 11 m)⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  set g := gEl y.2.1 with hgdef
  set n := y.2.2.1 with hndef
  have hee : (g * eta uJ 11 n * g⁻¹) * (g * eta uJ 11 n * g⁻¹) = 1 := by
    calc (g * eta uJ 11 n * g⁻¹) * (g * eta uJ 11 n * g⁻¹)
        = g * (eta uJ 11 n * eta uJ 11 n) * g⁻¹ := by group
      _ = 1 := by rw [eta_sq (elem_uJ hM)]; group
  have hMR : Mx (eta uJ 11 y.1 * Kel e) = rowsMatrix (mulRows (etaR y.1) (KelRows e)) := by
    rw [map_mul, Mx_etaR hM, Mx_Kel hM he, rowsMatrix_mulRows]
  have hMe : Mx (g * eta uJ 11 n * g⁻¹) =
      rowsMatrix (mulRows (mulRows (gMat y.2.1) (etaR n)) (gInv y.2.1)) := by
    rw [map_mul, map_mul, (Mx_gEl hM hg3).1, (Mx_gEl hM hg3).2, Mx_etaR hM, rowsMatrix_mulRows,
      rowsMatrix_mulRows]
  have hpowJ : ((eta uJ 11 y.1 * Kel e) * (g * eta uJ 11 n * g⁻¹)) ^ y.2.2.2 = 1 := by
    apply Mx_injective
    have h1 := congrArg rowsMatrix (eqRows_iff.1 hpow)
    rw [rowsMatrix_powRows, rowsMatrix_idRows] at h1
    rw [map_pow, map_mul, hMR, hMe, map_one Mx, ← rowsMatrix_mulRows]
    exact h1
  obtain ⟨k, hk⟩ := @dihedral_conj_odd J inferInstance (eta uJ 11 y.1 * Kel e)
    (g * eta uJ 11 n * g⁻¹) hR2 hee y.2.2.2 (Nat.odd_iff.2 hodd) hpowJ
  have h1 : IsConj (eta uJ 11 n) (g * eta uJ 11 n * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have h2 : IsConj (eta uJ 11 y.1 * Kel e) (g * eta uJ 11 n * g⁻¹) := isConj_iff.2 ⟨k, hk⟩
  have h3 : IsConj r (eta uJ 11 y.1 * Kel e) := isConj_iff.2 ⟨eta uJ 11 m, hconj⟩
  exact ⟨(h1.trans h2.symm).trans h3.symm, hn0, hn⟩

theorem burnsideJ4NP_classOf_spec {c e : ℕ} {y : ℕ × ℕ × ℕ × ℕ}
    (h : burnsideJ4NP_classOf c e = some y) :
    ∃ x ∈ invData, x.1 = e ∧ y ∈ x.2.2 ∧ ∃ m < 2048, m ^^^ actT (tabE e) m = c ^^^ y.1 := by
  unfold burnsideJ4NP_classOf burnsideJ4NP_classOfWith at h
  split at h
  · exact absurd h (by simp)
  · rename_i x hx
    have hxe : x.1 = e := by simpa using List.find?_some hx
    have hyp := List.find?_some h
    rw [List.contains_iff_mem] at hyp
    unfold imSet at hyp
    rw [List.mem_eraseDups] at hyp
    obtain ⟨m, hm, hmeq⟩ := List.mem_map.1 hyp
    exact ⟨x, List.mem_of_find?_eq_some hx, hxe, List.mem_of_find?_eq_some h, m,
      List.mem_range.1 hm, hmeq⟩

theorem burnsideJ4NP_isInvE_of_sq
    (hF : J4Facts) {c e : ℕ} (he : e < 1024) (he0 : e ≠ 0)
    (hsq : (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e) = 1) : isInvE e = true := by
  have hM := hF.mat
  have hAct : Acts (eta uJ 11 c * Kel e) (tabE e) := Acts_eta_mul_Kel hM he
  have hAct2 := hAct.mul hAct
  rw [hsq] at hAct2
  have hcomp : compT (tabE e) (tabE e) = idT := hAct2.unique hM Acts.one
  simp [isInvE, hcomp, burnsideJ4NP_tabE_ne_idT he he0]

theorem burnsideJ4NP_classOf_isSome
    (hF : J4Facts) {c e : ℕ} (hc : c < 2048) (he : e < 1024)
    (he0 : e ≠ 0) (hsq : (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e) = 1) :
    ∃ y, burnsideJ4NP_classOf c e = some y := by
  have hM := hF.mat
  set r := eta uJ 11 c * Kel e with hre
  have hinv : isInvE e = true := burnsideJ4NP_isInvE_of_sq hF he he0 hsq
  obtain ⟨x, hx, hxe⟩ := invData_cover e he hinv
  obtain ⟨x', hx'⟩ : ∃ x', invData.find? (fun x => x.1 == e) = some x' := by
    cases h : invData.find? (fun x => x.1 == e) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 h x hx
      simp [hxe] at this
    | some x' => exact ⟨x', rfl⟩
  have hx'e : x'.1 = e := by simpa using List.find?_some hx'
  obtain ⟨-, hq, hKK, hcov, -⟩ := invOKT_spec (invAllOK_spec x' (List.mem_of_find?_eq_some hx'))
  have hK := Acts_Kel hM he
  have hKel2 : Kel e * Kel e = eta uJ 11 x'.2.1 := by
    apply Mx_injective
    have h1 := congrArg rowsMatrix (eqRows_iff.1 hKK)
    rw [hx'e, rowsMatrix_mulRows] at h1
    rw [map_mul, Mx_Kel hM he, Mx_etaR hM]
    exact h1
  have hKc : Kel e * eta uJ 11 c = eta uJ 11 (actT (tabE e) c) * Kel e := by
    have := hK.2 c (by simpa using hc)
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hrr : r * r = eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x'.2.1) := by
    rw [hre]
    calc eta uJ 11 c * Kel e * (eta uJ 11 c * Kel e)
        = eta uJ 11 c * (Kel e * eta uJ 11 c) * Kel e := by group
      _ = eta uJ 11 c * (eta uJ 11 (actT (tabE e) c) * Kel e) * Kel e := by rw [hKc]
      _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * (Kel e * Kel e) := by group
      _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * eta uJ 11 x'.2.1 := by rw [hKel2]
      _ = eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x'.2.1) := by
        rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
  have hxor0 : c ^^^ actT (tabE e) c ^^^ x'.2.1 = 0 := by
    have hlt : c ^^^ actT (tabE e) c ^^^ x'.2.1 < 2 ^ 11 :=
      Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by simpa using hc) (actT_lt hK.1 c))
        (by simpa using hq)
    refine eta_inj hM _ hlt 0 (by norm_num) ?_
    rw [← hrr, hsq, eta_zero]
  have hqc : c ^^^ actT (tabE x'.1) c = x'.2.1 := by
    rw [hx'e]
    exact Nat.eq_of_xor_eq_zero hxor0
  obtain ⟨y, hy, m, hm, hmy⟩ := classCover_spec hcov hc hqc
  rw [hx'e] at hmy
  unfold burnsideJ4NP_classOf burnsideJ4NP_classOfWith
  rw [hx']
  dsimp only
  cases h : x'.2.2.find? (fun y => (imSet (tabE e)).contains (c ^^^ y.1)) with
  | none =>
    exfalso
    apply List.find?_eq_none.1 h y hy
    rw [List.contains_iff_mem]
    unfold imSet
    rw [List.mem_eraseDups]
    exact List.mem_map.2 ⟨m, List.mem_range.2 hm, hmy⟩
  | some y' => exact ⟨y', rfl⟩


end CFSG.ASVolI
