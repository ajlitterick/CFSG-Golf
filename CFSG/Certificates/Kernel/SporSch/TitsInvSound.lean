module

public import Certificates.Data.Kernel.SporSch.TitsInv
public import CFSG.Certificates.Kernel.SporSch.TitsEnum5Sound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Mathieu (icode)

theorem testBit_mask (j b : Nat) : (mask b).testBit j = decide (j < b) := by
  have e : mask b = 2 ^ b - 1 := by
    unfold mask
    rw [show Nat.shiftLeft 1 b = 1 <<< b from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    rfl
  rw [e, Nat.testBit_two_pow_sub_one]

theorem testBit_pg (w p j k : Nat) :
    (pg w (mask w) p j).testBit k = (decide (k < w) && p.testBit (w * j + k)) := by
  have e : pg w (mask w) p j = (p >>> (w * j)) &&& mask w := rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, testBit_mask, Bool.and_comm]

theorem pgR_eq (p i : Nat) : pgR p i = pg 11 (mask 11) p i := by
  apply Nat.eq_of_testBit_eq
  intro k
  have e : pgR p i = pg 11 (mask 11) ((p >>> (704 * (i / 64))) &&& mask 704) (i % 64) := rfl
  rw [e, testBit_pg, testBit_pg, Nat.testBit_and, Nat.testBit_shiftRight, testBit_mask]
  by_cases hk : k < 11
  · have h1 : 11 * (i % 64) + k < 704 := by omega
    have h2 : 704 * (i / 64) + (11 * (i % 64) + k) = 11 * i + k := by omega
    simp [hk, h1, h2]
  · simp [hk]


theorem allA_spec {α : Type} {f : α → Bool} : ∀ {A : List α}, allA f A = true → ∀ a ∈ A, f a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: A, h, a, ha => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allA f A) (f b) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1
    · exact allA_spec h2 a ha

theorem memN_spec {p : Nat} : ∀ {L : List Nat}, memN p L = true → p ∈ L
  | [], h => (Bool.false_ne_true h).elim
  | y :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memN p L) true (Nat.beq p y) = true := h
    cases hb : Nat.beq p y
    · rw [hb] at h'
      exact List.mem_cons_of_mem _ (memN_spec h')
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self


theorem gptR_eq (t0 t1 t2 t3 t4 i : Nat) :
    gptR t0 t1 t2 t3 t4 i = gpt 11 (mask 11) t0 t1 t2 t3 t4 i := by
  simp only [gptR, gpt, pgR_eq]

theorem sqGR_eq (G t0 t1 t2 t3 t4 : Nat) :
    sqGR G t0 t1 t2 t3 t4 = sqGPts 1755 11 (mask 11) G t0 t1 t2 t3 t4 := by
  simp only [sqGR, sqGPts, gptR_eq, pgR_eq]

theorem sqR_eq (t0 t1 t2 t3 t4 : Nat) :
    sqR t0 t1 t2 t3 t4 = sqPts 1755 11 (mask 11) t0 t1 t2 t3 t4 := by
  simp only [sqR, sqPts, gptR_eq]

theorem eqR_eq (Z t0 t1 t2 t3 t4 : Nat) :
    eqR Z t0 t1 t2 t3 t4 = eqPts 1755 11 (mask 11) Z t0 t1 t2 t3 t4 := by
  simp only [eqR, eqPts, gptR_eq, pgR_eq]

theorem memR_eq (L : List Nat) (t0 t1 t2 t3 t4 : Nat) :
    memR L t0 t1 t2 t3 t4 = memPts 1755 11 (mask 11) L t0 t1 t2 t3 t4 := by
  simp only [memR, memPts, eqR_eq]

theorem conjR_eq (T y t0 t1 t2 t3 t4 : Nat) :
    conjR T y t0 t1 t2 t3 t4 = conjPts 1755 11 (mask 11) T y t0 t1 t2 t3 t4 := by
  simp only [conjR, conjPts, gptR_eq, pgR_eq]


@[expose] def us (p : Nat) : Nat := p >>> 64


section Sift

open CFSG.KS.Raw.Orb CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Certificates.ChainArrays

variable {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}

theorem Fix_le {i j : Nat} (hij : i ≤ j) : Fix n S kO base j ≤ Fix n S kO base i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans Fix_succ_le ih

variable (hd : Hd n S base kO W)
include hd

theorem sift_step {l k : Nat} (hl : l < base.size) (hk : k < (lev n S base l).pts.size)
    {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ Fix n S kO base (l + 1)) {g : Array Nat}
    (hg : Rep n g (trP n S base l k * ρ)) :
    siftA n (rawLevels n S base) base l g =
        siftA n (rawLevels n S base) base (l + 1) (compA n (lev n S base l).trInv[k]! g) ∧
      Rep n (compA n (lev n S base l).trInv[k]! g) ρ := by
  have F := lev_facts hd hl
  have hbl := hd.base_lt l hl
  have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hl
  have hgb : g[base[l]!]! = (lev n S base l).pts[k]! := by
    rw [hg.apply hbl, Equiv.Perm.mul_apply, hρ.2 l (by omega) hbl]
    exact (tr_spec hd hl k hk).2
  refine ⟨?_, ?_⟩
  · rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
    simp only [hgb, F.pos_pts k hk, hk, decide_true, Bool.true_and]
  · have := rep_compA (rep_trInv hd hl hk) hg
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem tr_inj_step {l k k' : Nat} (hl : l < base.size) (hk : k < (lev n S base l).pts.size)
    (hk' : k' < (lev n S base l).pts.size) {ρ ρ' : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ Fix n S kO base (l + 1)) (hρ' : ρ' ∈ Fix n S kO base (l + 1))
    (h : trP n S base l k * ρ = trP n S base l k' * ρ') : k = k' ∧ ρ = ρ' := by
  have F := lev_facts hd hl
  have hbl := hd.base_lt l hl
  have e := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨base[l]!, hbl⟩ : Fin n) : Nat)) h
  simp only [Equiv.Perm.mul_apply, hρ.2 l (by omega) hbl, hρ'.2 l (by omega) hbl] at e
  rw [(tr_spec hd hl k hk).2, (tr_spec hd hl k' hk').2] at e
  have hkk : k = k' := by rw [← F.pos_pts k hk, ← F.pos_pts k' hk', e]
  subst hkk
  exact ⟨rfl, mul_left_cancel h⟩

theorem sift5 (h5 : base.size = 5) {a b c d e : Nat} (ha : a < (lev n S base 0).pts.size)
    (hb : b < (lev n S base 1).pts.size) (hc : c < (lev n S base 2).pts.size)
    (hdd : d < (lev n S base 3).pts.size) (he : e < (lev n S base 4).pts.size) {g : Array Nat}
    (hg : Rep n g (trP n S base 0 a * trP n S base 1 b * trP n S base 2 c * trP n S base 3 d *
      trP n S base 4 e)) : siftA n (rawLevels n S base) base 0 g = true := by
  have m1 := (tr_spec hd (by omega : 1 < base.size) b hb).1
  have m2 := (tr_spec hd (by omega : 2 < base.size) c hc).1
  have m3 := (tr_spec hd (by omega : 3 < base.size) d hdd).1
  have m4 := (tr_spec hd (by omega : 4 < base.size) e he).1
  have hg0 : Rep n g (trP n S base 0 a * (trP n S base 1 b * (trP n S base 2 c *
      (trP n S base 3 d * trP n S base 4 e)))) := by simpa only [mul_assoc] using hg
  obtain ⟨e0, r1⟩ := sift_step hd (by omega) ha (Subgroup.mul_mem _ m1 (Subgroup.mul_mem _
    (Fix_le (by omega) m2) (Subgroup.mul_mem _ (Fix_le (by omega) m3) (Fix_le (by omega) m4)))) hg0
  obtain ⟨e1, r2⟩ := sift_step hd (by omega) hb (Subgroup.mul_mem _ m2
    (Subgroup.mul_mem _ (Fix_le (by omega) m3) (Fix_le (by omega) m4))) r1
  obtain ⟨e2, r3⟩ := sift_step hd (by omega) hc (Subgroup.mul_mem _ m3 (Fix_le (by omega) m4)) r2
  obtain ⟨e3, r4⟩ := sift_step hd (by omega) hdd m4 r3
  obtain ⟨e4, r5⟩ := sift_step hd (by omega) he (Subgroup.one_mem _)
    (by rwa [mul_one] : Rep n _ (trP n S base 4 e * 1))
  have hls : ¬ 5 < (rawLevels n S base).size := by rw [chainLevels_size]; omega
  rw [e0, e1, e2, e3, e4, siftA, dite_eq_right hls]
  exact (eqA_iff r5 rep_idA).2 rfl

theorem prod5_inj (h5 : base.size = 5) {a b c d e a' b' c' d' e' : Nat}
    (ha : a < (lev n S base 0).pts.size) (hb : b < (lev n S base 1).pts.size)
    (hc : c < (lev n S base 2).pts.size) (hdd : d < (lev n S base 3).pts.size)
    (he : e < (lev n S base 4).pts.size) (ha' : a' < (lev n S base 0).pts.size)
    (hb' : b' < (lev n S base 1).pts.size) (hc' : c' < (lev n S base 2).pts.size)
    (hd' : d' < (lev n S base 3).pts.size) (he' : e' < (lev n S base 4).pts.size)
    (h : trP n S base 0 a * trP n S base 1 b * trP n S base 2 c * trP n S base 3 d *
      trP n S base 4 e = trP n S base 0 a' * trP n S base 1 b' * trP n S base 2 c' *
      trP n S base 3 d' * trP n S base 4 e') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' := by
  have M : ∀ i (hi : i < 5) {k : Nat}, k < (lev n S base i).pts.size →
      ∀ j ≤ i, trP n S base i k ∈ Fix n S kO base j := fun i hi k hk j hj =>
    Fix_le hj (tr_spec hd (by omega : i < base.size) k hk).1
  simp only [mul_assoc] at h
  obtain ⟨r0, h⟩ := tr_inj_step hd (by omega) ha ha'
    (Subgroup.mul_mem _ (M 1 (by omega) hb 1 le_rfl) (Subgroup.mul_mem _ (M 2 (by omega) hc 1
      (by omega)) (Subgroup.mul_mem _ (M 3 (by omega) hdd 1 (by omega)) (M 4 (by omega) he 1
      (by omega)))))
    (Subgroup.mul_mem _ (M 1 (by omega) hb' 1 le_rfl) (Subgroup.mul_mem _ (M 2 (by omega) hc' 1
      (by omega)) (Subgroup.mul_mem _ (M 3 (by omega) hd' 1 (by omega)) (M 4 (by omega) he' 1
      (by omega))))) h
  obtain ⟨r1, h⟩ := tr_inj_step hd (by omega) hb hb'
    (Subgroup.mul_mem _ (M 2 (by omega) hc 2 le_rfl) (Subgroup.mul_mem _ (M 3 (by omega) hdd 2
      (by omega)) (M 4 (by omega) he 2 (by omega))))
    (Subgroup.mul_mem _ (M 2 (by omega) hc' 2 le_rfl) (Subgroup.mul_mem _ (M 3 (by omega) hd' 2
      (by omega)) (M 4 (by omega) he' 2 (by omega)))) h
  obtain ⟨r2, h⟩ := tr_inj_step hd (by omega) hc hc'
    (Subgroup.mul_mem _ (M 3 (by omega) hdd 3 le_rfl) (M 4 (by omega) he 3 (by omega)))
    (Subgroup.mul_mem _ (M 3 (by omega) hd' 3 le_rfl) (M 4 (by omega) he' 3 (by omega))) h
  obtain ⟨r3, h⟩ := tr_inj_step hd (by omega) hdd hd' (M 4 (by omega) he 4 le_rfl)
    (M 4 (by omega) he' 4 le_rfl) h
  obtain ⟨r4, -⟩ := tr_inj_step hd (by omega) he he' (Subgroup.one_mem _) (Subgroup.one_mem _)
    (by rwa [mul_one, mul_one] : trP n S base 4 e * 1 = trP n S base 4 e' * 1)
  exact ⟨r0, r1, r2, r3, r4⟩

end Sift

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.KS.Prim

theorem arr_eq_of_get {n : Nat} {a b : Array Nat} (ha : a.size = n) (hb : b.size = n)
    (h : ∀ i < n, a[i]! = b[i]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i h1 h2
  rw [← getElem!_pos a i h1, ← getElem!_pos b i h2]
  exact h i (by omega)

theorem size_unpack (n w P : Nat) : (unpack n w P).size = n := by
  simp only [unpack, Array.size_ofFn]

theorem size_compA (n : Nat) (t u : Array Nat) : (compA n t u).size = n := by
  simp only [compA, Array.size_ofFn]

section Chain

variable {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}

theorem hd_of_binds {nb : Nat} (hb : Binds 1755 11 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS nb BP) : Raw.Orb.Hd 1755 S base S.size #[] :=
  ⟨le_rfl, Raw.Orb.isInv_of hb hp, fun _ hj hkj => absurd hj (Nat.not_lt.2 hkj),
    fun i hi => Raw.Orb.base_lt_of_levels hb hl i (by rw [← hb.2.2.2.2.2.1]; exact hi)⟩


theorem prodCode_rep (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) {c : Nat} (hc : c < tot5 LR) :
    CFSG.Monster.B.Co2.Rep 1755 (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR c))
      (Raw.Orb.trP 1755 S base 0 (c / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1)) *
        Raw.Orb.trP 1755 S base 1 (c / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1)) *
        Raw.Orb.trP 1755 S base 2 (c / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) *
        Raw.Orb.trP 1755 S base 3 (c / rcnt (LR 4) % rcnt (LR 3)) *
        Raw.Orb.trP 1755 S base 4 (c % rcnt (LR 4))) := by
  have hd := hd_of_binds hb hp hl
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hc
  obtain ⟨-, e, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  rw [prodCode_eq, ← e]
  exact CFSG.Monster.B.Co2.rep_compA (CFSG.Monster.B.Co2.rep_compA
    (CFSG.Monster.B.Co2.rep_compA (CFSG.Monster.B.Co2.rep_compA
      (Raw.Orb.rep_tr hd (by omega) (c0 ▸ d0)) (Raw.Orb.rep_tr hd (by omega) (c1 ▸ d1)))
      (Raw.Orb.rep_tr hd (by omega) (c2 ▸ d2))) (Raw.Orb.rep_tr hd (by omega) (c3 ▸ d3)))
    (Raw.Orb.rep_tr hd (by omega) (c4 ▸ d4))


end Chain


@[expose] noncomputable def letP (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), S (Nat.sub (Nat.shiftRight c (nat_lit 1))
    (nat_lit 1)), SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

theorem wPt_cons (S SI : Nat → Nat) (z : Int) (wd : List Int) (i : Nat) :
    wPt S SI (z :: wd) i = pgR (letP S SI (icode z)) (wPt S SI wd i) := by
  change strictN (icode z) (fun c => strictN (wPt S SI wd i) (fun j => pgR (letP S SI c) j)) = _
  rw [Raw.Orb.strictN_eq, Raw.Orb.strictN_eq]

section Letters

open CFSG.Monster.B.Co2

variable {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}

theorem rep_strong (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {j : Nat}
    (hj : j < kS) : Rep n S[j]! (permOfArr n S[j]!) ∧
      Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ ∧
      Rep n (unpack n w (PSI j)) (permOfArr n S[j]!)⁻¹ := by
  have hr := rep_permOfArr (Raw.Orb.isInvA_unpack (allN_spec hp j hj))
  rw [← hS.2 j hj] at hr
  refine ⟨hr.1, ?_, hr.2⟩
  rw [Raw.Orb.rawInvs_get (by omega)]
  exact rep_invCand hr.1

theorem letter_get (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {z : Int}
    (h1 : 0 < icode z) (h2 : icode z / 2 ≤ kS) {x : Nat} (hx : x < n) :
    (letterA S (rawInvs n S) z)[x]! = pg w (mask w) (letP PS PSI (icode z)) x ∧
      (letterA S (rawInvs n S) z)[x]! < n := by
  cases z with
  | ofNat k =>
    have ec : icode (Int.ofNat k) = k + k := rfl
    have h1' : 0 < k + k := h1
    have h2' : (k + k) / 2 ≤ kS := h2
    rw [ec]
    have e1 : Nat.land (k + k) 1 = 0 := by
      change (k + k) &&& 1 = 0
      rw [Nat.and_one_is_mod]
      omega
    have e2 : Nat.shiftRight (k + k) 1 = k := by
      rw [Raw.Orb.shr_eq]
      omega
    have eL : letP PS PSI (k + k) = PS (k - 1) := by
      unfold letP
      rw [e1, e2]
      rfl
    have hj : k - 1 < kS := by omega
    have hk0 : 0 < k := by omega
    have h0 : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk0
    have et : (Int.ofNat k).toNat = k := rfl
    have hL : letterA S (rawInvs n S) (Int.ofNat k) = S[k - 1]! := by
      unfold letterA
      rw [ite_eq_left h0, et]
    rw [hL, eL, hS.2 _ hj, unpack_getT hx]
    exact ⟨rfl, ((Raw.Orb.permOK_facts (allN_spec hp _ hj)).2.2 x hx).1⟩
  | negSucc k =>
    have ec : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl
    have h2' : (k + 1 + (k + 1) + 1) / 2 ≤ kS := h2
    rw [ec]
    have e1 : Nat.land (k + 1 + (k + 1) + 1) 1 = 1 := by
      change (k + 1 + (k + 1) + 1) &&& 1 = 1
      rw [Nat.and_one_is_mod]
      omega
    have e2 : Nat.shiftRight (k + 1 + (k + 1) + 1) 1 = k + 1 := by
      rw [Raw.Orb.shr_eq]
      omega
    have eL : letP PS PSI (k + 1 + (k + 1) + 1) = PSI k := by
      unfold letP
      rw [e1, e2]
      rfl
    have hj : k < kS := by omega
    have h0 : ¬ (0 : Int) < Int.negSucc k := Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero k))
    have et : (-Int.negSucc k).toNat = k + 1 := rfl
    have hL : letterA S (rawInvs n S) (Int.negSucc k) = (rawInvs n S)[k]! := by
      unfold letterA
      rw [ite_eq_right h0, et, Nat.add_sub_cancel]
    obtain ⟨-, r2, r3⟩ := rep_strong hS hp hj
    rw [hL, eL, ← unpack_getT hx, r2.apply hx, r3.apply hx]
    exact ⟨rfl, Fin.is_lt _⟩

end Letters

@[expose] def Bind13 (S : Array (Array Nat)) (PS PSI : Nat → Nat) : Prop :=
  S.size = 13 ∧ (∀ j < 13, S[j]! = unpack 1755 11 (PS j)) ∧
    allN 13 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true

theorem wPt_get {S : Array (Array Nat)} {PS PSI : Nat → Nat} (hS : Bind13 S PS PSI) :
    ∀ wd : List Int, lettersK 13 wd = true → ∀ i < 1755,
      (wordA 1755 S (rawInvs 1755 S) wd)[i]! = wPt PS PSI wd i ∧ wPt PS PSI wd i < 1755
  | [], _, i, hi => by
    rw [wordA, CFSG.Monster.B.Co2.idA_get hi]
    exact ⟨rfl, hi⟩
  | z :: wd, hl, i, hi => by
    rw [Raw.Orb.lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨h1, h2⟩, hl⟩ := hl
    obtain ⟨ih1, ih2⟩ := wPt_get hS wd hl i hi
    obtain ⟨l1, l2⟩ := letter_get ⟨hS.1, hS.2.1⟩ hS.2.2 h1 h2 ih2
    rw [wordA, CFSG.Monster.B.Co2.compA_get hi, ih1, wPt_cons, pgR_eq, ← l1]
    exact ⟨rfl, l2⟩

theorem wordA_rep {S : Array (Array Nat)} {PS PSI : Nat → Nat} {wd : List Int}
    (hS : Bind13 S PS PSI) (hl : lettersK 13 wd = true) :
    ∃ g, CFSG.Monster.B.Co2.Rep 1755 (wordA 1755 S (rawInvs 1755 S) wd) g :=
  ⟨_, CFSG.Monster.B.Co2.rep_wordA (gs := fun h => CFSG.Monster.B.Co2.permOfArr 1755 S[h]!)
    (fun _ hh => (rep_strong ⟨hS.1, hS.2.1⟩ hS.2.2 hh).1)
    (fun _ hh => (rep_strong ⟨hS.1, hS.2.1⟩ hS.2.2 hh).2.1) wd (lettersK_sound hl)⟩

theorem wPerm_sound {S : Array (Array Nat)} {PS PSI : Nat → Nat} {wd : List Int}
    (hS : Bind13 S PS PSI) (hl : lettersK 13 wd = true) :
    isInvA 1755 (wordA 1755 S (rawInvs 1755 S) wd)
      (invCand 1755 (wordA 1755 S (rawInvs 1755 S) wd)) = true := by
  obtain ⟨g, hg⟩ := wordA_rep hS hl
  exact isInvA_of_rep hg (rep_invCand hg)

theorem wPt_sound {S : Array (Array Nat)} {PS PSI : Nat → Nat} {wd : List Int} {i : Nat}
    (hS : Bind13 S PS PSI) (hl : lettersK 13 wd = true) (hi : i < 1755) :
    (wordA 1755 S (rawInvs 1755 S) wd)[i]! = wPt PS PSI wd i :=
  (wPt_get hS wd hl i hi).1

theorem conjW_sound {S : Array (Array Nat)} {PS PSI : Nat → Nat} {wd : List Int} {A y : Nat}
    (hS : Bind13 S PS PSI) (hA : canonK 1755 11 (mask 11) (1755 * 11) A = true)
    (_hy : canonK 1755 11 (mask 11) (1755 * 11) y = true) (h : conjW PS PSI wd A y = true) :
    compA 1755 (compA 1755 (wordA 1755 S (rawInvs 1755 S) wd) (unpack 1755 11 A))
      (invCand 1755 (wordA 1755 S (rawInvs 1755 S) wd)) = unpack 1755 11 y := by
  obtain ⟨hl, hc⟩ := (bAnd_iff _ _).1 h
  obtain ⟨g, hg⟩ := wordA_rep hS hl
  have hgi := rep_invCand hg
  obtain ⟨-, -, -, rA⟩ := canonK_facts hA
  refine arr_eq_of_get (size_compA _ _ _) (size_unpack _ _ _) fun i hi => ?_
  have hj := hgi.lt hi
  have e := Nat.eq_of_beq_eq_true (allN_spec hc _ hj)
  have hWj : (wordA 1755 S (rawInvs 1755 S) wd)[(invCand 1755 (wordA 1755 S (rawInvs 1755 S)
      wd))[i]!]! = i := by
    rw [hgi.apply hi, hg]
    simp
  rw [← wPt_sound hS hl hj, hWj, pgR_eq, pgR_eq, ← wPt_sound hS hl (rA _ hj)] at e
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hj, unpack_getT hj, e,
    unpack_getT hi]

theorem exclW_sound {S : Array (Array Nat)} {PS PSI : Nat → Nat} {wd : List Int} {T y : Nat}
    (hS : Bind13 S PS PSI) (_hT : canonK 1755 11 (mask 11) (1755 * 11) T = true)
    (hy : canonK 1755 11 (mask 11) (1755 * 11) y = true) (h : exclW PS PSI wd T y = true) :
    compA 1755 (compA 1755 (invCand 1755 (wordA 1755 S (rawInvs 1755 S) wd)) (unpack 1755 11 T))
      (wordA 1755 S (rawInvs 1755 S) wd) = unpack 1755 11 y := by
  obtain ⟨hl, hc⟩ := (bAnd_iff _ _).1 h
  obtain ⟨g, hg⟩ := wordA_rep hS hl
  have hgi := rep_invCand hg
  obtain ⟨-, -, -, ry⟩ := canonK_facts hy
  refine arr_eq_of_get (size_compA _ _ _) (size_unpack _ _ _) fun i hi => ?_
  have hu := hg.lt hi
  have e := Nat.eq_of_beq_eq_true (allN_spec hc i hi)
  rw [pgR_eq, pgR_eq, ← wPt_sound hS hl hi, ← wPt_sound hS hl (ry i hi)] at e
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hu, unpack_getT hu, ← e,
    unpack_getT hi, hg.apply (ry i hi), hgi]
  simp

end CFSG.KS.SporSch

end
