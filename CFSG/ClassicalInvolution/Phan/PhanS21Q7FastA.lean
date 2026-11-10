module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Fast
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7SoundC

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

theorem getElem!_map_range {n : Nat} (f : Nat → Nat) {i : Nat} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem getElem!_map_range_lt {n : Nat} (f : Nat → Nat) (hf : ∀ i, f i < 49) (i : Nat) :
    ((Array.range n).map f)[i]! < 49 := by
  by_cases hi : i < n
  · rw [getElem!_map_range f hi]
    exact hf i
  · rw [getElem!_neg _ _ (by simpa using hi)]
    simp

theorem gfNeg_lt (a : Nat) : gfNeg a < 49 := mk_lt _ _

theorem gfConj_lt (a : Nat) : gfConj a < 49 := mk_lt _ _

theorem fMul_eq {a b : Nat} (ha : a < 49) (hb : b < 49) : fMul a b = gfMul a b := by
  have h : a * 49 + b < 2401 := by omega
  unfold fMul tMul
  rw [getElem!_map_range _ h]
  have h1 : (a * 49 + b) / 49 = a := by omega
  have h2 : (a * 49 + b) % 49 = b := by omega
  rw [h1, h2]

theorem fAdd_eq {a b : Nat} (ha : a < 49) (hb : b < 49) : fAdd a b = gfAdd a b := by
  have h : a * 49 + b < 2401 := by omega
  unfold fAdd tAdd
  rw [getElem!_map_range _ h]
  have h1 : (a * 49 + b) / 49 = a := by omega
  have h2 : (a * 49 + b) % 49 = b := by omega
  rw [h1, h2]


theorem fConj_eq {a : Nat} (ha : a < 49) : fConj a = gfConj a := by
  unfold fConj tConj
  rw [getElem!_map_range _ ha]

theorem fNorm_eq {a : Nat} (ha : a < 49) : fNorm a = gfMul a (gfConj a) := by
  unfold fNorm tNorm
  rw [getElem!_map_range _ ha]

theorem fMul_lt (a b : Nat) : fMul a b < 49 :=
  getElem!_map_range_lt _ (fun _ => gfMul_lt _ _) _

theorem fAdd_lt (a b : Nat) : fAdd a b < 49 :=
  getElem!_map_range_lt _ (fun _ => gfAdd_lt _ _) _


theorem fNorm_lt (a : Nat) : fNorm a < 49 :=
  getElem!_map_range_lt _ (fun _ => gfMul_lt _ _) _

@[expose] def Lt49 (x : N7) : Prop :=
  x.x0 < 49 ∧ x.x1 < 49 ∧ x.x2 < 49 ∧ x.x3 < 49 ∧ x.x4 < 49 ∧ x.x5 < 49 ∧ x.x6 < 49


theorem gfDec_five : gfDec 5 = -2 := gfDec_kappa

theorem five_lt : (5 : Nat) < 49 := by norm_num

theorem hDiag_lt (x : N7) : hDiag x < 49 := fAdd_lt _ _

theorem hF_lt (x y : N7) : hF x y < 49 := fAdd_lt _ _


theorem hDiag_dec {x : N7} (hx : Lt49 x) : gfDec (hDiag x) = herC x.dec x.dec := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  simp only [hDiag, fNorm_eq, fMul_eq, fAdd_eq, hx0, hx1, hx2, hx3, hx4, hx5, hx6, five_lt,
    gfMul_lt, gfAdd_lt, gfDec_add, gfDec_mul, gfDec_conj, gfDec_five]
  simp only [herC, bfC, tauC, N7.dec, conj49]
  ring

theorem hF_dec {x y : N7} (hx : Lt49 x) (hy : Lt49 y) : gfDec (hF x y) = herC x.dec y.dec := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  simp only [hF, fConj_eq, fMul_eq, fAdd_eq, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hy0, hy1, hy2,
    hy3, hy4, hy5, hy6, five_lt, gfMul_lt, gfAdd_lt, gfConj_lt, gfDec_add, gfDec_mul, gfDec_conj,
    gfDec_five]
  simp only [herC, bfC, tauC, N7.dec, conj49]
  ring


theorem herC_swap (x y : V7) : herC y x = star (herC x y) := by
  simp only [herC, bfC, tauC, conj49, star_add, star_mul', star_neg, star_star, star_ofNat]
  ring

theorem eq_iff_dec {a b : Nat} (ha : a < 49) (hb : b < 49) : a = b ↔ gfDec a = gfDec b :=
  ⟨fun h => by rw [h], gfDec_inj ha hb⟩


theorem lt49_candN {c : N7} {n1 n2 n4 n5 n6 : Nat} (h1 : n1 < 49) (h2 : n2 < 49) (h4 : n4 < 49)
    (h5 : n5 < 49) (h6 : n6 < 49) : Lt49 (candN c n1 n2 n4 n5 n6) :=
  ⟨gfNeg_lt _, h1, h2, by simp [candN], h4, h5, h6⟩

theorem candN_mem_A {c : N7} {x2 x5 x6 : Nat} (h2 : x2 < 49) (h5 : x5 < 49) (h6 : x6 < 49) :
    candN c 1 x2 (gfAdd (gfNeg (gfMul x2 x5)) (gfMul x6 x6)) x5 x6 ∈ q7Cands c := by
  simp only [q7Cands, candsA, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨x2, h2, x5, h5, x6, h6, rfl⟩))

theorem candN_mem_B {c : N7} {x4 x6 : Nat} (h4 : x4 < 49) (h6 : x6 < 49) :
    candN c 0 1 x4 (gfMul x6 x6) x6 ∈ q7Cands c := by
  simp only [q7Cands, candsB, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨x4, h4, x6, h6, rfl⟩))

theorem candN_mem_C {c : N7} {x5 : Nat} (h5 : x5 < 49) : candN c 0 0 1 x5 0 ∈ q7Cands c := by
  simp only [q7Cands, candsC, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨x5, h5, rfl⟩)

theorem candN_mem_D (c : N7) : candN c 0 0 0 1 0 ∈ q7Cands c := by
  simp [q7Cands, candsD]

theorem mem_q7Pts_iff {c b : N7} (hb : b ∈ q7Cands c) :
    b ∈ q7Pts c ↔ (isFFN b = true ∧ colN e0N b = true ∧ colN c b = true) := by
  unfold q7Pts
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

theorem herC_e0_e0 : herC e0C e0C = 1 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem herC_e0_left (B : V7) : herC e0C B = star B.x0 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem herC_e0_right (B : V7) : herC B e0C = B.x0 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem vert_iff_vtxF {c b : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {n1 n2 n4 n5 n6 : Nat}
    (hb : b = candN c n1 n2 n4 n5 n6) (h1 : n1 < 49) (h2 : n2 < 49) (h4 : n4 < 49)
    (h5 : n5 < 49) (h6 : n6 < 49)
    (hq : gfDec n1 * gfDec n4 + gfDec n2 * gfDec n5 = gfDec n6 ^ 2) :
    (isFFN b = true ∧ colN e0N b = true ∧ colN c b = true) ↔
      vtxF c (herN c c) b (hDiag b) = true := by
  have hbL : Lt49 b := hb ▸ lt49_candN h1 h2 h4 h5 h6
  have hB : b.dec = candV c.dec (gfDec n1) (gfDec n2) (gfDec n4) (gfDec n5) (gfDec n6) := by
    rw [hb, candN_dec]
  have hB3 : b.dec.x3 = 0 := by rw [hB]; rfl
  have hC3 : c.dec.x3 = 1 := by simp [N7.dec, hc3, gfDec_one]
  have F1 : bfC b.dec b.dec = 0 := by
    rw [hB]
    simp only [bfC, candV]
    linear_combination 2 * hq
  have F2 : bfC e0C b.dec = 0 := by rw [bfC_e0C, hB3]
  have F3 : bfC c.dec b.dec = 0 := by
    rw [hB]
    simp only [bfC, candV, hC3]
    ring
  have e0 : gfDec (hDiag b) = herC b.dec b.dec := hDiag_dec hbL
  have eγ : gfDec (herN c c) = herC c.dec c.dec := herN_dec c c
  have eh : gfDec (hF c b) = herC c.dec b.dec := hF_dec hc hbL
  have hG0 : gramC e0C b.dec = herC b.dec b.dec - star b.dec.x0 * b.dec.x0 := by
    rw [gramC, herC_e0_e0, herC_e0_left, herC_e0_right, one_mul]
  have hG1 : gramC c.dec b.dec =
      herC c.dec c.dec * herC b.dec b.dec - herC c.dec b.dec * star (herC c.dec b.dec) := by
    rw [gramC, herC_swap c.dec b.dec]
  rw [isFFN_iff, colN_iff, colN_iff, e0N_dec]
  unfold isFFC colC vtxF
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  rw [eq_zero_iff_of_lt (hDiag_lt b), eq_iff_dec (hDiag_lt b) (fNorm_lt _),
    eq_iff_dec (fMul_lt _ _) (fNorm_lt _), e0, fNorm_eq (hbL.1), gfDec_mul, gfDec_conj,
    fMul_eq (herN_lt c c) (hDiag_lt b), gfDec_mul, eγ, e0, fNorm_eq (hF_lt c b), gfDec_mul,
    gfDec_conj, eh, hG0, hG1, F1, F2, F3, sub_eq_zero, sub_eq_zero]
  simp only [true_and]
  have e : star b.dec.x0 * b.dec.x0 = gfDec b.x0 * star (gfDec b.x0) := mul_comm _ _
  rw [e, and_assoc]


end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
