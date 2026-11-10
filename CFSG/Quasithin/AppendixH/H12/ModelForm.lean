module

public import CFSG.Quasithin.AppendixH.H12.ModelCore
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.Quasithin.AppendixH.H12.Basic

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H13.Mat8Cert (b2z)
open CFSG.ASVolI.ChH (IsIsoPoint IsQuadFormOn IsUnitaryForm kLine kSmul)
open CFSG.Quasithin.H13.L1442M
open Matrix

@[expose] def Qcols : List ℕ := [1, 3, 6, 13, 19, 50, 97, 211, 492, 920, 1051, 3126]


private theorem gmv_zU_eq (x : ℕ) : gmv zU x = mvN z12 x := by
  rw [gmv, zU_val, colsN_decN validN_z12]

private theorem glHom_zU_dc (c : ℕ) : glHom zU (dc c) = dc (mvN z12 c) := by
  rw [glHom_dc, zU_val, colsN_decN validN_z12]

private theorem gmv_gU_eq (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

private theorem quadN_gU0 (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD 0 one12) c) = quadN 12 Qcols c := by
  have h : (List.range 4096).all
      (fun c => quadN 12 Qcols (mvN (gG.getD 0 one12) c) == quadN 12 Qcols c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

private theorem quadN_gU1 (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD 1 one12) c) = quadN 12 Qcols c := by
  have h : (List.range 4096).all
      (fun c => quadN 12 Qcols (mvN (gG.getD 1 one12) c) == quadN 12 Qcols c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

private theorem quadN_gU (i : ℕ) (hi : i < 2) (c : ℕ) (hc : c < 4096) :
    quadN 12 Qcols (mvN (gG.getD i one12) c) = quadN 12 Qcols c := by
  interval_cases i
  · exact quadN_gU0 c hc
  · exact quadN_gU1 c hc

theorem quadN_gmv {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    quadN 12 Qcols (gmv g c) = quadN 12 Qcols c := by
  let P : Γ12 → Prop := fun g => ∀ c < 4096, quadN 12 Qcols (gmv g c) = quadN 12 Qcols c
  have h1 : P 1 := by
    intro c hc
    rw [gmv_one hc]
  have hstep : ∀ i < 2, ∀ y, P y → P (gU i * y) := by
    intro i hi y hy c hc
    rw [gmv_mul, gmv_gU_eq]
    rw [quadN_gU i hi (gmv y c) (gmv_lt y c)]
    exact hy c hc
  exact G_induction (p := P) h1 hstep hg c hc

theorem polN_gmv {g : Γ12} (hg : g ∈ G0) {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (gmv g a) (gmv g b) = polN 12 Qcols a b := by
  simp only [polN, ← gmv_xor]
  rw [quadN_gmv hg (Nat.xor_lt_two_pow (n := 12) ha hb), quadN_gmv hg ha, quadN_gmv hg hb]

private theorem polN_omega {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (mvN z12 a) (mvN z12 b) = polN 12 Qcols a b := by
  have h := polN_gmv (g := zU) zU_mem (a := a) (b := b) ha hb
  rwa [gmv_zU_eq, gmv_zU_eq] at h


@[expose] def q0 (v : Vec12) : ZMod 2 :=
  CFSG.Quasithin.H13.L1442M.quadOf (decN 12 Qcols) (Multiplicative.toAdd v)


private theorem mul_self_vec12 (v : Vec12) : v * v = 1 := by
  rw [← dc_cd v, ← dc_xor, Nat.xor_self, dc_zero]

private theorem sq_mul (v w : Vec12) : v * (v * w) = w := by
  rw [← mul_assoc, mul_self_vec12, one_mul]

private theorem zU_sq_apply (v : Vec12) : glHom zU (glHom zU v) = v * glHom zU v := by
  rw [← dc_cd v, glHom_zU_dc, glHom_zU_dc, omega_sq (cd_lt v), dc_xor]

private theorem f4_add_re (x y : FieldFour) : (x + y).re = (x.re ^^ y.re) := rfl

private theorem f4_add_im (x y : FieldFour) : (x + y).im = (x.im ^^ y.im) := rfl

private theorem f4_mul_re (x y : FieldFour) :
    (x * y).re = ((x.re && y.re) ^^ (x.im && y.im)) := rfl

private theorem f4_mul_im (x y : FieldFour) :
    (x * y).im = (((x.re && y.im) ^^ (x.im && y.re)) ^^ (x.im && y.im)) := rfl

@[expose] def smulV (c : FieldFour) (v : Vec12) : Vec12 :=
  (if c.re then v else 1) * (if c.im then glHom zU v else 1)

private theorem smulV_one_vec (c : FieldFour) : smulV c 1 = 1 := by
  simp [smulV, map_one]


theorem smulV_one (v : Vec12) : smulV 1 v = v := by
  simp [smulV]

theorem smulV_zero (v : Vec12) : smulV 0 v = 1 := by
  simp [smulV]

theorem smulV_add (c d : FieldFour) (v : Vec12) : smulV (c + d) v = smulV c v * smulV d v := by
  rcases c with ⟨cr, ci⟩
  rcases d with ⟨dr, di⟩
  cases cr <;> cases ci <;> cases dr <;> cases di <;>
    simp only [smulV, f4_add_re, f4_add_im, if_true, if_false, one_mul, mul_one, mul_self_vec12]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

theorem smulV_mul (c d : FieldFour) (v : Vec12) : smulV (c * d) v = smulV c (smulV d v) := by
  rcases c with ⟨cr, ci⟩
  rcases d with ⟨dr, di⟩
  cases cr <;> cases ci <;> cases dr <;> cases di <;>
    simp only [smulV, f4_mul_re, f4_mul_im, zU_sq_apply, map_mul, mul_self_vec12, if_true,
      if_false, one_mul, mul_one]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

theorem smulV_mul_vec (c : FieldFour) (u v : Vec12) : smulV c (u * v) = smulV c u * smulV c v := by
  rcases c with ⟨cr, ci⟩
  cases cr <;> cases ci <;>
    simp only [smulV, map_mul, if_true, if_false, one_mul, mul_one]
  all_goals simp [mul_self_vec12, sq_mul, mul_comm, mul_assoc, mul_left_comm]

@[expose] def ι0 : FieldFour →+* AddMonoid.End (Additive Vec12) where
  toFun c :=
    { toFun := fun x => Additive.ofMul (smulV c (Additive.toMul x))
      map_zero' := by
        show Additive.ofMul (smulV c (Additive.toMul (0 : Additive Vec12))) = 0
        rw [show Additive.toMul (0 : Additive Vec12) = (1 : Vec12) from rfl, smulV_one_vec]
        rfl
      map_add' := by
        intro a b
        show Additive.ofMul (smulV c (Additive.toMul (a + b))) =
          Additive.ofMul (smulV c (Additive.toMul a)) +
            Additive.ofMul (smulV c (Additive.toMul b))
        rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl]
        rw [show Additive.ofMul (smulV c (Additive.toMul a)) +
              Additive.ofMul (smulV c (Additive.toMul b)) =
            Additive.ofMul (smulV c (Additive.toMul a) * smulV c (Additive.toMul b)) from rfl]
        rw [← smulV_mul_vec] }
  map_one' := AddMonoidHom.ext fun x => by
    show Additive.ofMul (smulV 1 (Additive.toMul x)) = x
    rw [smulV_one]
    rfl
  map_mul' := by
    intro c d
    apply AddMonoidHom.ext
    intro x
    change Additive.ofMul (smulV (c * d) (Additive.toMul x)) =
      Additive.ofMul (smulV c (smulV d (Additive.toMul x)))
    rw [smulV_mul]
  map_zero' := AddMonoidHom.ext fun x => by
    show Additive.ofMul (smulV 0 (Additive.toMul x)) = 0
    rw [smulV_zero]
    rfl
  map_add' := by
    intro c d
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (smulV (c + d) (Additive.toMul x)) =
      Additive.ofMul (smulV c (Additive.toMul x)) +
        Additive.ofMul (smulV d (Additive.toMul x))
    rw [smulV_add]
    rfl


@[expose] def f0 (u v : Vec12) : FieldFour :=
  ⟨decide (q0 (glHom zU (glHom zU u) * v) + q0 (glHom zU (glHom zU u)) + q0 v = 1),
    decide (q0 (u * v) + q0 u + q0 v = 1)⟩


private theorem polN_omega2 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols (mvN z12 (mvN z12 a)) (mvN z12 (mvN z12 b)) = polN 12 Qcols a b := by
  have h1 := polN_omega (a := a) (b := b) ha hb
  have h2 := polN_omega (a := mvN z12 a) (b := mvN z12 b) (z12_lt a) (z12_lt b)
  rw [h2, h1]

private theorem key2 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    polN 12 Qcols a (mvN z12 b) = polN 12 Qcols (mvN z12 (mvN z12 a)) b := by
  nth_rewrite 1 [← omega_cube ha]
  rw [polN_omega (a := mvN z12 (mvN z12 a)) (b := b) (z12_lt (mvN z12 a)) hb]


end CFSG.Quasithin.AppendixH.H12.Model
