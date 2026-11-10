module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatTable
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Sporadic.He.Native

@[expose] def FpfM {d : ℕ} (M : M2 d) : Prop := ∀ v : Fin d → ZMod 2, M *ᵥ v = v → v = 0

@[expose] instance {d : ℕ} (M : M2 d) : Decidable (FpfM M) := by
  unfold FpfM; infer_instance

@[expose] def fpfB {d : ℕ} (M : M2 d) : Bool := decide (FpfM M)

@[expose] def tabPw (par : Array (ℕ × ℕ)) (L : Array (Array ℕ)) (x i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then x else tabMul par L x x

@[expose] def fpfA (d : ℕ) (X : AM) : Bool := fpfB (toMat 2 d X)

@[expose] def centralTOK (d : ℕ) (T : RawTab) : Bool :=
  let n := T.elts.size
  let fp := T.elts.map (fpfA d)
  (List.range n).all (fun a => (a == 0) ||
    !((List.range n).all fun b => tabMul T.par T.L a b == tabMul T.par T.L b a) ||
    fp[a]!) &&
  (List.range n).all (fun α =>
    (α == 0) || !(tabMul T.par T.L α (tabMul T.par T.L α α) == 0) ||
    (List.range n).all fun β =>
      (β == 0) || (β == α) || (β == tabMul T.par T.L α α) ||
      !(tabMul T.par T.L β (tabMul T.par T.L β β) == 0) ||
      !(tabMul T.par T.L α β == tabMul T.par T.L β α) ||
      (List.range 3).any fun i => (List.range 3).any fun j =>
        let γ := tabMul T.par T.L (tabPw T.par T.L α i) (tabPw T.par T.L β j)
        (γ != 0) && !(fp[γ]!))

@[expose] def tabAbelianOK (B : RawTab) : Bool :=
  (List.range B.elts.size).all fun a => (List.range B.elts.size).all fun b =>
    tabMul B.par B.L a b == tabMul B.par B.L b a

@[expose] def coverOK (d : ℕ) (adm : AM → Bool) (S B : RawTab) (wits : Array (AM × AM)) :
    Bool :=
  (List.range S.elts.size).all fun a =>
    (a == 0) || !(tabMul S.par S.L a (tabMul S.par S.L a a) == 0) ||
    wits.any fun w => matEqB 2 d w.1 S.elts[a]! && adm w.2 &&
      (List.range B.elts.size).any fun b =>
        matEqB 2 d (mulM 2 d w.2 S.elts[a]!) (mulM 2 d B.elts[b]! w.2)

@[expose] def coverOK3 (d : ℕ) (adm : AM → AM → Bool) (S B : RawTab)
    (wits : Array (AM × AM × AM)) : Bool :=
  (List.range S.elts.size).all fun a =>
    (a == 0) || !(tabMul S.par S.L a (tabMul S.par S.L a a) == 0) ||
    wits.any fun w => matEqB 2 d w.1 S.elts[a]! && adm w.2.1 w.2.2 &&
      (List.range B.elts.size).any fun b =>
        matEqB 2 d (mulM 2 d w.2.1 S.elts[a]!) (mulM 2 d B.elts[b]! w.2.1)


theorem factorization_three_of_eq {n k m : ℕ} (h : n = 3 ^ k * m) (hm : ¬ 3 ∣ m) :
    n.factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fpfM_conj_mp {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G)
    (h : FpfM (mat x)) : FpfM (mat (g * x * g⁻¹)) := by
  intro w hw
  have hinv : mat g⁻¹ * mat g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : mat g * mat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have this' : (mat g * mat x * mat g⁻¹) *ᵥ w = w := by
    have := hw
    rwa [map_mul, map_mul] at this
  have h1 : mat x *ᵥ (mat g⁻¹ *ᵥ w) = mat g⁻¹ *ᵥ w := by
    calc mat x *ᵥ (mat g⁻¹ *ᵥ w)
        = (mat g⁻¹ * mat g) *ᵥ (mat x *ᵥ (mat g⁻¹ *ᵥ w)) := by rw [hinv, Matrix.one_mulVec]
      _ = mat g⁻¹ *ᵥ ((mat g * mat x * mat g⁻¹) *ᵥ w) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = mat g⁻¹ *ᵥ w := by rw [this']
  have h3 := h _ h1
  have : w = mat g *ᵥ (mat g⁻¹ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  rw [this, h3, Matrix.mulVec_zero]

theorem fpfM_conj {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G) :
    FpfM (mat (g * x * g⁻¹)) = FpfM (mat x) := by
  apply propext
  refine ⟨fun h => ?_, fpfM_conj_mp mat g x⟩
  have := fpfM_conj_mp mat g⁻¹ _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

section Spec


end Spec

end CFSG.HardMathSupport.Foote.E27
