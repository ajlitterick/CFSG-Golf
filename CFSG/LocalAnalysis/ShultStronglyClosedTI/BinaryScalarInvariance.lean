module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.Classical2.CentralLiftCommutator

public section

namespace CFSG.ShultStronglyClosedTI

open scoped commutatorElement
open CFSG.RankThree.Classical2

universe u v

theorem exists_scalar_quadratic_ne_zero (K : Type u) [Field K] [Finite K]
    (hcard : 4 < Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ a ^ 2 + a + 1 ≠ 0 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X + 1
  have hp : p ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : Polynomial K => q.coeff 2) h
    norm_num [p, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
  have hdegree : p.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le <;> simp
    · simp
  let bad : Finset K := insert 0 (insert 1 p.roots.toFinset)
  have hbad : bad.card ≤ 4 := by
    have hroot := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
    have h1 := Finset.card_insert_le (1 : K) p.roots.toFinset
    have h0 := Finset.card_insert_le (0 : K) (insert 1 p.roots.toFinset)
    dsimp only [bad]
    omega
  have hlt : bad.card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt hbad hcard
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (by simp [bad, h])
  have ha1 : a ≠ 1 := by
    intro h
    exact ha (by simp [bad, h])
  refine ⟨a, ha0, ha1, ?_⟩
  intro h
  have hroot : a ∈ p.roots := (Polynomial.mem_roots hp).mpr (by
    simpa [p, Polynomial.IsRoot] using h)
  exact ha (by simp [bad, hroot])

theorem binaryScalarInvariantBiadditive_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {A : Type v} [AddCommGroup A] (hcard : 4 < Nat.card K)
    (b : K → K → A)
    (hleft : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hright : ∀ x y y', b x (y + y') = b x y + b x y')
    (hinvariant : ∀ a : K, a ≠ 0 → ∀ x y, b (a * x) (a * y) = b x y) :
    ∀ x y, b x y = 0 := by
  have hzero (y : K) : b 0 y = 0 := by
    have h := hleft 0 0 y
    simpa using h
  have htwo (x y : K) : b x y + b x y = 0 := by
    rw [← hleft, CharTwo.add_self_eq_zero, hzero]
  obtain ⟨a, ha0, ha1, hquad⟩ := exists_scalar_quadratic_ne_zero K hcard
  have hap : a + 1 ≠ 0 := by
    intro h
    exact ha1 (CharTwo.add_eq_zero.mp h)
  have hmove (x y : K) : b (a * x) y = b x (a⁻¹ * y) := by
    have h := hinvariant a ha0 x (a⁻¹ * y)
    simpa only [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] using h
  have hcross (x y : K) : b x y = b (a * x) y + b x (a * y) := by
    calc
      b x y = b ((a + 1) * x) ((a + 1) * y) := (hinvariant (a + 1) hap x y).symm
      _ = (b (a * x) (a * y) + b (a * x) y) +
          (b x (a * y) + b x y) := by
        rw [add_mul, add_mul, one_mul, one_mul, hleft, hright, hright]
      _ = b (a * x) y + b x (a * y) := by
        rw [hinvariant a ha0]
        calc
          (b x y + b (a * x) y) + (b x (a * y) + b x y) =
              (b x y + b x y) + (b (a * x) y + b x (a * y)) := by abel
          _ = b (a * x) y + b x (a * y) := by rw [htwo, zero_add]
  let c : K := a + a⁻¹ + 1
  have hc : c ≠ 0 := by
    intro h
    have heq : a * c = a ^ 2 + a + 1 := by
      dsimp only [c]
      rw [mul_add, mul_add, mul_inv_cancel₀ ha0]
      ring
    exact hquad (heq.symm.trans (by rw [h, mul_zero]))
  have hkill (x y : K) : b x (c * y) = 0 := by
    have heq : b x ((a + a⁻¹) * y) = b x y := by
      rw [add_mul, hright, ← hmove]
      exact (add_comm _ _).trans (hcross x y).symm
    dsimp only [c]
    rw [add_mul, one_mul, hright, heq, htwo]
  intro x y
  have h := hkill x (c⁻¹ * y)
  simpa only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] using h

theorem binaryScalarInvariantAddHom_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {A : Type v} [AddCommGroup A] (hcard : 4 < Nat.card K)
    (b : K →+ K →+ A)
    (hinvariant : ∀ a : Kˣ, ∀ x y, b ((a : K) * x) ((a : K) * y) = b x y) :
    ∀ x y, b x y = 0 := by
  apply binaryScalarInvariantBiadditive_eq_zero hcard (fun x y => b x y)
  · intro x x' y
    exact DFunLike.congr_fun (map_add b x x') y
  · intro x y y'
    exact map_add (b x) y y'
  · intro a ha x y
    exact hinvariant (Units.mk0 a ha) x y


end CFSG.ShultStronglyClosedTI
