module

public import CFSG.LieType.Steinberg.CentralExt.SpinOddThree
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (exists_ne_three single_add_single_apply_of_ne'
  neg_one_zpow_boolSign negPair negPair_swap single_add_single_add_not two_mul_boolSign
  not_isLong_single_two swapPair swapPair_swap not_isLong_add_disjoint)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TorusLift

attribute [local instance] centerCommGroup

variable {E K : Type*} [Group E] [Group K] {π : E →* K} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π) {k : Type*} [Field k] {x : k → K}
  (hx : ∀ s t, x (s + t) = x s * x t)

theorem commPairing_map {g : K} {σ : k → k} (hg : ∀ s, g * x s * g⁻¹ = x (σ s)) (s t : k) :
    commPairing hcen hπ hx (σ s) (σ t) = commPairing hcen hπ hx s t := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [commPairing_apply, commPairing_apply]
  set g' := lift hπ g
  rw [commutatorElement_eq_of_map_eq hcen
      (show π (lift hπ (x (σ s))) = π (g' * lift hπ (x s) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg])
      (show π (lift hπ (x (σ t))) = π (g' * lift hπ (x t) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg]),
    ← conjugate_commutatorElement]
  have hc := Subgroup.mem_center_iff.1 (hcen (commLift_mem_ker hπ hx s t)) g'
  rw [hc, mul_inv_cancel_right]

end CFSG.LieType.Steinberg.CentralExt.TorusLift

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]


end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

attribute [local instance] TorusLift.centerCommGroup

open SpinOddClosed (TorIdx chi)
open QuadraticAlgebra

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def negStar (t : ShortField b c) : ShortField b c := ⟨-(t.re + b * t.im), t.im⟩

theorem fieldCoord_negStar (t : ShortField b c) :
    fieldCoord (negStar t) = planeRefl b c planeOne (fieldCoord t) := by
  rw [planeRefl, planeNorm_planeOne, div_one]
  ext k
  fin_cases k <;> simp [fieldCoord, negStar, polarPlane, planeOne]
  ring

theorem pairing_eq_zero_of_negStar [Finite K] (hK : Nat.card K = 3) {A : Type*} [AddCommGroup A]
    (P : ShortField b c →+ ShortField b c →+ A) (hP0 : ∀ s, P s s = 0)
    (hσ : ∀ s t, P (negStar s) (negStar t) = P s t) : P = 0 := by
  have h3 : (3 : K) = 0 := WeylLift.three_eq_zero hK
  have hsmul : ∀ (r : K) x y, P x y = 0 → P (r • x) y = 0 := fun r x y h => by
    rcases WeylLift.eq_zero_or_one_or_neg_one hK r with rfl | rfl | rfl
    · rw [zero_smul, map_zero, AddMonoidHom.zero_apply]
    · rw [one_smul, h]
    · rw [neg_smul, one_smul, map_neg, AddMonoidHom.neg_apply, h, neg_zero]
  have hsmul' : ∀ (r : K) x y, P x y = 0 → P x (r • y) = 0 := fun r x y h => by
    rcases WeylLift.eq_zero_or_one_or_neg_one hK r with rfl | rfl | rfl
    · rw [zero_smul, map_zero]
    · rw [one_smul, h]
    · rw [neg_smul, one_smul, map_neg, h, neg_zero]
  have hσ1 : negStar (1 : ShortField b c) = -1 := by
    ext <;> simp [negStar]
  have hσω : negStar (QuadraticAlgebra.omega : ShortField b c) = QuadraticAlgebra.omega - b • 1 := by
    ext <;> simp [negStar]
  have h1b : P 1 (b • 1) = 0 := hsmul' b 1 1 (hP0 1)
  have hneg : P 1 QuadraticAlgebra.omega = -P 1 QuadraticAlgebra.omega := by
    have h := hσ 1 QuadraticAlgebra.omega
    rw [hσ1, hσω, map_neg, AddMonoidHom.neg_apply, map_sub, h1b, sub_zero] at h
    exact h.symm
  have h111 : (1 : ShortField b c) + 1 + 1 = 0 := by
    ext
    · simp only [re_add, re_one, re_zero]
      linear_combination h3
    · simp
  have h1ω : P 1 QuadraticAlgebra.omega = 0 := by
    have h := congrArg (fun z => P z QuadraticAlgebra.omega) h111
    simp only [map_add, AddMonoidHom.add_apply, map_zero, AddMonoidHom.zero_apply] at h
    have h2 : P 1 QuadraticAlgebra.omega + P 1 QuadraticAlgebra.omega = 0 := by
      nth_rewrite 2 [hneg]
      exact add_neg_cancel _
    rw [h2, zero_add] at h
    exact h
  have hω1 : P QuadraticAlgebra.omega 1 = 0 := by
    have h := hP0 (1 + QuadraticAlgebra.omega)
    simp only [map_add, AddMonoidHom.add_apply, hP0, h1ω, zero_add, add_zero] at h
    exact h
  have hbase : ∀ x ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)),
      ∀ y ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)), P x y = 0 := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · exact hP0 1
    · exact h1ω
    · exact hω1
    · exact hP0 QuadraticAlgebra.omega
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  rw [← re_smul_add_im_smul s, ← re_smul_add_im_smul t]
  simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.zero_apply]
  have h1 : (1 : ShortField b c) ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)) := Or.inl rfl
  have hω : (QuadraticAlgebra.omega : ShortField b c) ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)) := Or.inr rfl
  rw [hsmul _ _ _ (hsmul' _ _ _ (hbase _ h1 _ h1)), hsmul _ _ _ (hsmul' _ _ _ (hbase _ h1 _ hω)),
    hsmul _ _ _ (hsmul' _ _ _ (hbase _ hω _ h1)), hsmul _ _ _ (hsmul' _ _ _ (hbase _ hω _ hω))]

theorem shortWeyl_conj_x {i k : Fin (n - 1)} (hik : i ≠ k) {γ : Fin (n - 1) → ℤ} {u : Bool}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) (t : ShortField b c) :
    shortWeyl n hirr i * x hirr γ t * (shortWeyl n hirr i)⁻¹ = x hirr γ (negStar t) := by
  rw [x_of_short hirr h, x_of_short hirr h, shortWeyl_conj_twShortRoot, fieldCoord_negStar,
    longWeylSign_of_ne hik.symm, one_smul]
  congr 1
  simp [shortWeylBool, hik.symm]

variable {E : Type*} [Group E] {π : E →* spinGroup (quadMinus n K b c)}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_short_three [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] [Finite K]
    (hK : Nat.card K = 3) (hn : 4 ≤ n)
    {γ : Fin (n - 1) → ℤ} {k : Fin (n - 1)} {u : Bool}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) :
    TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
  obtain ⟨i, hik, -⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) k k
  exact pairing_eq_zero_of_negStar hK _ (TorusLift.commPairing_self hcen hπ (x_add hirr γ))
    (TorusLift.commPairing_map hcen hπ (x_add hirr γ) (shortWeyl_conj_x hirr hik h))

omit hcen in
theorem X_eq_algebraMap_re {γ : Fin (n - 1) → ℤ} (hγ : IsRootLift hirr π γ (X hirr π γ))
    (hl : IsLong (toStdB (n - 1) γ)) (s : ShortField b c) :
    X hirr π γ s = X hirr π γ (algebraMap K (ShortField b c) s.re) := by
  have h := hγ.1 (algebraMap K (ShortField b c) s.re) (s - algebraMap K (ShortField b c) s.re)
  rw [add_sub_cancel] at h
  rw [h, hγ.2.2.1 (s - algebraMap K (ShortField b c) s.re) ?_, mul_one]
  rw [x_of_isLong hirr hl, re_sub, algebraMap_re, sub_self, elt_of_isLong _ hl, rootElt_zero]

include hcen hπ in
theorem commute_X_of_swap [Finite K] (hK : Nat.card K = 3) {γ δ : Fin (n - 1) → ℤ}
    (hγ : IsRootLift hirr π γ (X hirr π γ)) (hδ : IsRootLift hirr π δ (X hirr π δ))
    (hγl : IsLong (toStdB (n - 1) γ)) (hδl : IsLong (toStdB (n - 1) δ))
    (hl : ¬IsLong (toStdB (n - 1) γ + toStdB (n - 1) δ))
    (h0 : toStdB (n - 1) γ + toStdB (n - 1) δ ≠ 0) {g : spinGroup (quadMinus n K b c)} {a : K}
    (ha : a * a = 1)
    (h1 : ∀ d, g * rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ) d * g⁻¹ =
      rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ) (a * d))
    (h2 : ∀ d, g * rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ) d * g⁻¹ =
      rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ) (a * d)) (s t : ShortField b c) :
    X hirr π γ s * X hirr π δ t = X hirr π δ t * X hirr π γ s := by
  have hx : ∀ {e : Fin (n - 1) → ℤ}, IsLong (toStdB (n - 1) e) → ∀ r : K,
      x hirr e (algebraMap K (ShortField b c) r) =
        rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) e) r := fun hel r => by
    rw [x_of_isLong hirr hel, algebraMap_re, elt_of_isLong _ hel]
  rw [X_eq_algebraMap_re hirr hγ hγl, X_eq_algebraMap_re hirr hδ hδl]
  exact WeylLift.commute_of_swap_lift hK hcen hπ
    (x := rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ))
    (x₁ := rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ))
    (Y := fun r => X hirr π γ (algebraMap K (ShortField b c) r))
    (Y₁ := fun r => X hirr π δ (algebraMap K (ShortField b c) r))
    (fun r r' => (congrArg (X hirr π γ) (map_add _ r r')).trans (hγ.1 _ _))
    (fun r r' => (congrArg (X hirr π δ) (map_add _ r r')).trans (hδ.1 _ _))
    (fun r => (hγ.2.1 _).trans (hx hγl r)) (fun r => (hδ.2.1 _).trans (hx hδl r))
    (fun r r' => (commute_rootElt (minusFrame n b c).toHypFrame hγl hδl h0 hl r r').eq) ha h1 h2
    _ _


end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
