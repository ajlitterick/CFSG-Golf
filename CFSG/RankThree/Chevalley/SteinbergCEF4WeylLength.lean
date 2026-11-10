module

public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.LieType.Chevalley.LatticeWeylGroup
public import CFSG.Monster.SteinbergBQOddPrimeCongruenceTorsionFree

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

namespace F4Weyl


@[expose] def reflT (i : Fin Tag.F4.rank) : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  Matrix.of fun k l => (if k = l then 1 else 0) - if l = i then Tag.F4.cartan i k else 0

@[expose] def invTranspose (w : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) :
    Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  (LinearMap.toMatrix' (↑w⁻¹ : Module.End ℤ (Fin Tag.F4.rank → ℤ))).transpose

@[expose] def charMatrices : Set (Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) :=
  invTranspose '' (latticeWeylGroup .F4 : Set (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ)

theorem invTranspose_one : invTranspose 1 = 1 := by
  rw [invTranspose, inv_one, Units.val_one, LinearMap.toMatrix'_one, Matrix.transpose_one]

theorem invTranspose_mul (a b : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) :
    invTranspose (a * b) = invTranspose a * invTranspose b := by
  rw [invTranspose, invTranspose, invTranspose, mul_inv_rev, Units.val_mul,
    LinearMap.toMatrix'_mul, Matrix.transpose_mul]

theorem invTranspose_reflectUnit (i : Fin Tag.F4.rank) :
    invTranspose (reflectUnit .F4 i) = reflT i := by
  ext k l
  rw [invTranspose, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  change reflect .F4 i (Pi.single k 1) l = reflT i k l
  rw [reflect]
  simp only [reflT, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hkl : k = l <;> by_cases hli : l = i <;> simp [hkl, hli, eq_comm]


theorem mem_charMatrices {u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} :
    u ∈ charMatrices ↔ ∃ w : WeylGroup .F4, invTranspose (weylToAut .F4 w) = u := by
  rw [charMatrices, ← range_weylToAut]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, rfl⟩

theorem invTranspose_weylToAut_mul (w v : WeylGroup .F4) :
    invTranspose (weylToAut .F4 (w * v)) =
      invTranspose (weylToAut .F4 w) * invTranspose (weylToAut .F4 v) := by
  rw [map_mul, invTranspose_mul]

theorem invTranspose_weylToAut_simple (i : Fin Tag.F4.rank) :
    invTranspose (weylToAut .F4 (simple .F4 i)) = reflT i := by
  rw [weylToAut_simple, invTranspose_reflectUnit]

theorem invTranspose_weylToAut_mul_inv (w : WeylGroup .F4) :
    invTranspose (weylToAut .F4 w) * invTranspose (weylToAut .F4 w⁻¹) = 1 := by
  rw [← invTranspose_weylToAut_mul, mul_inv_cancel, map_one, invTranspose_one]


@[expose] def longestWord : List (Fin 4) :=
  [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]


theorem mul_reflT_apply (X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (i k l : Fin Tag.F4.rank) :
    (X * reflT i) k l = X k l - if l = i then ∑ m, X k m * Tag.F4.cartan i m else 0 := by
  rw [Matrix.mul_apply]
  by_cases hli : l = i
  · subst hli
    simp [reflT, mul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  · simp [reflT, hli, Finset.sum_ite_eq']

theorem reflT_mul_apply (X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (i k l : Fin Tag.F4.rank) :
    (reflT i * X) k l = X k l - Tag.F4.cartan i k * X i l := by
  rw [Matrix.mul_apply]
  simp [reflT, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem eq_scalar_of_commute_reflT {X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    (h : ∀ i, X * reflT i = reflT i * X) :
    X = Matrix.scalar (Fin Tag.F4.rank) (X ⟨0, by decide⟩ ⟨0, by decide⟩) := by
  have key : ∀ i k l, (if l = i then ∑ m, X k m * Tag.F4.cartan i m else 0) =
      Tag.F4.cartan i k * X i l := by
    intro i k l
    have h1 := congrFun (congrFun (h i) k) l
    rw [mul_reflT_apply, reflT_mul_apply] at h1
    linarith
  have hoff : ∀ i l, l ≠ i → X i l = 0 := by
    intro i l hli
    have h1 := key i i l
    rw [ite_eq_right hli, Tag.cartan_self] at h1
    linarith
  have hrel : ∀ i k, X k k * Tag.F4.cartan i k = Tag.F4.cartan i k * X i i := by
    intro i k
    have h1 := key i k i
    rw [ite_eq_left rfl, Finset.sum_eq_single k (fun m _ hmk => by rw [hoff k m hmk, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk)] at h1
    exact h1
  have h01 := hrel ⟨0, by decide⟩ ⟨1, by decide⟩
  have h12 := hrel ⟨1, by decide⟩ ⟨2, by decide⟩
  have h23 := hrel ⟨2, by decide⟩ ⟨3, by decide⟩
  have hc01 : Tag.F4.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 := by decide
  have hc12 : Tag.F4.cartan ⟨1, by decide⟩ ⟨2, by decide⟩ = -1 := by decide
  have hc23 : Tag.F4.cartan ⟨2, by decide⟩ ⟨3, by decide⟩ = -1 := by decide
  rw [hc01] at h01
  rw [hc12] at h12
  rw [hc23] at h23
  have hcases : ∀ k : Fin Tag.F4.rank, k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ ∨
      k = ⟨2, by decide⟩ ∨ k = ⟨3, by decide⟩ := by decide
  ext k l
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    rcases hcases k with rfl | rfl | rfl | rfl <;> linarith
  · rw [ite_eq_right hkl]
    exact hoff k l (Ne.symm hkl)

@[expose] def charRep : WeylGroup .F4 →* GL (Fin Tag.F4.rank) ℤ where
  toFun w := ⟨invTranspose (weylToAut .F4 w), invTranspose (weylToAut .F4 w⁻¹),
    invTranspose_weylToAut_mul_inv w, by
      rw [← invTranspose_weylToAut_mul, inv_mul_cancel, map_one, invTranspose_one]⟩
  map_one' := Units.ext (by
    change invTranspose (weylToAut .F4 1) = 1
    rw [map_one, invTranspose_one])
  map_mul' w v := Units.ext (invTranspose_weylToAut_mul w v)

theorem coe_charRep (w : WeylGroup .F4) :
    (charRep w : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) = invTranspose (weylToAut .F4 w) :=
  rfl

theorem injOn_map_charMatrices {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Set.InjOn (fun u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ =>
      u.map (Int.castRingHom (ZMod p))) charMatrices := by
  intro u hu u' hu' heq
  obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
  obtain ⟨v, rfl⟩ := mem_charMatrices.1 hu'
  simp only at heq
  set ι : ℤ →+* CFSG.Monster.ratLocal p := Int.castRingHom _ with hι
  have hιinj : Function.Injective ι := fun a b hab => by
    have h1 := congrArg (fun x : CFSG.Monster.ratLocal p => (x : ℚ)) hab
    simpa [hι] using h1
  set g := Matrix.GeneralLinearGroup.map ι (charRep (v⁻¹ * w)) with hg
  have hfin : IsOfFinOrder g := (Matrix.GeneralLinearGroup.map ι).isOfFinOrder
    (charRep.isOfFinOrder (isOfFinOrder_of_finite _))
  have hcomp : ∀ a : ℤ, CFSG.Monster.ratLocalRed p (ι a) = Int.castRingHom (ZMod p) a :=
    fun a => by rw [← RingHom.comp_apply, RingHom.ext_int ((CFSG.Monster.ratLocalRed p).comp ι)
      (Int.castRingHom (ZMod p))]
  have hmat : (invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w)).map
      (Int.castRingHom (ZMod p)) = 1 := by
    rw [Matrix.map_mul, heq, ← Matrix.map_mul, ← invTranspose_weylToAut_mul, inv_mul_cancel,
      map_one, invTranspose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hred : Matrix.GeneralLinearGroup.map (CFSG.Monster.ratLocalRed p) g = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, hg, Matrix.GeneralLinearGroup.map_apply, hcomp,
      coe_charRep, invTranspose_weylToAut_mul]
    have h1 := congrFun (congrFun hmat i) j
    rw [Matrix.map_apply] at h1
    rw [h1]
    rfl
  have hg1 := (CFSG.Monster.odd_prime_congruence_torsion_free p hp2 (Fin Tag.F4.rank)).1 g hred
    hfin
  have hone : invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w) = 1 := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin Tag.F4.rank) (CFSG.Monster.ratLocal p) =>
      (x : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (CFSG.Monster.ratLocal p)) i j) hg1
    simp only [hg, Matrix.GeneralLinearGroup.map_apply, coe_charRep,
      invTranspose_weylToAut_mul, Units.val_one] at h1
    apply hιinj
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [hι]
    · simp [hι, hij]
  calc invTranspose (weylToAut .F4 w)
      = invTranspose (weylToAut .F4 v) *
          (invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w)) := by
        rw [← mul_assoc, ← invTranspose_weylToAut_mul, mul_inv_cancel, map_one,
          invTranspose_one, one_mul]
    _ = invTranspose (weylToAut .F4 v) := by rw [hone, mul_one]

theorem map_mul_comm_of_eq_scalar {p : ℕ} {A M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    {c : ZMod p} (hA : A.map (Int.castRingHom (ZMod p)) = Matrix.scalar (Fin Tag.F4.rank) c) :
    (A * M).map (Int.castRingHom (ZMod p)) = (M * A).map (Int.castRingHom (ZMod p)) := by
  rw [Matrix.map_mul, Matrix.map_mul, hA]
  exact (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq

theorem eq_one_or_neg_one_of_map_eq_scalar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} (hu : u ∈ charMatrices) {c : ZMod p}
    (hc : u.map (Int.castRingHom (ZMod p)) = Matrix.scalar (Fin Tag.F4.rank) c) :
    u = 1 ∨ u = -1 := by
  obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
  have hcomm : ∀ i, invTranspose (weylToAut .F4 w) * reflT i =
      reflT i * invTranspose (weylToAut .F4 w) := by
    intro i
    have h1 : invTranspose (weylToAut .F4 w) * reflT i ∈ charMatrices := mem_charMatrices.2
      ⟨w * simple .F4 i, by rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_simple]⟩
    have h2 : reflT i * invTranspose (weylToAut .F4 w) ∈ charMatrices := mem_charMatrices.2
      ⟨simple .F4 i * w, by rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_simple]⟩
    exact injOn_map_charMatrices hp2 h1 h2 (map_mul_comm_of_eq_scalar hc)
  have hX := eq_scalar_of_commute_reflT hcomm
  set d := invTranspose (weylToAut .F4 w) ⟨0, by decide⟩ ⟨0, by decide⟩ with hd
  have hinv := invTranspose_weylToAut_mul_inv w
  rw [hX] at hinv
  have h00 := congrFun (congrFun hinv ⟨0, by decide⟩) ⟨0, by decide⟩
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h00
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h00 with ⟨hd1, -⟩ | ⟨hd1, -⟩
  · left
    rw [hX, hd1, map_one]
  · right
    rw [hX, hd1, map_neg, map_one]


theorem sum_length_eq [Fintype (WeylGroup .F4)] (q : ℕ) :
    ∑ w : WeylGroup .F4, q ^ (coxeterSystem .F4).length w =
      (([2, 6, 8, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, q ^ i).prod := by
  rw [sum_length_F4]
  simp only [geomSum, one_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [geom_eq_mul_geom_pow q (show 3 * 2 = 6 from rfl),
    geom_eq_mul_geom_pow q (show 4 * 3 = 12 from rfl)]
  ring

open Polynomial in
theorem weyl_length_polynomial [Fintype (WeylGroup .F4)] :
    ∑ w : WeylGroup .F4, (X : ℤ[X]) ^ (coxeterSystem .F4).length w =
        (([2, 6, 8, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
      Nat.card (WeylGroup .F4) = 1152 := by
  refine ⟨eq_of_forall_natCast_eval_eq fun n => ?_, ?_⟩
  · have h := congrArg (Nat.cast : ℕ → ℤ) (sum_length_eq n)
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil] at h
    simpa only [eval_finsetSum, eval_pow, eval_X, eval_mul, eval_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil] using h
  · have h := sum_length_eq 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul,
      mul_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
    rw [Nat.card_eq_fintype_card, h]

end F4Weyl

open F4Weyl


end CFSG.RankThree.Chevalley
