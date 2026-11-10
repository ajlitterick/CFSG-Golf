module

public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.RankThree.Lattice.SteinbergBIF4EightTwelve

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl

@[expose] def f4Col (B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (k : Fin Tag.F4.rank) :
    Fin Tag.F4.rank → ℤ :=
  fun i => B i k

structure F4CyclicBasis (w : WeylGroup .F4) where
  B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  N : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  ε : ℤ
  smul_zero : w • f4Col B (f4Index 0) = f4Col B (f4Index 1)
  smul_one : w • f4Col B (f4Index 1) = f4Col B (f4Index 2)
  smul_two : w • f4Col B (f4Index 2) = f4Col B (f4Index 3)
  smul_three : w • f4Col B (f4Index 3) = ε • f4Col B (f4Index 2) - f4Col B (f4Index 0)
  N_mul : N * B = 1
  mul_N : B * N = 1

namespace F4CyclicBasis

variable {w : WeylGroup .F4} (D : F4CyclicBasis w) {L : Type} [Field L]

theorem single_eq_sum (j : Fin Tag.F4.rank) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = ∑ i, D.N i j • f4Col D.B i := by
  funext t
  have h := congrFun (congrFun D.mul_N t) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, f4Col]
  rw [Pi.single_apply, ← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem eq_of_rootChar_basis {c c' : Fin Tag.F4.rank → Lˣ}
    (h : ∀ k, rootChar c (f4Col D.B k) = rootChar c' (f4Col D.B k)) : c = c' := by
  funext j
  have e : ∀ a : Fin Tag.F4.rank → Lˣ, a j = ∏ i, rootChar a (f4Col D.B i) ^ D.N i j := by
    intro a
    rw [← rootChar_pi_single a j, D.single_eq_sum j, rootChar_sum]
    exact Finset.prod_congr rfl fun i _ => rootChar_zsmul a _ _
  rw [e c, e c']
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

@[expose] def cycTuple (q : ℕ) (ζ : Lˣ) : Fin Tag.F4.rank → Lˣ :=
  fun j => ζ ^ (∑ i : Fin Tag.F4.rank, (q : ℤ) ^ (i : ℕ) * D.N i j)

@[expose] def cycTupleHom (q : ℕ) : Lˣ →* (Fin Tag.F4.rank → Lˣ) where
  toFun := D.cycTuple q
  map_one' := by
    funext j
    simp [cycTuple]
  map_mul' ζ ζ' := by
    funext j
    simp only [cycTuple, Pi.mul_apply, mul_zpow]

theorem cycTupleHom_apply (q : ℕ) (ζ : Lˣ) : D.cycTupleHom q ζ = D.cycTuple q ζ :=
  rfl

theorem rootChar_cycTuple_col (q : ℕ) (ζ : Lˣ) (k : Fin Tag.F4.rank) :
    rootChar (D.cycTuple q ζ) (f4Col D.B k) = ζ ^ ((q : ℤ) ^ (k : ℕ)) := by
  have hNB : ∀ i, ∑ j, D.N i j * D.B j k = if i = k then 1 else 0 := fun i => by
    have h := congrFun (congrFun D.N_mul i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  rw [rootChar]
  simp only [cycTuple, f4Col, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, hNB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem cycTupleHom_injective (q : ℕ) :
    Function.Injective (D.cycTupleHom (L := L) q) := fun ζ ζ' h => by
  have h0 := congrArg (fun c => rootChar c (f4Col D.B (f4Index 0))) h
  simp only [cycTupleHom_apply, rootChar_cycTuple_col] at h0
  rwa [show ((f4Index 0 : Fin Tag.F4.rank) : ℕ) = 0 from rfl, pow_zero, zpow_one, zpow_one] at h0

theorem forall_rootChar_smul_eq_pow_iff (q : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    (∀ v, rootChar c (w • v) = rootChar c v ^ q) ↔
      ∃ ζ : Lˣ, ζ ^ ((q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) = 1 ∧ c = D.cycTuple q ζ := by
  constructor
  · intro h
    set ζ := rootChar c (f4Col D.B (f4Index 0)) with hζ
    have h1 : rootChar c (f4Col D.B (f4Index 1)) = ζ ^ ((q : ℤ) ^ (1 : ℕ)) := by
      rw [← D.smul_zero, h, pow_one, zpow_natCast]
    have h2 : rootChar c (f4Col D.B (f4Index 2)) = ζ ^ ((q : ℤ) ^ (2 : ℕ)) := by
      rw [← D.smul_one, h, h1, ← zpow_natCast, ← zpow_mul]
      congr 1
    have h3 : rootChar c (f4Col D.B (f4Index 3)) = ζ ^ ((q : ℤ) ^ (3 : ℕ)) := by
      rw [← D.smul_two, h, h2, ← zpow_natCast, ← zpow_mul]
      congr 1
    have h4 := h (f4Col D.B (f4Index 3))
    rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul, h2, h3,
      ← hζ, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at h4
    refine ⟨ζ, ?_, D.eq_of_rootChar_basis fun k => ?_⟩
    · have e : (q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1 =
          (q : ℤ) ^ 3 * q - (q : ℤ) ^ 2 * D.ε + 1 := by
        ring
      rw [e, zpow_add, zpow_sub, ← h4, zpow_one]
      group
    · rw [rootChar_cycTuple_col]
      fin_cases k
      · show rootChar c (f4Col D.B (f4Index 0)) = ζ ^ ((q : ℤ) ^ (0 : ℕ))
        rw [pow_zero, zpow_one]
      · exact h1
      · exact h2
      · exact h3
  · rintro ⟨ζ, hζ, rfl⟩ v
    have hsmul : ∀ (c : Fin Tag.F4.rank → Lˣ) (x : Fin Tag.F4.rank → ℤ),
        rootChar c (w • x) = rootChar (fun j => rootChar c (w • Pi.single j 1)) x := by
      intro c x
      rw [smul_eq_sum_smul_single w x, rootChar_sum, rootChar]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [rootChar_zsmul]
    have hc : (fun j => rootChar (D.cycTuple q ζ) (w • Pi.single j 1)) =
        D.cycTuple q ζ ^ q := by
      refine D.eq_of_rootChar_basis fun k => ?_
      rw [← hsmul, rootChar_pow_tuple, rootChar_cycTuple_col,
        ← zpow_natCast, ← zpow_mul]
      fin_cases k
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 0)) = ζ ^ ((q : ℤ) ^ (0 : ℕ) * q)
        rw [D.smul_zero, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (1 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 1)) = ζ ^ ((q : ℤ) ^ (1 : ℕ) * q)
        rw [D.smul_one, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (2 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 2)) = ζ ^ ((q : ℤ) ^ (2 : ℕ) * q)
        rw [D.smul_two, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (3 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 3)) = ζ ^ ((q : ℤ) ^ (3 : ℕ) * q)
        rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul,
          rootChar_cycTuple_col, rootChar_cycTuple_col]
        show (ζ ^ ((q : ℤ) ^ (2 : ℕ))) ^ D.ε * (ζ ^ ((q : ℤ) ^ (0 : ℕ)))⁻¹ = _
        rw [show (q : ℤ) ^ (3 : ℕ) * q = ((q : ℤ) ^ 2 * D.ε + -1) +
            ((q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) by ring, zpow_add, hζ, mul_one, zpow_add,
          ← zpow_mul, pow_zero, zpow_one, zpow_neg_one]
    rw [hsmul, hc, rootChar_pow_tuple]

@[expose] def torus (L : Type) [Field L] (q d : ℕ) : Subgroup (ModGL .F4 L) :=
  (rootsOfUnity d L).map ((rootDiagUnitHom .F4 L).comp (D.cycTupleHom q))

theorem rootDiagUnit_mem_torus_iff (q d : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit .F4 c ∈ D.torus L q d ↔ ∃ ζ : Lˣ, ζ ^ d = 1 ∧ c = D.cycTuple q ζ := by
  constructor
  · rintro ⟨ζ, hζ, h⟩
    exact ⟨ζ, (mem_rootsOfUnity d ζ).1 hζ, (rootDiagUnit_injective h).symm⟩
  · rintro ⟨ζ, hζ, rfl⟩
    exact ⟨ζ, (mem_rootsOfUnity d ζ).2 hζ, rfl⟩

theorem torus_le_torusGroup (q d : ℕ) : D.torus L q d ≤ torusGroup .F4 L := by
  rintro _ ⟨ζ, -, rfl⟩
  exact F4_rootDiagUnit_mem_torusGroup _

theorem natCard_torus [IsAlgClosed L] (q d : ℕ) [NeZero (d : L)] :
    Nat.card (D.torus L q d) = d := by
  have : NeZero d := ⟨fun h => NeZero.ne (d : L) (by rw [h, Nat.cast_zero])⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  rw [torus, Subgroup.card_map_of_injective
    (rootDiagUnit_injective.comp (D.cycTupleHom_injective q)), hζ.card_rootsOfUnity]


theorem conj_frob_eq_iff_mem_torus (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q) {d : ℕ}
    (hd : (d : ℤ) = (q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) {u : ModGL .F4 L}
    (hu : u ∈ torusGroup .F4 L) :
    canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom F) u *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹ = u ↔ u ∈ D.torus L q d := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  rw [conj_frob_rootDiagUnit_eq_iff F hF w c, D.forall_rootChar_smul_eq_pow_iff,
    D.rootDiagUnit_mem_torus_iff, ← hd]
  simp only [zpow_natCast]

end F4CyclicBasis


end CFSG.RankThree.Chevalley
