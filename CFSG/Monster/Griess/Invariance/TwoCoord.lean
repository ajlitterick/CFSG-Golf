module

public import CFSG.Monster.Griess.Invariance.TwoCoord.Values

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix DiagonalInvariance TwoCoordInvariance

abbrev TwoIdx : Type := Fin 24 ⊕ (LtPair × Fin 3)

@[expose] def twoIdx : TwoIdx → TIdx
  | .inl i => .inl i
  | .inr x => .inr (.inl x)

@[expose] def VABCD : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun x : TwoIdx => tbasis (twoIdx x))

@[expose] def diagPairVal (k : Fin 24) (p : LtPair) : ℚ :=
  4 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0))

@[expose] def pairTripleVal (x y z : LtPair × Fin 3) : ℚ :=
  if x.1 = y.1 ∧ y.1 = z.1 ∧ x.2 ≠ y.2 ∧ y.2 ≠ z.2 ∧ x.2 ≠ z.2 then -8
  else if x.2 = y.2 ∧ y.2 = z.2 ∧ IsPairTriangle x.1 y.1 z.1 then 4 else 0

@[expose] def twoCoordValue : TwoIdx → TwoIdx → TwoIdx → ℚ
  | .inl i, .inl j, .inl k => if i = j ∧ j = k then 4 else 0
  | .inl k, .inr x, .inr y => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inl k, .inr y => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inr y, .inl k => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inr y, .inr z => pairTripleVal x y z
  | _, _, _ => 0

namespace TwoCoordInvariance

theorem T_diag_diag_diag (k i j : Fin 24) :
    T (tbasis (.inl k)) (tbasis (.inl i)) (tbasis (.inl j)) = if k = i ∧ i = j then 4 else 0 := by
  rw [T_diag_tbasis]
  simp only [diagEig, tnorm, Sum.inl.injEq]
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : i = j
    · simp [h2]
    · simp [h2]
  · simp [h1, Ne.symm h1]

theorem T_diag_diag_pair (k i : Fin 24) (x : LtPair × Fin 3) :
    T (tbasis (.inl k)) (tbasis (.inl i)) (tbasis (.inr (.inl x))) = 0 := by
  rw [T_diag_tbasis, ite_eq_right (by simp), mul_zero]

theorem T_diag_pair_diag (k : Fin 24) (x : LtPair × Fin 3) (j : Fin 24) :
    T (tbasis (.inl k)) (tbasis (.inr (.inl x))) (tbasis (.inl j)) = 0 := by
  rw [T_diag_tbasis, ite_eq_right (by simp), mul_zero]

theorem T_diag_pair_pair (k : Fin 24) (x y : LtPair × Fin 3) :
    T (tbasis (.inl k)) (tbasis (.inr (.inl x))) (tbasis (.inr (.inl y))) =
      if x = y then diagPairVal k x.1 else 0 := by
  rw [T_diag_tbasis]
  obtain ⟨p, m⟩ := x
  by_cases h : (p, m) = y
  · rw [ite_eq_left (by rw [h]), ite_eq_left h]
    simp only [diagEig, tnorm, diagPairVal]
    ring
  · rw [ite_eq_right (fun h' => h (by simpa using h')), ite_eq_right h, mul_zero]

theorem tbasis_pair_eq (p : LtPair) (m : Fin 3) :
    tbasis (.inr (.inl (p, m))) = ![inA (Ap p), inX (xv p (-1)), inX (xv p 1)] m := by
  rcases m with ⟨_ | _ | _ | m, hm⟩
  · exact tbasis_pair_zero' p
  · exact tbasis_pair_one' p
  · exact tbasis_pair_two' p
  · omega

theorem T_tbasis_pair3 (x y z : LtPair × Fin 3) :
    T (tbasis (.inr (.inl x))) (tbasis (.inr (.inl y))) (tbasis (.inr (.inl z))) =
      pairTripleVal x y z := by
  obtain ⟨p, m⟩ := x
  obtain ⟨q, m'⟩ := y
  obtain ⟨r, m''⟩ := z
  rw [tbasis_pair_eq, tbasis_pair_eq, tbasis_pair_eq]
  fin_cases m <;> fin_cases m' <;> fin_cases m'' <;>
    simp [pairTripleVal, T_Ap3, T_AAX, T_inA_inX_inA, T_inX_inA_inA, T_Ap_xv2, T_xv_Ap_xv,
      T_xv2_Ap', T_xv3] <;> norm_num

end TwoCoordInvariance

theorem T_tbasis_twoIdx (x y z : TwoIdx) :
    T (tbasis (twoIdx x)) (tbasis (twoIdx y)) (tbasis (twoIdx z)) = twoCoordValue x y z := by
  rcases x with k | x <;> rcases y with i | y <;> rcases z with j | z
  · exact T_diag_diag_diag k i j
  · exact T_diag_diag_pair k i z
  · exact T_diag_pair_diag k y j
  · exact T_diag_pair_pair k y z
  · exact (T_swap12 _ _ _).trans (T_diag_pair_diag i x j)
  · exact (T_swap12 _ _ _).trans (T_diag_pair_pair i x z)
  · exact (T_cycle2 _ _ _).trans (T_diag_pair_pair j x y)
  · exact T_tbasis_pair3 x y z


@[expose] def twoShift : TwoIdx → TwoIdx
  | .inl i => .inl i
  | .inr (p, m) => .inr (p, m + 1)

theorem tauB_tbasis_twoIdx (x : TwoIdx) :
    tauB (tbasis (twoIdx x)) = tbasis (twoIdx (twoShift x)) := by
  rcases x with i | ⟨p, m⟩
  · exact tauB_diag i
  · exact tauB_pair p m


theorem twoCoordValue_twoShift (x y z : TwoIdx) :
    twoCoordValue (twoShift x) (twoShift y) (twoShift z) = twoCoordValue x y z := by
  rcases x with i | ⟨p, m⟩ <;> rcases y with j | ⟨q, m'⟩ <;> rcases z with k | ⟨r, m''⟩ <;>
    simp [twoShift, twoCoordValue, pairTripleVal]


theorem T_tauB_of_mem_VABCD {u v w : SpaceB} (hu : u ∈ VABCD) (hv : v ∈ VABCD)
    (hw : w ∈ VABCD) : T (tauB u) (tauB v) (tauB w) = T u v w := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨c, rfl⟩ := hz
        rw [tauB_tbasis_twoIdx, tauB_tbasis_twoIdx, tauB_tbasis_twoIdx, T_tbasis_twoIdx,
          T_tbasis_twoIdx, twoCoordValue_twoShift]
      | zero => simp only [map_zero]
      | add w w' _ _ h h' => simp only [map_add, h, h']
      | smul t w _ h => simp only [map_smul, h]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add v v' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | smul t v _ h => simp only [map_smul, LinearMap.smul_apply, h]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add u u' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | smul t u _ h => simp only [map_smul, LinearMap.smul_apply, h]


end CFSG.Monster.Griess
