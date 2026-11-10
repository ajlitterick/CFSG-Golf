module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalC

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Native

@[expose] def suzZS : Set (Equiv.Perm (Fin 22880)) :=
  {x | x ∈ suzS3 ∧ ∀ y ∈ suzS3, x * y = y * x}


theorem suzS3_center_eq :
    suzZS = Set.range (fun r : Fin 9 => centerFullPerm r) := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨r, hr, rfl⟩ := mem_center_records hx hc
    exact ⟨⟨r, hr⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨centerFullPerm_mem r.2, centerFullPerm_central r.2⟩


theorem mem_center_map_iff {x : Equiv.Perm (Fin 22880)} :
    x ∈ (Subgroup.center suzS3).map suzS3.subtype ↔ x ∈ suzZS := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨w, hw⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (hc g g.2).symm

theorem centerFullPerm_zero :
    centerFullPerm 0 = 1 := by
  rw [centerFullPerm_eq (by norm_num)]
  simp

theorem centerFullPerm_one :
    centerFullPerm 1 = suzZ := by
  rw [centerFullPerm_eq (by norm_num)]
  simp

theorem centerFullPerm_pow_three
    {r : ℕ} (hr : r < 9) : centerFullPerm r ^ 3 = 1 := by
  rw [centerFullPerm_eq hr, (Commute.pow_pow (show Commute (centerFullPerm 3) suzZ from
    centerFullPerm_three_comm_z) _ _).mul_pow, ← pow_mul, ← pow_mul, mul_comm (r / 3),
    mul_comm (r % 3), pow_mul, pow_mul, centerFullPerm_three_pow, suzZ_pow_three, one_pow,
    one_pow, one_mul]


theorem center_pow_three
    {x : suzS3} (hx : x ∈ Subgroup.center suzS3) : x ^ 3 = 1 := by
  have hx' : (x : Equiv.Perm (Fin 22880)) ∈ suzZS := mem_center_map_iff.1 ⟨x, hx, rfl⟩
  rw [suzS3_center_eq] at hx'
  obtain ⟨r, hr⟩ := hx'
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hr, centerFullPerm_pow_three r.2]
  rfl

theorem zpowers_sq {G : Type*} [Group G] {x : G} (h : x ^ 3 = 1) :
    Subgroup.zpowers (x * x) = Subgroup.zpowers x := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)
  · rw [Subgroup.zpowers_le]
    have hx : x = (x * x) * (x * x) := by
      calc x = x ^ 3 * x := by rw [h, one_mul]
        _ = (x * x) * (x * x) := by rw [pow_succ, pow_two]; simp only [mul_assoc]
    exact Subgroup.mem_zpowers_iff.2 ⟨2, by rw [zpow_two]; exact hx.symm⟩

theorem centerFullPerm_sq_eq :
    centerFullPerm 1 * centerFullPerm 1 = centerFullPerm 2 ∧
    centerFullPerm 3 * centerFullPerm 3 = centerFullPerm 6 ∧
    centerFullPerm 4 * centerFullPerm 4 = centerFullPerm 8 ∧
    centerFullPerm 5 * centerFullPerm 5 = centerFullPerm 7 := by
  obtain ⟨-, -, -, -, -, h1, h3, h4, h5, -⟩ := sylowCenterChecks_facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_compA (rep_centerFull (by norm_num)) (rep_centerFull (by norm_num)))
      (rep_centerFull (by norm_num))).1 h1
  · exact (eqA_iff (rep_compA (rep_centerFull (by norm_num)) (rep_centerFull (by norm_num)))
      (rep_centerFull (by norm_num))).1 h3
  · exact (eqA_iff (rep_compA (rep_centerFull (by norm_num)) (rep_centerFull (by norm_num)))
      (rep_centerFull (by norm_num))).1 h4
  · exact (eqA_iff (rep_compA (rep_centerFull (by norm_num)) (rep_centerFull (by norm_num)))
      (rep_centerFull (by norm_num))).1 h5

@[expose] def suzLine (r : ℕ) : Subgroup (Equiv.Perm (Fin 22880)) :=
  Subgroup.zpowers (centerFullPerm r)

theorem suzLine_of_mem
    {r : ℕ} (hr : r < 9) (hr0 : r ≠ 0) :
    suzLine r = suzLine 1 ∨ suzLine r = suzLine 3 ∨ suzLine r = suzLine 4 ∨
      suzLine r = suzLine 5 := by
  obtain ⟨h1, h3, h4, h5⟩ := centerFullPerm_sq_eq
  interval_cases r
  · exact absurd rfl hr0
  · exact Or.inl rfl
  · left
    rw [suzLine, ← h1, zpowers_sq (centerFullPerm_pow_three (by norm_num))]
    rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · right; left
    rw [suzLine, ← h3, zpowers_sq (centerFullPerm_pow_three (by norm_num))]
    rfl
  · right; right; right
    rw [suzLine, ← h5, zpowers_sq (centerFullPerm_pow_three (by norm_num))]
    rfl
  · right; right; left
    rw [suzLine, ← h4, zpowers_sq (centerFullPerm_pow_three (by norm_num))]
    rfl


@[expose] def suzFusionG : Equiv.Perm (Fin 22880) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => if (h : ℕ) = 0 then suzA0 else suzA1)
    (toLetters 2 [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2])

theorem rep_suzFusionG : Rep 22880 fusionTransArr suzFusionG := by
  have key : ∀ (A0 A1 I0 I1 : Array ℕ) (g0 g1 : Equiv.Perm (Fin 22880)),
      Rep 22880 A0 g0 → Rep 22880 A1 g1 → Rep 22880 I0 g0⁻¹ → Rep 22880 I1 g1⁻¹ →
      Rep 22880 (wordA 22880 #[A0, A1] #[I0, I1] [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2])
        (Quiver.SchreierGraph.evalWord (fun h : Fin 2 => if (h : ℕ) = 0 then g0 else g1)
          (toLetters 2 [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2])) := by
    intro A0 A1 I0 I1 g0 g1 r0 r1 i0 i1
    refine rep_wordA (gs := fun h => if h = 0 then g0 else g1) (fun h hh => ?_)
      (fun h hh => ?_) _ (by decide)
    · interval_cases h
      · exact r0
      · exact r1
    · interval_cases h
      · exact i0
      · exact i1
  exact key _ _ _ _ _ _ rep_suzA0 rep_suzA1
    (rep_inv_of_isInvA rep_suzA0 (Bool.and_eq_true_iff.1 (arrays_check.1 0 (by norm_num))).2)
    (rep_inv_of_isInvA rep_suzA1 (Bool.and_eq_true_iff.1 (arrays_check.1 1 (by norm_num))).2)

theorem suzFusionG_mem : suzFusionG ∈ suzP := by
  refine evalWord_mem (fun h => ?_) _
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem fusionNormChecks_facts :
    isInvA 22880 fusionTransArr (invCand 22880 fusionTransArr) = true ∧
    eqA 22880 (compA 22880 fusionTransArr (compA 22880 zArr (invCand 22880 fusionTransArr)))
      (centerFull 5) = true ∧
    fusionTransArr[0]! = 95 ∧ fixedCountN 22880 (centerFull 3) = 38 ∧
    fixedCountN 22880 (centerFull 4) = 38 ∧
    (∀ k < 39, isInvA 280 (normWordArr k) (invCand 280 (normWordArr k)) = true) ∧
    (∀ k < 8, isInvA 280 localGenArrs[k]! (invCand 280 localGenArrs[k]!) = true) ∧
    (∀ k < 39, ∀ k' < 39, k < k' → eqA 280 (normConj k) (normConj k') = false ∧
      eqA 280 (normConj k) (compA 280 (normConj k') (normConj k')) = false) := by
  have h := threeLocal_parts.2.2.2
  simp only [fusionNormChecks, Bool.and_eq_true, beq_iff_eq, allLt_iff, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun k hk k' hk' hkk' => ?_⟩
  have := h8 k hk k' hk'
  simpa [hkk'] using this

theorem suzFusionG_conj :
    suzFusionG * suzZ * suzFusionG⁻¹ = centerFullPerm 5 := by
  have hinv := rep_inv_of_isInvA rep_suzFusionG fusionNormChecks_facts.1
  have := (eqA_iff (rep_compA rep_suzFusionG (rep_compA rep_zArr hinv))
    (rep_centerFull (by norm_num))).1 fusionNormChecks_facts.2.1
  rw [← this, mul_assoc]

theorem fusion_lines :
    suzLine 1 = suzQ ∧
      suzQ.map (MulAut.conj suzFusionG).toMonoidHom = suzLine 5 := by
  refine ⟨by rw [suzLine, centerFullPerm_one]; rfl, ?_⟩
  rw [suzQ, MonoidHom.map_zpowers, suzLine, ← suzFusionG_conj]
  rfl

theorem ncard_fixed_eq {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    {x : Fin n | g x = x}.ncard = fixedCountN n t := by
  classical
  have hset : {x : Fin n | g x = x} =
      ((Finset.univ.filter fun x : Fin n => g x = x : Finset (Fin n)) : Set (Fin n)) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset, fixedCountN, fixedList,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply Finset.card_bij (fun (x : Fin n) _ => (x : ℕ))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨x.2, by rw [ht x, hx]⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro y hy
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    rw [← ht ⟨y, hy.1⟩]
    exact hy.2


@[expose] def localOrig (h : ℕ) : Equiv.Perm (Fin 280) :=
  if hh : h < localChain.originalCount then localChain.original.get ⟨h, hh⟩ else 1

theorem localOrig_mem (h : ℕ) : localOrig h ∈ localChain.originalSubgroup := by
  rw [localOrig]
  split_ifs with hh
  · exact Subgroup.subset_closure (schreier_vector_get_mem_toList _ _)
  · exact Subgroup.one_mem _

theorem rep_localOrig
    {h : ℕ} (hh : h < 8) : Rep 280 localGenArrs[h]! (localOrig h) := by
  have hh' : h < localChain.originalCount := by
    change h < localGenArrs.size
    simpa [localGenArrs] using hh
  simp only [localOrig, hh', ↓reduceDIte]
  exact localChain_arrays.orig ⟨h, hh'⟩

@[expose] def normWordPerm (k : ℕ) : Equiv.Perm (Fin 280) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 8 => localOrig h) (toLetters 8 (normWords.getD k []))

theorem normWords_letters
    (k : ℕ) : lettersOK 8 (normWords.getD k []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : normWords[k]? with
  | none => rfl
  | some w => exact graphArrays_check.2.2.2.2.2.2.2.2.2.2.2.1 w (List.mem_of_getElem? hh)

theorem rep_normWordPerm
    (k : ℕ) : Rep 280 (normWordArr k) (normWordPerm k) := by
  refine rep_wordA (gs := localOrig) (fun h hh => rep_localOrig hh) (fun h hh => ?_) _
    (normWords_letters k)
  have hlt : h < localGenArrs.size := by simpa [localGenArrs] using hh
  rw [getElem!_pos _ h (by simpa using hlt), Array.getElem_map, ← getElem!_pos _ h hlt]
  exact rep_inv_of_isInvA (rep_localOrig hh) (fusionNormChecks_facts.2.2.2.2.2.2.1 h hh)

theorem normWordPerm_mem (k : ℕ) : normWordPerm k ∈ localChain.originalSubgroup :=
  evalWord_mem (ι := fun h : Fin 8 => localOrig h) (fun h => localOrig_mem h) _

end CFSG.Sporadic.SuzOddCore
