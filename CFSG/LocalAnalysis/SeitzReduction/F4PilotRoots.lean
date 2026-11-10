module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance f4PilotRootsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def rootR : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

@[expose] def rootS : Fin (Tag.rank .F4) → ℤ := ![1, 2, 3, 2]

@[expose] def C3Roots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 1, 2, 0],
    ![0, 1, 1, 1], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1],
    ![0, -1, -1, 0], ![0, 0, -1, -1], ![0, -1, -2, 0], ![0, -1, -1, -1], ![0, -1, -2, -1],
    ![0, -1, -2, -2]]


@[expose] def C3Set : Set (Fin (Tag.rank .F4) → ℤ) := {γ | γ ∈ C3Roots}


@[expose] def root1221 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 1]

@[expose] def root1242 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 4, 2]


theorem rootR_mem_rootFinset : rootR ∈ rootFinset .F4 := by decide +kernel

theorem rootS_mem_rootFinset : rootS ∈ rootFinset .F4 := by decide +kernel

theorem iform_rootR_rootS_values :
    iform rootR rootR = 4 ∧ iform rootS rootS = 2 ∧ iform rootR rootS = 2 := by decide +kernel


theorem iform_rootR_single : ∀ j : Fin (Tag.rank .F4),
    iform rootR (Pi.single j 1) = if j = 0 then 2 else 0 := by decide +kernel

theorem iform_rootS_single : ∀ j : Fin (Tag.rank .F4),
    iform rootS (Pi.single j 1) = if j = 3 then 1 else 0 := by decide +kernel

theorem C3Roots_check : (∀ γ ∈ C3Roots, γ ∈ rootFinset .F4 ∧ γ 0 = 0) ∧
    ∀ γ ∈ rootFinset .F4, γ 0 = 0 → γ ∈ C3Roots := by
  decide +kernel


theorem coeff_check : ∀ γ ∈ rootFinset .F4,
    |γ 0| ≤ 2 ∧ (γ 0 = 2 → γ = rootR) ∧ (iform γ γ = 2 → |γ 0| ≤ 1) ∧ |γ 3| ≤ 2 ∧
      (|γ 3| = 2 ↔ γ = rootS ∨ γ = -rootS ∨ (iform γ γ = 4 ∧ γ 3 ≠ 0)) ∧
      (iform γ γ = 2 ∨ iform γ γ = 4) := by
  decide +kernel


theorem iform_eq_sum_mul_iform_single {τ : Tag} (θ v : Fin τ.rank → ℤ) :
    iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem iform_rootR (v : Fin (Tag.rank .F4) → ℤ) : iform rootR v = 2 * v 0 := by
  rw [iform_eq_sum_mul_iform_single]
  simp only [iform_rootR_single, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

theorem iform_rootS (v : Fin (Tag.rank .F4) → ℤ) : iform rootS v = v 3 := by
  rw [iform_eq_sum_mul_iform_single]
  simp only [iform_rootS_single, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]


section Membership

variable {γ : Fin (Tag.rank .F4) → ℤ}

theorem isRoot_rootR : IsRoot .F4 rootR := mem_rootFinset.1 rootR_mem_rootFinset

theorem isRoot_rootS : IsRoot .F4 rootS := mem_rootFinset.1 rootS_mem_rootFinset

theorem mem_C3Roots_iff : γ ∈ C3Roots ↔ IsRoot .F4 γ ∧ γ 0 = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (C3Roots_check.1 γ h).1, (C3Roots_check.1 γ h).2⟩,
    fun h => C3Roots_check.2 γ (mem_rootFinset.2 h.1) h.2⟩

theorem mem_C3Roots_iff_iform : γ ∈ C3Roots ↔ IsRoot .F4 γ ∧ iform rootR γ = 0 := by
  rw [mem_C3Roots_iff, iform_rootR]
  exact and_congr_right fun _ => by omega


theorem mem_C3Set_iff : γ ∈ C3Set ↔ IsRoot .F4 γ ∧ γ 0 = 0 := mem_C3Roots_iff


theorem iform_self_eq_two_or_four (hγ : IsRoot .F4 γ) : iform γ γ = 2 ∨ iform γ γ = 4 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.2.2.2

theorem abs_coeff_zero_le_two (hγ : IsRoot .F4 γ) : |γ 0| ≤ 2 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).1

theorem eq_rootR_of_coeff_zero_eq_two (hγ : IsRoot .F4 γ) (h : γ 0 = 2) : γ = rootR :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.1 h


theorem abs_coeff_zero_le_one_of_short (hγ : IsRoot .F4 γ) (hs : iform γ γ = 2) : |γ 0| ≤ 1 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.1 hs


end Membership


@[expose] def rootWords : List ℕ :=
  [38151207, 38151175, 1680105511, 1680081479, 610419208, 2384454, 610418728, 2384390, 105006598,
    26881688136, 105005094, 26881303656, 9766699529, 149029, 9766699593, 147973, 6562917, 6562821,
    430107010089, 430100858441, 156267193354, 9316, 9252, 156267193450, 410180, 410116,
    6881712161290, 6881613734954, 2500275093547, 2500275095051, 579, 25635, 110105819759115,
    110105819759179, 40004401520684, 34, 1602, 1761693116146700, 640070424330829, 1, 97,
    28187089858347053, 10241126789293102, 0, 0, 450993437733552718, 163858028628689423,
    7215895003736843375]

@[expose] def rootWordsCheck : Bool :=
  (List.range 48).all fun k =>
    wordPos Tag.F4.rootCertificate (decodeWord (rootWords.getD k 0)) k ==
      if iform (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k) = 4 then 43 else 44

theorem rootWordsCheck_eq_true : rootWordsCheck = true := by decide +kernel


theorem certificate_positions :
    Tag.F4.rootCertificate.roots.length = 48 ∧ Tag.F4.rootCertificate.root 43 = rootR ∧
      Tag.F4.rootCertificate.root 44 = rootS ∧ Tag.F4.rootCertificate.root 25 = ![0, 1, 2, 1] ∧
      Tag.F4.rootCertificate.root 1 = ![0, 1, 0, 0] ∧
      Tag.F4.rootCertificate.root 0 = ![1, 0, 0, 0] ∧
      Tag.F4.rootCertificate.root 35 = root1242 ∧
      Tag.F4.rootCertificate.root 36 = root1221 ∧
      Tag.F4.rootCertificate.root 15 = ![0, 1, 2, 2] ∧
      Tag.F4.rootCertificate.root 8 = ![0, 1, 1, 0] :=
  ⟨by decide +kernel, List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem explicitWords_check :
    wordPos Tag.F4.rootCertificate [0, 1] 43 = 35 ∧
    wordPos Tag.F4.rootCertificate [0, 2, 1, 3, 2, 1, 0] 43 = 15 ∧
    wordPos Tag.F4.rootCertificate [0, 2, 1, 3, 2, 1, 0] 44 = 25 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 44 = 25 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 36 = 8 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 35 = 15 := by
  decide +kernel

section Weyl


theorem weylOfWord_smul_root_of_wordPos {ω : List ℕ} {k k' : ℕ} (hk : k < 48)
    (h : wordPos Tag.F4.rootCertificate ω k = k') :
    weylOfWord .F4 ω • Tag.F4.rootCertificate.root k = Tag.F4.rootCertificate.root k' := by
  rw [← h, ← (wordPos_spec (Tag.rootCertificate_check .F4) ω
    (by rw [certificate_positions.1]; exact hk)).2]

theorem exists_smul_eq_rootR {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hl : iform γ γ = 4) : ∃ w : WeylGroup .F4, w • γ = rootR := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  rw [certificate_positions.1] at hk
  have h := rootWordsCheck_eq_true
  simp only [rootWordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk' := h k hk
  rw [ite_eq_left hl] at hk'
  exact ⟨_, (weylOfWord_smul_root_of_wordPos hk hk').trans certificate_positions.2.1⟩

theorem exists_smul_eq_rootS {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hs : iform γ γ = 2) : ∃ w : WeylGroup .F4, w • γ = rootS := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  rw [certificate_positions.1] at hk
  have h := rootWordsCheck_eq_true
  simp only [rootWordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk' := h k hk
  rw [ite_eq_right (by omega)] at hk'
  exact ⟨_, (weylOfWord_smul_root_of_wordPos hk hk').trans certificate_positions.2.2.1⟩


theorem weylOfWord_rootR_rootS_mem_C3Roots :
    weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0] • rootR = ![0, 1, 2, 2] ∧
      weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0] • rootS = ![0, 1, 2, 1] := by
  constructor
  · rw [← certificate_positions.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.1, certificate_positions.2.2.2.2.2.2.2.2.1]
  · rw [← certificate_positions.2.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.2.1, certificate_positions.2.2.2.1]


end Weyl

end CFSG.SeitzReduction.F4Pilot
