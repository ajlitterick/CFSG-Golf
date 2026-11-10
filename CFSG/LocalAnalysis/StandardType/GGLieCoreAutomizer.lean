module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

private theorem ggLieAut_exists_entry_ne_zero {τ : Tag} {L : Type} [Field L]
    {f : Module.End L (RootModule τ L)} (hf : f ≠ 0) :
    ∃ (a b : Label τ), f (Finsupp.single b 1) a ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  refine Finsupp.basisSingleOne.ext fun i => ?_
  simp only [Finsupp.coe_basisSingleOne, LinearMap.zero_apply]
  exact Finsupp.ext fun a => by rw [h a i, Finsupp.zero_apply]

theorem rootSubgroup_injective_of_isRoot
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h : rootSubgroup τ L γ = rootSubgroup τ L δ) : γ = δ := by
  set g : ModGL τ L := pinnedX τ L γ 1 with hgdef
  have hg1 : g ≠ 1 := by
    rw [hgdef]
    intro h1
    have h10 : (1 : L) = 0 := pinnedX_injective τ L γ (by rw [h1, pinnedX_zero])
    exact one_ne_zero h10
  have hgUγ : g ∈ rootSubgroup τ L γ := by
    rw [hgdef]; exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hgUδ : g ∈ rootSubgroup τ L δ := by rw [← h]; exact hgUγ
  have hgadj : g ∈ adjointGroup τ L := rootSubgroup_le_adjointGroup γ hgUγ
  let gA : adjointGroup τ L := ⟨g, hgadj⟩
  have hne : ((g : Module.End L (RootModule τ L)) - 1) ≠ 0 := by
    intro h0
    exact hg1 (Units.ext (sub_eq_zero.1 h0))
  obtain ⟨a, b, hab⟩ := ggLieAut_exists_entry_ne_zero hne
  have hmat : ((gA : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a -
      (Finsupp.single b 1 : RootModule τ L) a ≠ 0 := by
    have : (gA : ModGL τ L) = g := rfl
    rw [this]
    simpa using hab
  have hshiftγ : ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • γ := by
    refine (rootOperatorFamily τ).rootSubgroup_weight_shift ⟨γ, hγ⟩ gA ?_ a b hmat
    have : gA ∈ (rootSubgroup τ L γ).subgroupOf (adjointGroup τ L) := hgUγ
    rwa [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq L ⟨γ, hγ⟩] at this
  have hshiftδ : ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • δ := by
    refine (rootOperatorFamily τ).rootSubgroup_weight_shift ⟨δ, hδ⟩ gA ?_ a b hmat
    have : gA ∈ (rootSubgroup τ L δ).subgroupOf (adjointGroup τ L) := hgUδ
    rwa [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq L ⟨δ, hδ⟩] at this
  obtain ⟨k, hk1, hk⟩ := hshiftγ
  obtain ⟨k', hk'1, hk'⟩ := hshiftδ
  have hkk : k • γ = k' • δ := add_left_cancel (hk.symm.trans hk')
  obtain ⟨j, f, hf⟩ := hγ.exists_addMonoidHom_eq_single
  obtain ⟨l, f', hf'⟩ := hδ.exists_addMonoidHom_eq_single
  have hA : (k : ℤ) = (k' : ℤ) * (f δ) j := by
    have h1 : f (k • γ) = f (k' • δ) := congrArg f hkk
    rw [map_nsmul, map_nsmul, hf] at h1
    have h2 := congrFun h1 j
    simpa using h2
  have hB : (k' : ℤ) = (k : ℤ) * (f' γ) l := by
    have h1 : f' (k' • δ) = f' (k • γ) := congrArg f' hkk.symm
    rw [map_nsmul, map_nsmul, hf'] at h1
    have h2 := congrFun h1 l
    simpa using h2
  have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk1
  have hk'pos : (0 : ℤ) < (k' : ℤ) := by exact_mod_cast hk'1
  have hApos : 0 < (f δ) j := by
    by_contra hle
    push Not at hle
    nlinarith [hA, hkpos, hk'pos]
  have hunit : (f δ) j * (f' γ) l = 1 := by
    have h1 : (k : ℤ) = (k : ℤ) * ((f' γ) l * (f δ) j) := by
      calc (k : ℤ) = (k' : ℤ) * (f δ) j := hA
        _ = ((k : ℤ) * (f' γ) l) * (f δ) j := by rw [hB]
        _ = (k : ℤ) * ((f' γ) l * (f δ) j) := by ring
    have h2 : (k : ℤ) * ((f' γ) l * (f δ) j) - (k : ℤ) = 0 := by linarith
    have h3 : (k : ℤ) * ((f' γ) l * (f δ) j - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (ne_of_gt hkpos)
    · rw [mul_comm]; exact sub_eq_zero.1 h4
  have hA1 : (f δ) j = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h
    · exact h
    · exfalso; nlinarith [h, hApos]
  have hkk' : k = k' := by
    have : (k : ℤ) = (k' : ℤ) := by rw [hA, hA1, mul_one]
    exact_mod_cast this
  subst hkk'
  exact nsmul_right_injective (M := Fin τ.rank → ℤ) (n := k) (by omega) hkk


end CFSG.StandardType.LieCore
