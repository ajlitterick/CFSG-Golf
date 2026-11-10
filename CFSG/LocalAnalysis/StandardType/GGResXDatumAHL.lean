module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGHLFrame
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggHLT_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

lemma ggHLT_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨2 ^ k - 1, by omega⟩

lemma ggHLT_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ k, by omega⟩

lemma ggHLT_odd_ggTorM {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorM lab) := by
  unfold ggTorM
  split_ifs with h
  · exact ggHLT_odd_two_pow_add_one hlab.1
  · exact ggHLT_odd_two_pow_sub_one hlab.1

lemma ggHLT_weyl_A {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl _, hn, Or.inl (ggHLT_coxeter_reindex_refl _)⟩

theorem ggHLT_lin {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {x : G} (hxB : x ∈ Bs) (hxX : x ∈ Subgroup.centralizer (X : Set G)) :
    ∃ (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs)
      (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
        v - α i v • ι (Additive.ofMul ⟨_, hbk i⟩)) ∧
      (∀ i j, α i (ι (Additive.ofMul ⟨_, hbk j⟩)) = (C i j : ZMod p)) ∧
      (∀ i, α i (ι (Additive.ofMul ⟨x, hxB⟩)) = 0) := by
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin N → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin N → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  refine ⟨hnk, hbk, α, fun i v => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hF1 i ⟨x, hxB⟩ ((ggGamma_eq_one_iff X hN _).mpr hxX)


end CFSG.StandardType
