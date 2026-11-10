module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

@[expose] def IsOddLieComponent3 {X : Type} [Group X] (L : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (n : ℕ), (t = .PSL → 3 ≤ n) ∧
    (t ∈ CFSG.Blueprint.classicalTags ∨ t ∈ CFSG.Blueprint.chevalleyExceptionalTags) ∧
    CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) t n 3 1

structure LieDecomposition3 {X : Type} [Group X] (Ψ : Set (Subgroup X)) (Y : Subgroup X) where
  ι : Type
  Q : ι → Subgroup X
  commute : ∀ i j, i ≠ j → Commutes (Q i) (Q j)
  iSup_eq : ⨆ i, Q i = Y
  exists_le : ∀ L ∈ Ψ, ∃ i, L ≤ Q i
  kind : ∀ i, ((∃ L ∈ Ψ, L = Q i) ∧ (∀ L ∈ Ψ, L ≤ Q i → L = Q i) ∧ Group.IsSolvable (Q i)) ∨
    (CFSG.Open.IsQuasisimple (Q i) ∧ IsOddLieComponent3 (Q i)) ∨
    (CFSG.Open.IsQuasisimple (Q i) ∧ Nonempty (↥(Q i) ≃* ↥CFSG.Blueprint.NativeSporadic.M11))

theorem LieDecomposition3.congr {X : Type} [Group X] {Ψ Ψ' : Set (Subgroup X)}
    {Y Y' : Subgroup X} (hΨ : Ψ = Ψ') (hY : Y = Y') :
    Nonempty (LieDecomposition3 Ψ Y) → Nonempty (LieDecomposition3 Ψ' Y') := by
  subst hΨ
  subst hY
  exact id

section Abstract

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

theorem range_model3 (h0 : ModelClauseZero) {c : CompData} {t : StatedLieTag} {n : ℕ}
    (ht : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n)
    (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G) (hψ1 : ∃ x, ψ x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥ψ.range ∧ IsOddLieComponent3 ψ.range := by
  subst hc
  obtain ⟨hK, hmodel⟩ := h0 t n 3 1 Nat.prime_three ht hadm
  have hq := Quasisimple.central_quotient hK ψ.ker hker
  refine ⟨Components.quasisimple_of_equiv (QuotientGroup.quotientKerEquivRange ψ).symm hq, ?_⟩
  have hn : t = .PSL → 3 ≤ n := by
    intro h
    subst h
    have h2 : 2 ≤ n := hadm.2.2.1
    have h3 : (n, 3 ^ 1) ≠ (2, 3) := hadm.2.2.2.2
    have : n ≠ 2 := fun h => h3 (by simp [h])
    omega
  have hψ1' : ∃ x, ψ.rangeRestrict x ≠ 1 := by
    obtain ⟨x, hx⟩ := hψ1
    exact ⟨x, fun h => hx (congrArg Subtype.val h)⟩
  exact ⟨t, n, hn, isFundTag_mem_tags ht,
    lieModel_of_surjective hK ψ.rangeRestrict ψ.rangeRestrict_surjective hψ1' hmodel⟩

theorem range_m11 (hM : M11Facts) {c : CompData} (hc : c = CompData.m11) (ψ : c.G →* X)
    (hψ1 : ∃ x, ψ x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥ψ.range ∧
      Nonempty (↥ψ.range ≃* ↥CFSG.Blueprint.NativeSporadic.M11) := by
  subst hc
  obtain ⟨hsimple, hcard⟩ := hM
  have hker : ψ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker ψ).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hψ1
      exact hx (by
        have : x ∈ ψ.ker := by rw [h]; trivial
        exact this)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* ↥ψ.range := MonoidHom.ofInjective hinj
  have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Std.Commutative (α := ↥CFSG.Blueprint.NativeSporadic.M11) (· * ·) :=
      ⟨fun a b => hcon a b⟩
    have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hcomm⟩
    have hp := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
    rw [hcard] at hp
    norm_num at hp
  have hq : CFSG.Open.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M11 := by
    have := hsimple
    obtain ⟨a, b, hab⟩ := hnab
    have hcenter : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
      rcases (inferInstance : (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11).Normal
        ).eq_bot_or_eq_top with h | h
      · exact h
      · exact (hab (Subgroup.mem_center_iff.mp (by rw [h]; trivial : a ∈ _) b).symm).elim
    have hcomm : commutator ↥CFSG.Blueprint.NativeSporadic.M11 = ⊤ := by
      rcases (inferInstance : (commutator ↥CFSG.Blueprint.NativeSporadic.M11).Normal
        ).eq_bot_or_eq_top with h | h
      · exfalso
        have h1 : ⁅a, b⁆ ∈ commutator ↥CFSG.Blueprint.NativeSporadic.M11 :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact hab h1
      · exact h
    exact ⟨hcomm, ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  exact ⟨Components.quasisimple_of_equiv e.symm hq, ⟨e.symm⟩⟩

theorem fund_eq_top_of_sl23 {c : CompData} (hc : c = CompData.sl23) :
    ∀ R ∈ c.fund, R = (⊤ : Subgroup c.G) := by
  subst hc
  intro R hR
  exact hR

theorem isSolvable_range_of_sl23 {c : CompData} (hc : c = CompData.sl23) (ψ : c.G →* X) :
    Group.IsSolvable ↥ψ.range := by
  subst hc
  have := isSolvable_sl2Three
  exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective


end Abstract

section Components

variable {X : Type} [Group X] {Ψ : Set (Subgroup X)} {Y : Subgroup X}

namespace LieDecomposition3

variable (D : LieDecomposition3 Ψ Y)

theorem le_join (i : D.ι) : D.Q i ≤ Y := (le_iSup D.Q i).trans D.iSup_eq.le

theorem normal_subgroupOf (i : D.ι) : ((D.Q i).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (D.le_join i)]
  have key : ∀ g ∈ (⨆ j, D.Q j : Subgroup X), ∀ n ∈ D.Q i, g * n * g⁻¹ ∈ D.Q i := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.Q k).mul_mem ((D.Q k).mul_mem hy hn) ((D.Q k).inv_mem hy)
      · have := D.commute k i hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  intro q y hq hy
  exact key y (D.iSup_eq.ge hy) q hq

theorem isSubnormal_top [Y.Normal] (i : D.ι) : IsSubnormal (D.Q i) ⊤ :=
  IsSubnormal.step (D.le_join i) (D.normal_subgroupOf i)
    (isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf)

theorem isComponentOf [Y.Normal] (i : D.ι) (hq : CFSG.Open.IsQuasisimple (D.Q i)) :
    IsComponentOf (D.Q i) ⊤ :=
  ⟨le_top, D.isSubnormal_top i, hq⟩

theorem eq_or_commutes_of_isComponentOf [Finite X] [Y.Normal] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : (∃ i, L = D.Q i) ∨ Commutes L Y := by
  by_cases h : ∃ i, L = D.Q i
  · exact Or.inl h
  · right
    push Not at h
    have hle : Y ≤ Subgroup.centralizer (L : Set X) := by
      rw [← D.iSup_eq]
      refine iSup_le fun i => ?_
      have hc : ⁅L, D.Q i⁆ = ⊥ := by
        rcases D.kind i with ⟨-, -, hsolv⟩ | ⟨hq, -⟩ | ⟨hq, -⟩
        · have := hsolv
          exact LocalComponents.commutes_with_solvable_subnormal L (D.Q i) hL
            (D.isSubnormal_top i)
        · exact LocalComponents.commute_of_ne L (D.Q i) hL (D.isComponentOf i hq) (h i)
        · exact LocalComponents.commute_of_ne L (D.Q i) hL (D.isComponentOf i hq) (h i)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rwa [Subgroup.commutator_comm])
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x hx

end LieDecomposition3

end Components

section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem not_le_center_of_mem3 (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ centMembers Ω a) :
    ¬ (K.subgroupOf (centLayer Ω a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω a))) ≤
      Subgroup.center (↥(centLayer Ω a) ⧸ classicalInvolutionOddCore ↥(centLayer Ω a)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
  exact (hz.subgroupOf (le_centLayer hK)).map_oddQuotient.not_le_center


end Local


section Balance


end Balance

end CFSG.ClassicalInvolution.Q3
