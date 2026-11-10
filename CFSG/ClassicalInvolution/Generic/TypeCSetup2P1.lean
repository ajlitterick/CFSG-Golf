module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupInputs
import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality
import CFSG.ClassicalInvolution.Balance.BootstrapUntouched
import CFSG.ClassicalInvolution.Balance.Theorem5Untouched

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

section Component

omit [Finite G] in
private theorem mathlib_isSubnormal_subgroupOf {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commutes_of_component_of_normalized {H L M : Subgroup G} (hL : IsComponentOf L H)
    (hMH : M ≤ H) (hMn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (hodd : Odd (Nat.card M)) :
    ∀ l ∈ L, ∀ m ∈ M, l * m = m * l := by
  have hL' : IsComponentOf (L.subgroupOf H) ⊤ := by
    refine ⟨le_top, ?_, Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hL.1)
      hL.2.2⟩
    exact Components.chain_of_mathlib_subnormal (mathlib_isSubnormal_subgroupOf hL.2.1)
  have hMn' : (M.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMH]
    exact fun x c hx hc => hMn c hc x hx
  have hsolv : Group.IsSolvable ↥M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv' : Group.IsSolvable ↥(M.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hMH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMH).injective
  have hcomm := LocalComponents.commutes_with_solvable_subnormal (L.subgroupOf H)
    (M.subgroupOf H) hL' (isSubnormal_of_normal_subgroupOf le_top inferInstance)
  intro l hl m hm
  have h1 : (⟨l, hL.1 hl⟩ : ↥H) ∈ L.subgroupOf H := hl
  have h2 : (⟨m, hMH hm⟩ : ↥H) ∈ M.subgroupOf H := hm
  have h3 := Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact congrArg Subtype.val h3

end Component

section Member

variable [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem isQuasisimple_member_of_deltaCore_eq_bot (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {L : Subgroup G} {w : G} (hLΩ : L ∈ Ω) (hw : IsClassicalMember p f L w) {F : Subgroup G}
    (hF : IsElemAbelian 2 F) (hLF : L ≤ Subgroup.centralizer (F : Set G))
    (hΔ : deltaCore F = ⊥) : CFSG.Open.IsQuasisimple L := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hW : WeakMember (GaloisField p f) L w :=
    ⟨hw.orderOf_eq_two, hw.mem, hw.perfect, hw.subnormal, hw.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  set C : Subgroup G := Subgroup.centralizer ({w} : Set G) with hC
  have hzF : ∀ x ∈ F, w * x = x * w := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hLF hw.mem) x hx).symm
  have hFC : F ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hzF x hx).symm
  have hsub : IsSubnormal L (C ⊓ Subgroup.centralizer (F : Set G)) := by
    have h := isSubnormal_inf hw.subnormal (C ⊓ Subgroup.centralizer (F : Set G))
    rwa [inf_eq_left.mpr (le_inf (isSubnormal_le hw.subnormal) hLF),
      inf_eq_right.mpr inf_le_left] at h
  refine isQuasisimple_of_deltaCore_eq_bot_layer hw.subnormal hmem.perfect hmem.quasisimple hF
    hFC hLF hΔ hsub ?_
  intro f₀ hf₀ hf₀1 M hM
  exact hB_of_localLieSystems hp2 CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hLΩ hw.isCentralInvolution
    (not_subset_center_of_ne_one hnab hf₀1)
    (hLF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₀))) (hzF f₀ hf₀) M hM

theorem member_commutes_oddCoreIn_of_deltaCore_eq_bot (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {x w : G} {F : Subgroup G} (hxF : x ∈ F) (hwF : w ∈ F) (hF : IsElemAbelian 2 F)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hw : IsClassicalMember p f L w)
    (hLF : L ≤ Subgroup.centralizer (F : Set G)) (hΔ : deltaCore F = ⊥)
    (hN : oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤ Subgroup.centralizer (F : Set G)) :
    ∀ n ∈ oddCoreIn (Subgroup.centralizer ({x} : Set G)), ∀ l ∈ L, n * l = l * n := by
  have hqs := isQuasisimple_member_of_deltaCore_eq_bot hnab hp2 hq hΩ hIH hLΩ hw hF hLF hΔ
  set H : Subgroup G := Subgroup.centralizer (F : Set G) with hH
  have hHw : H ≤ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF)
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxF)
  have hsub : IsSubnormal L H := by
    have h := isSubnormal_inf hw.subnormal H
    rwa [inf_eq_left.mpr hLF, inf_eq_right.mpr hHw] at h
  intro n hn l hl
  exact (commutes_of_component_of_normalized ⟨hLF, hsub, hqs⟩ hN
    (fun h hh m hm => conj_mem_oddCoreIn (hHx hh) hm) (odd_card_oddCoreIn _) l hl n hn).symm

end Member

section Alpha

omit [Finite G] in
private theorem closure_pair_conj (g a b : G) :
    Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({a, b} : Set G)) := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

omit [Finite G] in
private theorem closure_pair_mul_left (a b : G) :
    Subgroup.closure ({a, a * b} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h1 : (a : G) ∈ Subgroup.closure ({a, a * x} : Set G) := Subgroup.subset_closure (by simp)
      have h2 : a * x ∈ Subgroup.closure ({a, a * x} : Set G) := Subgroup.subset_closure (by simp)
      have := mul_mem (inv_mem h1) h2
      simpa using this

omit [Finite G] in
theorem alphaCore_conjSub_eq_bot {F : Subgroup G} (h : alphaCore F = ⊥) (g : G) :
    alphaCore (conjSub g F) = ⊥ := by
  have := Theorem5.alphaCore_map g F
  rw [h, Subgroup.map_bot] at this
  exact this.symm

omit [Finite G] in
theorem oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot {F : Subgroup G} {x : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) (h : alphaCore F = ⊥) :
    oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤ Subgroup.centralizer (F : Set G) := by
  intro u hu
  have huF : u ∈ uCore F := involutionOddCore_le_uCore hxF hx1 hu
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : ⁅u, f⁆ ∈ alphaCore F := commutator_le_alphaCore (Subgroup.commutator_mem_commutator
    huF hf)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end Alpha

section Local


end Local

section Edge


end Edge


end CFSG.ClassicalInvolution.Generic.TypeCSetup
