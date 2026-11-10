module

public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.Quasithin.Background.E2TenKG
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

namespace Pair

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem isSz_of_mulEquiv {A B : Type} [Group A] [Group B] {n : ℕ} (e : A ≃* B) (h : IsSz n B) :
    IsSz n A := by
  obtain ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨f⟩⟩ := h
  exact ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨e.trans f⟩⟩

theorem center_commutator_seven
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Pair X T M V g) {n : ℕ} (hn : 1 < n)
    (hY : IsPSL 2 2 n (StarQuot M X) ∨ IsSz n (StarQuot M X))
    [((PP M V X g).subgroupOf X).Normal] :
    (Subgroup.center ↥(commutator (Xbar M V X g)) = ⊥ ∨
      (IsSz 3 (StarQuot M X) ∧ ∀ z ∈ Subgroup.center ↥(commutator (Xbar M V X g)), z * z = 1)) ∧
    ∀ l ∈ commutator (Xbar M V X g),
      l * l ∈ (Subgroup.center ↥(commutator (Xbar M V X g))).map
        (commutator (Xbar M V X g)).subtype → l * l = 1 := by
  have hXs := isSimpleGroup_of_psl_or_sz hY
  have hXp := commutator_eq_top_of_psl_or_sz hn hY
  have hXna := nonabelian_of_psl_or_sz hn hY
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator (Xbar M V X g ⧸ Jbar M V X g) = ⊤ := commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g) := MulEquiv.isSimpleGroup e
  have hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := h.Jbar_le_center
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator _ hJc hS hsimp hna
  set Lb := commutator (Xbar M V X g) with hLb
  have : Group.IsPerfect ↥Lb := hLq.1
  set eX : ↥Lb ⧸ Subgroup.center ↥Lb ≃* StarQuot M X := eL.trans e
  have hcase : Subgroup.center ↥Lb = ⊥ ∨
      (IsSz 3 (StarQuot M X) ∧ ∀ z ∈ Subgroup.center ↥Lb, z * z = 1) := by
    rcases hY with hY | hY
    · left
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · have hZ2 := sq_eq_one_of_mem_center_isPSL_two hY eX
        have hP2 : IsPGroup 2 (Subgroup.center ↥Lb) := fun z =>
          ⟨1, Subtype.ext (by simpa [pow_two] using hZ2 z z.2)⟩
        obtain ⟨e5⟩ := nonempty_alt_five_of_isPSL_two hY
        obtain ⟨v₁, hv₁, v₂, hv₂, h₁, h₂, h₁₂⟩ := h.exists_two_Vbar hsimp hna
        exact center_commutator_eq_bot_of_alt_five _ hKG3 hJc hS hsimp hna (e.trans e5) hP2
          h.Vbar_sq hv₁ hv₂ h₁ h₂ h₁₂
      · exact center_eq_bot_of_isPSL hn3 hY eX
    · by_cases hn3 : n = 3
      · subst hn3
        exact Or.inr ⟨hY, sq_eq_one_of_mem_center_isSz_three hY eX⟩
      · exact Or.inl (center_eq_bot_of_isSz hn3 hY eX)
  have hlift : ∀ l ∈ Lb, l * l ∈ (Subgroup.center ↥Lb).map Lb.subtype → l * l = 1 := by
    by_cases hb : Subgroup.center ↥Lb = ⊥
    · exact lift_of_center_eq_bot hb
    · obtain ⟨hSz, hZ2⟩ := hcase.resolve_left hb
      exact lift_of_involutions_lift hZ2 (hKG1 ↥Lb hLq hb (isSz_of_mulEquiv eX hSz)).1
  exact ⟨hcase, hlift⟩


theorem center_seven
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Pair X T M V g) {n : ℕ} (hn : 1 < n)
    (hY : IsPSL 2 2 n (StarQuot M X) ∨ IsSz n (StarQuot M X))
    [((PP M V X g).subgroupOf X).Normal] :
    Subgroup.center (Xbar M V X g) = Jbar M V X g ∧
      (∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1) ∧ pCoreOf 2 X = kerIn M X :=
  h.center_quot_facts (isSimpleGroup_of_psl_or_sz hY) (commutator_eq_top_of_psl_or_sz hn hY)
    (nonabelian_of_psl_or_sz hn hY) (h.center_commutator_seven hKG1 hKG3 hn hY).2

end Pair

end E2


end CFSG.Quasithin
