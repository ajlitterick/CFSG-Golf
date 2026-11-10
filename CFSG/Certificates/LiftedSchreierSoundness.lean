module

public import CFSG.Certificates.LiftedSchreierSearch
public import CFSG.Certificates.SchreierChainOrder

public noncomputable section

namespace CFSG.Certificates

variable {n : ℕ} {K : Type*} [Group K]

theorem map_schreierWordValue {G G' : Type*} [Group G] [Group G'] (f : G →* G') {r : ℕ}
    (S : Fin r → G) (j : ℕ) (hj : j ≤ r) (w : List (SchreierLetter j)) :
    f (schreierWordValue S j hj w) = schreierWordValue (fun l => f (S l)) j hj w := by
  induction w with
  | nil => rw [schreierWordValue_nil, schreierWordValue_nil, map_one]
  | cons a w ih =>
    rcases a with ⟨a, _ | _⟩
    · rw [schreierWordValue_cons_negative, schreierWordValue_cons_negative, map_mul, map_inv,
        ih]
    · rw [schreierWordValue_cons_positive, schreierWordValue_cons_positive, map_mul, ih]

theorem schreierWordValue_congr {G : Type*} [Group G] {r r' : ℕ} (S : Fin r → G)
    (S' : Fin r' → G) (j : ℕ) (hj : j ≤ r) (hj' : j ≤ r')
    (hS : ∀ a : Fin j, S ⟨a.val, a.isLt.trans_le hj⟩ = S' ⟨a.val, a.isLt.trans_le hj'⟩)
    (w : List (SchreierLetter j)) : schreierWordValue S j hj w = schreierWordValue S' j hj' w := by
  unfold schreierWordValue
  congr 1
  funext a
  exact hS a

namespace ValidLiftedSchreier

variable {Q : RawSchreierDatum n} {φ : K →* Equiv.Perm (Fin n)} {U : Vector K Q.originalCount}

theorem lift_image (hV : ValidLiftedSchreier Q φ U) (j : Fin Q.strongCount) :
    φ (Q.lift U j) = Q.strong.get j := by
  have hvalid := (validSchreier_iff Q).1 hV.valid
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount, j.val = a → φ (Q.lift U j) = Q.strong.get j := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · have hcast : Fin.castLE Q.originalCount_le ⟨j.val, hj⟩ = j := Fin.ext rfl
        rw [Q.lift_of_lt U j hj, hV.original_image, ← hvalid.1 ⟨j.val, hj⟩, hcast]
      · have hm := Nat.le_of_not_lt hj
        rw [Q.lift_of_le U j hm, map_schreierWordValue, hvalid.2.1 j hm,
          RawSchreierDatum.derivationValue]
        apply schreierWordValue_congr
        intro l
        exact ih l.val (by omega) _ rfl
  exact all j.val j rfl


theorem schreier_mem_next (hV : ValidLiftedSchreier Q φ U) (i : Fin Q.baseCount) (g : K)
    (hg : g ∈ Q.liftedLevelSubgroup U i.val) :
    ∀ (x : Fin n) (tx : K), Q.liftedTransversal? U i x = some tx →
      ∃ ty, Q.liftedTransversal? U i (φ g x) = some ty ∧
        ty⁻¹ * g * tx ∈ Q.liftedLevelSubgroup U (i.val + 1) := by
  refine Subgroup.closure_induction_left
    (p := fun g _ => ∀ (x : Fin n) (tx : K), Q.liftedTransversal? U i x = some tx →
      ∃ ty, Q.liftedTransversal? U i (φ g x) = some ty ∧
        ty⁻¹ * g * tx ∈ Q.liftedLevelSubgroup U (i.val + 1)) ?_ ?_ ?_ hg
  · intro x tx htx
    refine ⟨tx, by simpa using htx, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro s hs g _ ih x tx htx
    obtain ⟨tz, htz, hmem⟩ := ih x tx htx
    obtain ⟨j, hj, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U i.val s).1 hs
    have hp : (Q.strong.get j, Q.lift U j) ∈ Q.liftedLevelSteps U i.val :=
      (Q.mem_liftedLevelSteps_iff U i.val _).2 ⟨j, hj, Or.inl rfl⟩
    obtain ⟨tw, htw, hsift⟩ := hV.schreier i (φ g x) tz htz _ hp
    refine ⟨tw, ?_, ?_⟩
    · rw [map_mul, Equiv.Perm.mul_apply, hV.lift_image j]
      exact htw
    · have h₁ := Q.liftSift_mem φ U (i.val + 1) _ hsift
      have h₂ := Subgroup.mul_mem _ h₁ hmem
      convert h₂ using 1
      group
  · intro s hs g _ ih x tx htx
    obtain ⟨tz, htz, hmem⟩ := ih x tx htx
    obtain ⟨j, hj, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U i.val s).1 hs
    have hp : (Q.strong.get j, Q.lift U j)⁻¹ ∈ Q.liftedLevelSteps U i.val :=
      (Q.mem_liftedLevelSteps_iff U i.val _).2 ⟨j, hj, Or.inr rfl⟩
    obtain ⟨tw, htw, hsift⟩ := hV.schreier i (φ g x) tz htz _ hp
    refine ⟨tw, ?_, ?_⟩
    · rw [map_mul, Equiv.Perm.mul_apply, map_inv, hV.lift_image j]
      exact htw
    · have h₁ := Q.liftSift_mem φ U (i.val + 1) _ hsift
      have h₂ := Subgroup.mul_mem _ h₁ hmem
      convert h₂ using 1
      simp only [Prod.snd_inv]
      group

theorem liftedLevelSubgroup_succ (hV : ValidLiftedSchreier Q φ U) (i : Fin Q.baseCount) :
    Q.liftedLevelSubgroup U (i.val + 1) = Q.liftedLevelSubgroup U i.val ⊓
      (MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i)).comap φ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro h hh
    obtain ⟨j, hj, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U _ h).1 hh
    rw [SetLike.mem_coe, Subgroup.mem_inf]
    refine ⟨Q.lift_mem_liftedLevelSubgroup U i.val j
      (Q.levelIndices_subset i.val (i.val + 1) (Nat.le_succ _) hj), ?_⟩
    rw [Subgroup.mem_comap, hV.lift_image j, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    apply (Q.mem_levelIndices_iff (i.val + 1) j).1 hj
    rw [Q.base_take_succ i]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def] at hg
    obtain ⟨hg, hstab⟩ := hg
    obtain ⟨ty, hty, hmem⟩ :=
      hV.schreier_mem_next i g hg (Q.base.get i) 1 (Q.liftedTransversal_root U i)
    rw [hstab, Q.liftedTransversal_root U i, Option.some.injEq] at hty
    rw [← hty, inv_one, one_mul, mul_one] at hmem
    exact hmem

theorem mem_liftedLevelSubgroup_iff (hV : ValidLiftedSchreier Q φ U) (i : ℕ)
    (hi : i ≤ Q.baseCount) (g : K) :
    g ∈ Q.liftedLevelSubgroup U i ↔
      g ∈ Q.liftedOriginalSubgroup U ∧ ∀ b ∈ Q.base.toList.take i, φ g b = b := by
  induction i with
  | zero => simp [Q.liftedLevelSubgroup_zero U]
  | succ i ih =>
    let j : Fin Q.baseCount := ⟨i, by omega⟩
    rw [hV.liftedLevelSubgroup_succ j]
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def]
    rw [ih (by omega), Q.base_take_succ j]
    constructor
    · rintro ⟨⟨hg, hfix⟩, hlast⟩
      refine ⟨hg, fun b hb => ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · exact hfix b hb
      · rw [List.mem_singleton.1 hb]
        exact hlast
    · rintro ⟨hg, hfix⟩
      exact ⟨⟨hg, fun b hb => hfix b (List.mem_append_left _ hb)⟩,
        hfix _ (List.mem_append_right _ (List.mem_singleton_self _))⟩


theorem liftedLevelSubgroup_terminal (hV : ValidLiftedSchreier Q φ U) :
    Q.liftedLevelSubgroup U Q.baseCount = ⊥ :=
  Subgroup.closure_eq_bot_iff.2 fun h hh => hV.terminal h hh

theorem eq_one_of_map_eq_one (hV : ValidLiftedSchreier Q φ U) {g : K}
    (hg : g ∈ Q.liftedOriginalSubgroup U) (h1 : φ g = 1) : g = 1 := by
  have hk : g ∈ Q.liftedLevelSubgroup U Q.baseCount :=
    (hV.mem_liftedLevelSubgroup_iff Q.baseCount le_rfl g).2 ⟨hg, fun b _ => by rw [h1]; rfl⟩
  rw [hV.liftedLevelSubgroup_terminal] at hk
  exact Subgroup.mem_bot.1 hk

theorem injOn (hV : ValidLiftedSchreier Q φ U) {g g' : K} (hg : g ∈ Q.liftedOriginalSubgroup U)
    (hg' : g' ∈ Q.liftedOriginalSubgroup U) (h : φ g = φ g') : g = g' := by
  have h1 := hV.eq_one_of_map_eq_one (mul_mem (inv_mem hg') hg)
    (by rw [map_mul, map_inv, h, inv_mul_cancel])
  exact (inv_mul_eq_one.1 h1).symm

theorem map_liftedOriginalSubgroup (hV : ValidLiftedSchreier Q φ U) :
    (Q.liftedOriginalSubgroup U).map φ = Q.originalSubgroup := by
  rw [RawSchreierDatum.liftedOriginalSubgroup, MonoidHom.map_closure,
    RawSchreierDatum.originalSubgroup]
  congr 1
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get U u).1 hu
    rw [hV.original_image j]
    exact schreier_vector_get_mem_toList _ j
  · intro ha
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.original a).1 ha
    exact ⟨U.get j, schreier_vector_get_mem_toList U j, hV.original_image j⟩

theorem map_mem_originalSubgroup (hV : ValidLiftedSchreier Q φ U)
    (g : Q.liftedOriginalSubgroup U) : φ g ∈ Q.originalSubgroup := by
  rw [← hV.map_liftedOriginalSubgroup]
  exact Subgroup.mem_map_of_mem φ g.property

@[expose] def liftedRestrict (hV : ValidLiftedSchreier Q φ U) :
    Q.liftedOriginalSubgroup U →* Q.originalSubgroup :=
  (φ.comp (Q.liftedOriginalSubgroup U).subtype).codRestrict Q.originalSubgroup
    hV.map_mem_originalSubgroup


theorem liftedRestrict_bijective (hV : ValidLiftedSchreier Q φ U) :
    Function.Bijective hV.liftedRestrict := by
  constructor
  · intro g g' h
    exact Subtype.ext (hV.injOn g.property g'.property (congrArg Subtype.val h))
  · intro a
    have ha : (a : Equiv.Perm (Fin n)) ∈ (Q.liftedOriginalSubgroup U).map φ := by
      rw [hV.map_liftedOriginalSubgroup]
      exact a.property
    obtain ⟨g, hg, hga⟩ := ha
    exact ⟨⟨g, hg⟩, Subtype.ext hga⟩

@[expose] def restrictEquiv (hV : ValidLiftedSchreier Q φ U) :
    Q.liftedOriginalSubgroup U ≃* Q.originalSubgroup :=
  MulEquiv.ofBijective hV.liftedRestrict hV.liftedRestrict_bijective

theorem restrictEquiv_apply (hV : ValidLiftedSchreier Q φ U) (g : Q.liftedOriginalSubgroup U) :
    (hV.restrictEquiv g : Equiv.Perm (Fin n)) = φ g := rfl


theorem finite (hV : ValidLiftedSchreier Q φ U) : Finite (Q.liftedOriginalSubgroup U) :=
  Finite.of_equiv _ hV.restrictEquiv.symm.toEquiv

theorem card_eq (hV : ValidLiftedSchreier Q φ U) :
    Nat.card (Q.liftedOriginalSubgroup U) = ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i) := by
  rw [Nat.card_congr hV.restrictEquiv.toEquiv, Q.original_card_eq_orbit_product hV.valid]


end ValidLiftedSchreier


end CFSG.Certificates
