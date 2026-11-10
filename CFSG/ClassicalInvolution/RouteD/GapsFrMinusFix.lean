module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusEigen
public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups commutatorElement

section Group

variable {Kc X : Type} [Group Kc] [Group X]

private theorem eq_of_central_perfect (α : Kc ≃* Kc) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc) : ∀ r ∈ R, α r = r := by
  have hle : ⁅R, R⁆ ≤ MonoidHom.eqLocus (α : Kc →* Kc) (MonoidHom.id Kc) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show α ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement]
    have e1 : α x = x * (x⁻¹ * α x) := by group
    have e2 : α y = y * (y⁻¹ * α y) := by group
    rw [e1, e2, CFSG.ClassicalInvolution.ModelFacts.commutatorElement_mul_central (hc x hx)
      (hc y hy)]
  intro r hr
  have hr' : r ∈ ⁅R, R⁆ := by rw [hR]; exact hr
  exact hle hr'

theorem alpha_mem_of_perfect (α : Kc ≃* Kc) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (h : ∀ r ∈ R, ∃ r' ∈ R, ∃ c ∈ Subgroup.center Kc, α r = r' * c) : ∀ r ∈ R, α r ∈ R := by
  intro r hr
  have hr' : r ∈ ⁅R, R⁆ := by rw [hR]; exact hr
  clear hr
  rw [Subgroup.commutator_def] at hr'
  induction hr' using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨y₁, hy₁, c₁, hc₁, e₁⟩ := h a ha
    obtain ⟨y₂, hy₂, c₂, hc₂, e₂⟩ := h b hb
    rw [map_commutatorElement, e₁, e₂,
      CFSG.ClassicalInvolution.RouteD.Gaps.commutator_mul_central _ _ _ _ hc₁ hc₂]
    simp only [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hy₁ hy₂) (R.inv_mem hy₁)) (R.inv_mem hy₂)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact R.mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact R.inv_mem ha

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem commute_of_fixed (θ : Kc →* X) (hker : θ.ker ≤ Subgroup.center Kc) (α : Kc ≃* Kc)
    (σ : X ≃* X) (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V)) {g : V ≃ₗ[K] V}
    (hconj : ∀ y, ρ (α y) * g = g * ρ y) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (hfix : ∀ r ∈ R, σ (θ r) = θ r) : ∀ r ∈ R, g * ρ r = ρ r * g := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hfix r hr, inv_mul_cancel])
  intro r hr
  have := hconj r
  rw [eq_of_central_perfect α hR hc r hr] at this
  exact this.symm

theorem fixed_of_commute (θ : Kc →* X) (α : Kc ≃* Kc) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V))
    (hρ : ρ.ker ≤ Subgroup.center Kc) {g : V ≃ₗ[K] V} (hconj : ∀ y, ρ (α y) * g = g * ρ y)
    {R : Subgroup Kc} (hR : ⁅R, R⁆ = R) (hcomm : ∀ r ∈ R, g * ρ r = ρ r * g) :
    ∀ r ∈ R, σ (θ r) = θ r := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hρ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : ρ (α r) * g = ρ r * g := by rw [hconj r, hcomm r hr]
    have h2 : ρ (α r) = ρ r := mul_right_cancel h1
    rw [h2, inv_mul_cancel])
  intro r hr
  rw [← hαθ, eq_of_central_perfect α hR hc r hr]

end Group

section Nodes

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem spinAction_rankOne_vec0 (h0 : 0 < n - 1) {k : Fin (n - 1)} (hk : 1 ≤ k.val)
    {r : spinGroup (quadMinus n F b c)} (hr : r ∈ rankOne (minusDatum n hirr).rootGroup k)
    (u : Bool) :
    spinAction (quadMinus n F b c) r (minusVec n ⟨0, h0⟩ u) = minusVec n ⟨0, h0⟩ u := by
  let Fix0 : Subgroup (spinGroup (quadMinus n F b c)) :=
    { carrier := {y | ∀ u, spinAction (quadMinus n F b c) y (minusVec n ⟨0, h0⟩ u) =
        minusVec n ⟨0, h0⟩ u}
      mul_mem' := fun {x y} hx hy u => by
        rw [map_mul, LinearEquiv.mul_apply, hy u, hx u]
      one_mem' := fun u => by simp
      inv_mem' := fun {x} hx u => by
        have h1 := hx u
        calc spinAction (quadMinus n F b c) x⁻¹ (minusVec n ⟨0, h0⟩ u)
            = spinAction (quadMinus n F b c) x⁻¹
                (spinAction (quadMinus n F b c) x (minusVec n ⟨0, h0⟩ u)) := by rw [h1]
          _ = minusVec n ⟨0, h0⟩ u := by
            rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl }
  have hle : rankOne (minusDatum n hirr).rootGroup k ≤ Fix0 := by
    unfold rankOne
    by_cases hlong : k.val + 1 < n - 1
    · have hij : k ≠ ⟨k.val + 1, hlong⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
      have hk0 : (⟨0, h0⟩ : Fin (n - 1)) ≠ k := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      have hk1 : (⟨0, h0⟩ : Fin (n - 1)) ≠ ⟨k.val + 1, hlong⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
      refine sup_le ?_ ?_
      · show minusRootGroup n hirr (Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_long n hirr hij true false (toStdB_single_of_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact (minusFrame n b c).toHypFrame.spinAction_longRoot_vec_of_ne hij true false a hk0 hk1 u
      · show minusRootGroup n hirr (-Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_long n hirr hij.symm true false (toStdB_neg_single_of_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact (minusFrame n b c).toHypFrame.spinAction_longRoot_vec_of_ne hij.symm true false a hk1
          hk0 u
    · have hk0 : (⟨0, h0⟩ : Fin (n - 1)) ≠ k := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      refine sup_le ?_ ?_
      · show minusRootGroup n hirr (Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_short n hirr k true (toStdB_single_of_not_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact spinAction_twShortRoot_vec_of_ne n hirr hk0 true a u
      · show minusRootGroup n hirr (-Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_short n hirr k false (toStdB_neg_single_of_not_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact spinAction_twShortRoot_vec_of_ne n hirr hk0 false a u
  exact hle hr u

end Nodes

section Perfect

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ}

private theorem rootSL2_conj_perfect (h4 : 4 ≤ Nat.card K) (F₀ : HypFrame Q m) (a b : ℕ)
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
    ⁅(rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom,
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom⁆ =
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom := by
  have : Group.IsPerfect SL(2, K) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have h1 : ⁅rootSL2 F₀ a b ha hb hab s t, rootSL2 F₀ a b ha hb hab s t⁆ =
      rootSL2 F₀ a b ha hb hab s t :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := F₀.longSL2 (i := ⟨a, ha⟩) (j := ⟨b, hb⟩)
      (fun h => hab (congrArg Fin.val h)) s t))
  rw [← Subgroup.map_commutator, h1]

end Perfect

section RankOnePerfect

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

omit [Finite F] in
private theorem comm_le_self (R : Subgroup (spinGroup (quadMinus n F b c))) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem rankOne_minusDatum_perfect' (h4 : 4 ≤ Nat.card F) (k : Fin (n - 1)) :
    ⁅rankOne (minusDatum n hirr).rootGroup k, rankOne (minusDatum n hirr).rootGroup k⁆ =
      rankOne (minusDatum n hirr).rootGroup k := by
  by_cases hk : k.val + 1 < n - 1
  · exact le_antisymm (comm_le_self _)
      (CFSG.ClassicalInvolution.RouteD.rankOne_minusDatum_perfect hirr h4 hk)
  · have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    refine le_antisymm (comm_le_self _) ?_
    rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_short hirr hk]
    exact range_perfect_of_sl2
      (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField' (b := b) (c := c)) _

end RankOnePerfect

section Main

noncomputable abbrev minusHyp {F : Type} [Field F] (n : ℕ) (b c : F) :
    HypFrame (quadMinus n F b c) (n - 1) :=
  (minusFrame n b c).toHypFrame


end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
