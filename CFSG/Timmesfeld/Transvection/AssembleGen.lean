module

public import CFSG.Timmesfeld.Transvection.Frame
public import CFSG.Timmesfeld.Transvection.LineSpan

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H]

@[expose] def deltaIn (Δ : Set (Subgroup H)) (M : Subgroup H) : Set (Subgroup H) :=
  {X | X ∈ Δ ∧ X ≤ M}

@[expose] def perpSet (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) (j : ℕ) :
    Set (Subgroup H) :=
  {X | X ∈ Δ ∧ ∀ i : Fin r, i.val < j → Commuting X (P i) ∧ Commuting X (Q i)}

theorem conjSub_mem_lineOf {Δ : Set (Subgroup H)} (hΔ : IsRootClass Δ) {A B D : Subgroup H}
    (hD : D ∈ lineOf Δ A B) (g : H) : conjSub D g ∈ lineOf Δ (conjSub A g) (conjSub B g) := by
  refine ⟨hΔ.conjSub_mem hD.1 g, fun Y hY hYA hYB => ?_⟩
  have hY' : conjSub (conjSub Y g⁻¹) g = Y := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  have h1 : Commuting (conjSub Y g⁻¹) A := by
    have := hYA.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h2 : Commuting (conjSub Y g⁻¹) B := by
    have := hYB.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h3 := (hD.2 _ (hΔ.conjSub_mem hY g⁻¹) h1 h2).conjSub g
  rwa [hY'] at h3


end CFSG.Timmesfeld.Transvection
