module

public import CFSG.Certificates.CosetTableColumns
public import CFSG.Certificates.CosetTableCompact

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ) : Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    checkC (colParams ws ((subsetOf m S).map fun x => [(x, true)])) cap n

@[expose] def subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ) :
    Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    checkHLTC (colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k) cap n

theorem subsetCheckC_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {cap n : ℕ} (h : subsetCheckCC ws S cap n = true) : subsetCheckC ws S cap n = true := by
  unfold subsetCheckCC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hc⟩ := h
  unfold subsetCheckC
  rw [← checkC_eq n hcap]
  exact hc

theorem subsetCheckShortC_of_subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortCC ws S k cap n = true) :
    subsetCheckShortC ws S k cap n = true := by
  unfold subsetCheckShortCC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hc⟩ := h
  unfold subsetCheckShortC
  rw [← checkHLTC_eq n hcap]
  exact hc

theorem card_le_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    (h : subsetCheckCC ws S cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) :=
  card_le_of_subsetCheckC ws S (subsetCheckC_of_subsetCheckCC ws S h)

theorem card_le_of_subsetCheckShortCC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortCC ws S k cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) :=
  card_le_of_subsetCheckShortC ws S (subsetCheckShortC_of_subsetCheckShortCC ws S h)

theorem card_le_of_subsetCheckCC_nil (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : subsetCheckCC ws [] cap n = true) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n :=
  card_le_of_subsetCheckC_nil ws (subsetCheckC_of_subsetCheckCC ws [] h)


end CFSG.CosetTable
