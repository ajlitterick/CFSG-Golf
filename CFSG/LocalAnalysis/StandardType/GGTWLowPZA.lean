module

public import Certificates.Data.TwoDepSmallLow
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private lemma l05nLA_fact_eq (n : ℕ) : ggTWLFact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (n + 1) * ggTWLFact n = (n + 1).factorial
      rw [ih, Nat.factorial_succ]

private lemma l05nLA_weylType_mem {r n c : ℕ} (h : GGWeylTypeData r n c) :
    (n, c) ∈ ggTWLWeylTypes r := by
  rcases h with ⟨h1, hn, hc⟩ | ⟨h2, hn, hc⟩ | ⟨h4, hn, hc⟩ | ⟨hr, hn, hc⟩ |
    ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩ | ⟨hr, hn, hc⟩
  · obtain rfl := hn; obtain rfl := hc
    simp [ggTWLWeylTypes, h1, l05nLA_fact_eq]
  · obtain rfl := hn; obtain rfl := hc
    simp [ggTWLWeylTypes, h2, l05nLA_fact_eq]
  · obtain rfl := hn
    have hev : Even r ↔ r % 2 = 0 := by rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    have hc' : c = if r % 2 = 0 then 2 else 1 := by rw [hc, if_congr hev rfl rfl]
    obtain rfl := hc'
    simp [ggTWLWeylTypes, h4, l05nLA_fact_eq]
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide
  · obtain rfl := hr; obtain rfl := hn; obtain rfl := hc; decide

theorem ggTWLPZArith_sound {N K : ℕ} {hasCen : Bool} (h : ggTWLPZArith N K hasCen = true)
    {r n c : ℕ} (ht : GGWeylTypeData r n c) (hlo : N - 3 ≤ r) (hhi : r ≤ N - 1)
    (hKn : K ∣ n) : n = K ∧ c = 1 ∧ hasCen = true := by
  have hmem := l05nLA_weylType_mem ht
  simp only [ggTWLPZArith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hall⟩ := h
  have hall' : ∀ i ∈ List.range 3, (ggTWLWeylTypes (N - 3 + i)).all (fun t =>
      t.1 % K != 0 || (t.1 == K && t.2 == 1 && hasCen)) = true :=
    List.all_eq_true.mp hall
  have hi : r - (N - 3) ∈ List.range 3 := by
    rw [List.mem_range]
    omega
  have hsum : N - 3 + (r - (N - 3)) = r := by omega
  have hinner := hall' (r - (N - 3)) hi
  rw [hsum] at hinner
  have hcond := (List.all_eq_true.mp hinner) (n, c) hmem
  have hmod : n % K = 0 := Nat.mod_eq_zero_of_dvd hKn
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
  rcases hcond with hne | ⟨⟨hnK, hc⟩, hcen⟩
  · exact absurd hmod hne
  · exact ⟨hnK, hc, hcen⟩

end CFSG.StandardType

end
