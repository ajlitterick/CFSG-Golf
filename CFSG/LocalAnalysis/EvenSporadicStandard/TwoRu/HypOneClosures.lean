module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

variable {n : ℕ}


@[expose] def letterG (gg : ℕ → Equiv.Perm (Fin n)) (z : ℤ) : Equiv.Perm (Fin n) :=
  if 0 < z then gg (z.toNat - 1) else (gg ((-z).toNat - 1))⁻¹

theorem wordG_mem {K : Subgroup (Equiv.Perm (Fin n))} (gg : ℤ → Equiv.Perm (Fin n))
    {w : List ℤ} (h : ∀ z ∈ w, gg z ∈ K) : wordG gg w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons z w ih =>
    rw [wordG, List.map_cons, List.prod_cons]
    exact K.mul_mem (h z List.mem_cons_self) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem rep_wordTables (hn : n < 2 ^ 32) (K : Subgroup (Equiv.Perm (Fin n)))
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ K)
    {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ gens.size) :
    ∃ g ∈ K, Rep n (wordT n (letterTab gens gensInv) w) g := by
  have hl : ∀ z ∈ w, Rep n (letterTab gens gensInv z) (letterG gg z) ∧ letterG gg z ∈ K := by
    intro z hz
    obtain ⟨hz0, hzs⟩ := hw z hz
    by_cases hpos : 0 < z
    · obtain ⟨h1, -, h3⟩ := hg (z.toNat - 1) (by omega)
      simp only [letterTab, letterG, hpos, ite_true]
      exact ⟨h1, h3⟩
    · obtain ⟨-, h2, h3⟩ := hg ((-z).toNat - 1) (by omega)
      simp only [letterTab, letterG, hpos, ite_false]
      exact ⟨h2, K.inv_mem h3⟩
  exact ⟨wordG (letterG gg) w, wordG_mem _ fun z hz => (hl z hz).2,
    Rep.wordT hn w fun z hz => (hl z hz).1⟩

end CFSG.EvenSporadicStandard.TwoRu.HypOne
