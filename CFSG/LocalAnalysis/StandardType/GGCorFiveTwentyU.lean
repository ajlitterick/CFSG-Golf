module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp

public section

namespace CFSG.StandardType

open CFSG.Assembly UCoord

theorem UCoord.card_sumZero_le (m p : ℕ) [NeZero p] : Nat.card ↥(sumZero (m + 1) p) ≤ p ^ m := by
  let F : ↥(sumZero (m + 1) p) → (Fin m → Multiplicative (ZMod p)) :=
    fun f i => (f : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i)
  have hF : Function.Injective F := by
    intro f g hfg
    have hi : ∀ i : Fin m, crd f (Fin.castSucc i) = crd g (Fin.castSucc i) := fun i =>
      congrArg Multiplicative.toAdd (congrFun hfg i)
    refine ext_crd fun k => ?_
    induction k using Fin.lastCases with
    | last =>
      have hf := sum_crd f
      have hg := sum_crd g
      rw [Fin.sum_univ_castSucc] at hf hg
      simp only [hi] at hf
      exact add_left_cancel (hf.trans hg.symm)
    | cast i => exact hi i
  calc Nat.card ↥(sumZero (m + 1) p) ≤ Nat.card (Fin m → Multiplicative (ZMod p)) :=
        Nat.card_le_card_of_injective F hF
    _ = p ^ m := by
        rw [Nat.card_fun, Nat.card_fin]
        congr 1
        exact Nat.card_zmod p


theorem ggTorusAutCardSC_unitary_all
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusAutCardSC p
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) d.factorial := by
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj :
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
            MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  exact ggTorusAutCardSC_of_permEltSC hp hp2 (by omega) hZ hIp hcp hT

theorem ggTorusAutCardSC_unitary_twA_label
    {p r n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ r + 1) :
    LargeEvenLabelAll (⟨.twA, r, n⟩ : LargeEvenLabel) fun R _ I _ =>
      GGTorusAutCardSC p R I r (r + 1).factorial := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ, ?_⟩
  have hd : 3 ≤ r + 1 := by omega
  have hdq : (r + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hpd' : ¬ p ∣ r + 1 := hpd
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have h := ggTorusAutCardSC_unitary_all (K := K) (n := n) (d := r + 1) (p := p)
    hK hn hd hdq hp hp2 hpq hpd'
  simpa [show r + 1 - 1 = r by omega] using h

theorem ggTorusAutCardSC_unitary_four
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusAutCardSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) 3 24 := by
  have hdq : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  simpa only [show (4 - 1 : ℕ) = 3 by norm_num, show Nat.factorial 4 = 24 by norm_num] using
    ggTorusAutCardSC_unitary_all hK hn (by norm_num : 3 ≤ 4) hdq
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) h3 (by norm_num : ¬ 3 ∣ 4)

theorem ggPumpLineAutKnown_unitary_four_label
    {n : ℕ}
    (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twA, 3, n⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 3 24 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ
  obtain ⟨K, hKfield, hKfin, hK, hQ⟩ := hQ
  exact ⟨K, hKfield, hKfin, hK, hQ, ggTorusAutCardSC_unitary_four hK hn h3⟩

@[expose] def GGUnitaryCoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1) ∨
    (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1)


end CFSG.StandardType

end
