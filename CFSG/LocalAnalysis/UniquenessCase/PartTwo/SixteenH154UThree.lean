module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem s16h_not_dvd_two_pow_three (n : ℕ) : ¬ 3 ∣ 2 ^ n := fun hdvd =>
  absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hdvd)) (by norm_num)


private theorem s16h_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1


theorem s16h_uniqueMax_of_noncyclic_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hk : IsStronglyPEmbedded 3 D.M) {P X : Subgroup G} (hP : IsPGroup 3 P)
    (hPc : ¬ IsCyclic ↥P) (hPX : P ≤ X) (hXM : X ≤ D.M) : UniqueMax D.M X :=
  uc22p22u_uniqueMax_mono D hPX hXM
    (uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_three (by norm_num) (hPX.trans hXM) hP
      hPc (Or.inl (ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hk
        (hPX.trans hXM) hP)))

theorem s16h_uniqueMax_cent_of_cElt_three (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (hk : IsStronglyPEmbedded 3 D.M) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V)
    {P : Subgroup G} (hPp : IsPGroup 3 P) (hPc : ¬ IsCyclic ↥P) {w : G} (hwV : w ∈ V)
    (hwV₀ : w ∉ V₀) (hP : P ≤ F11.CElt D.M V₀ w) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V (Hyp125.hyp11 h127 h.hyp125)
    (s16c34_card_v0_le_four D h) w hwV hwV₀
  have hindex : ¬ 3 ∣ (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) := by
    rw [hn]
    exact s16h_not_dvd_two_pow_three n
  obtain ⟨B, hB, hBp, hBc⟩ :=
    c23_exists_noncyclic_le_of_not_dvd_relIndex Nat.prime_three hP hindex hPp hPc
  exact s16h_uniqueMax_of_noncyclic_three D h61 h63 hk hBp hBc hB inf_le_left


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
