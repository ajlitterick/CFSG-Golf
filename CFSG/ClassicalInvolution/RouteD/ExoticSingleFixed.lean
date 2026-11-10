module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleConj
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSkew
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleOdd
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (La_range_eq_or_eq_swap)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {p f : ℕ} [Fact p.Prime]

theorem eq_swap_of_isFundTwin {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hodd : Odd (Nat.card K))
    (hsame : ∀ (R₀ R₁ : Subgroup (V ≃ₗ[K] V)) (i₀ i₁ : V ≃ₗ[K] V), IsFundamental Q R₀ i₀ →
      IsFundamental Q R₁ i₁ → Commutes R₀ R₁ → i₁ = i₀)
    (fr : OFrame Q) {L' : Subgroup (V ≃ₗ[K] V)} (hL' : L' ∈ fundSet Q)
    (htw : IsFundTwin (fundSet Q) fr.La.range L') : L' = fr.swap.La.range := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨j, G, rfl, hj⟩ := hL'
  have hj' : G.La (-1) = fr.La (-1) :=
    hj.symm.trans
      (hsame fr.La.range G.La.range _ _ (IsFundamental.of_frame fr) ⟨G, rfl, hj⟩ htw.2.1)
  rcases La_range_eq_or_eq_swap h2 hj' with h | h
  · exact absurd h.symm htw.1
  · exact h

theorem oddTwinFixed_spin (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible .POmegaOdd 3 p f)
    {X : Type} [Group X] (ψ : spinGroup (quadOdd 3 (GaloisField p f)) →* X)
    (hψker : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ x, σ (σ x) = x) (hσr : ∀ k, σ (ψ k) ∈ ψ.range)
    {R R' : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)))
    (htw : IsFundTwin (fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f))) R R')
    (hfixR : ∀ r ∈ R, σ (ψ r) = ψ r) : ∀ r ∈ R', σ (ψ r) = ψ r := by
  have hp2 : p ≠ 2 := hadm.2.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hn3 : 3 ≤ 3 := le_refl 3
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_card_galoisField hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hQuot := Gaps.centralQuot_odd (p := p) (f := f) hp2 hn3 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 :=
    Gaps.finrank_odd p f 3
  have hQ := nondegenerate_polarBilin_quadOdd 3 (GaloisField p f) h2
  obtain ⟨α, g, hαψ, hα⟩ :=
    ModelFacts.OrthAut.exists_isConj_lift_odd hp2 hn3 hf hK ψ hψker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p f))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hα2 : ∀ y, α (α y) = y := by
    have key := ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup (quadOdd 3 (GaloisField p f)) →* _).comp
        (α : spinGroup (quadOdd 3 (GaloisField p f)) →* _)) (MonoidHom.id _) (fun x => by
      apply hψker
      rw [MonoidHom.mem_ker]
      change ψ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαψ, hαψ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨i, fr, hRfr, -⟩ := hQuot.map_mem R hR
  have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
  rw [hRfr] at htwin
  have hsame : ∀ (R₀ R₁ : Subgroup (_ ≃ₗ[GaloisField p f] _)) (i₀ i₁ : _ ≃ₗ[GaloisField p f] _),
      IsFundamental (quadOdd 3 (GaloisField p f)) R₀ i₀ →
      IsFundamental (quadOdd 3 (GaloisField p f)) R₁ i₁ → Commutes R₀ R₁ → i₁ = i₀ :=
    fun R₀ R₁ i₀ i₁ h₀ h₁ hc =>
      commuting_same_involution hodd (by rw [hdim]; omega) h₀ h₁ hc
  have hR'fr : R'.map (spinAction (quadOdd 3 (GaloisField p f))) = fr.swap.La.range :=
    eq_swap_of_isFundTwin hodd hsame fr (hQuot.map_mem R' hR') htwin
  have hfix : ∀ r ∈ R, α r = r := fixes_of_perfect_of_central (hQuot.perf R hR).ge α
    fun r hr => hψker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ, hfixR r hr, inv_mul_cancel])
  have hfixR' := fixes_twin_of_isConj hQ (by rw [hdim]; omega) hα hα2
    (ker_spinAction_le_center _) fr (hQuot.perf R' hR').ge hRfr hR'fr hfix
    (fun g' hg hskew _ => no_skew_adjoint_odd h2 hQ (by rw [hdim]; decide) g' hg hskew)
  intro r' hr'
  rw [← hαψ, hfixR' r' hr']

theorem oddTwinFixed : OddTwinFixed p f := by
  intro n hn hq hadm X _ ψ hψker σ hσ2 hσr R hR R' hR' htw hfixR
  subst hn
  exact oddTwinFixed_spin hq hadm ψ hψker σ hσ2 hσr hR hR' htw hfixR

theorem rowSingleOddSmall : RowPiece p f ShapeSingleOddSmall :=
  rowSingleOddSmall_of_fixed oddTwinFixed

end CFSG.ClassicalInvolution.RouteD.Exotic
