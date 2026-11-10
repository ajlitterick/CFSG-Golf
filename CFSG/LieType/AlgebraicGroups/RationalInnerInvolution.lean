module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
public import CFSG.LieType.Chevalley.RationalToralSignDiagram

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.ToralSign

section Signs

variable {τ : Tag} {k : Type} [Field k]

theorem eq_signCharTuple_of_sign (hk : ringChar k ≠ 2) {b : Fin τ.rank → kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) : b = signCharTuple (maskChar (signTupleBits b)) := by
  funext i
  have h := rootChar_eq_intUnitsMap hk hb (Pi.single i 1)
  rw [rootChar] at h
  rw [signCharTuple, ← h, Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem exists_conj_rootDiagUnit_signCharTuple_iff
    [IsAlgClosed k] (hk : ringChar k ≠ 2)
    (ψ ψ' : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (∃ g ∈ adjointGroup τ k, g * rootDiagUnit τ (signCharTuple (k := k) ψ) * g⁻¹ =
      rootDiagUnit τ (signCharTuple (k := k) ψ')) ↔ ψ' ∈ charOrbit ψ := by
  rw [(exceptional_root_diagonal_conjugacy_Weyl_transporter τ k _ _).1]
  simp only [rootChar_signCharTuple, (intUnitsMap_injective hk).eq_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v => ?_⟩
    have := hw (w⁻¹ • v)
    rwa [smul_inv_smul] at this
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v => ?_⟩
    have := hw (w • v)
    rwa [inv_smul_smul] at this

theorem signCharTuple_permChar (ρ : Equiv.Perm (Fin τ.rank))
    (ψ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (fun i => signCharTuple (k := k) ψ (ρ.symm i)) = signCharTuple (k := k) (permChar ρ ψ) := by
  funext i
  rw [signCharTuple, signCharTuple, permChar_apply, permLattice_single]

end Signs

section General

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem exists_conj_eq_rootDiagUnit_of_reps
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [CharP k p]
    (ρ : Equiv.Perm (Fin τ.rank)) (F : ModGL τ k →* ModGL τ k)
    (hFG : ∀ g ∈ adjointGroup τ k, F g ∈ adjointGroup τ k)
    (hFd : ∀ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
      F (rootDiagUnit τ b) = rootDiagUnit τ fun i => b (ρ.symm i))
    (reps : List (SignRep τ))
    (hfix : ∀ e ∈ reps, permChar ρ (signMaskChar τ e.mask) = signMaskChar τ e.mask)
    (hrep : ∀ χ, permChar ρ χ ∈ charOrbit χ →
      ∃ e ∈ reps, χ ∈ charOrbit (signMaskChar τ e.mask))
    {x : ModGL τ k} (hx : x ∈ adjointGroup τ k) (hFx : F x = x) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ k, ∃ e ∈ reps,
      g * x * g⁻¹ = rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) ∧
      F (rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask))) =
        rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨g₀, hg₀, b, hb, hgx⟩ := exceptional_Lang_inner_involution_torus_conjugacy τ hp k hx hx2
  obtain ⟨ψ, rfl⟩ : ∃ ψ, b = signCharTuple ψ := ⟨_, eq_signCharTuple_of_sign hk hb⟩
  have hFdb : F (rootDiagUnit τ (signCharTuple ψ)) =
      rootDiagUnit τ (signCharTuple (permChar ρ ψ)) := by
    rw [hFd _ hb, signCharTuple_permChar]
  have hc : (F g₀ * g₀⁻¹) * rootDiagUnit τ (signCharTuple ψ) * (F g₀ * g₀⁻¹)⁻¹ =
      rootDiagUnit τ (signCharTuple (permChar ρ ψ)) := by
    rw [← hFdb, ← hgx, map_mul, map_mul, map_inv, hFx]
    group
  have horb : permChar ρ ψ ∈ charOrbit ψ :=
    (exists_conj_rootDiagUnit_signCharTuple_iff hk ψ (permChar ρ ψ)).1
      ⟨_, mul_mem (hFG g₀ hg₀) (inv_mem hg₀), hc⟩
  obtain ⟨e, he, hψ⟩ := hrep ψ horb
  obtain ⟨n, hn, hnc⟩ :=
    (exists_conj_rootDiagUnit_signCharTuple_iff hk (signMaskChar τ e.mask) ψ).2 hψ
  refine ⟨n⁻¹ * g₀, mul_mem (inv_mem hn) hg₀, e, he, ?_, ?_⟩
  · calc n⁻¹ * g₀ * x * (n⁻¹ * g₀)⁻¹ = n⁻¹ * (g₀ * x * g₀⁻¹) * n := by group
      _ = n⁻¹ * (n * rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) * n⁻¹) * n := by
          rw [hgx, hnc]
      _ = _ := by group
  · rw [hFd _ (signCharTuple_sign _), signCharTuple_permChar, hfix e he]

end General

section Node

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def signMaskTuple (m : ℕ) : Fin τ.rank → kˣ :=
  fun j => (-1) ^ (m / 2 ^ (j : ℕ) % 2)

theorem signCharTuple_signMaskChar (m : ℕ) :
    signCharTuple (k := k) (signMaskChar τ m) = signMaskTuple τ k m := by
  funext j
  rw [signCharTuple, signMaskChar_single, map_zpow, zpow_natCast, signMaskTuple]
  congr 1
  exact Units.ext (by simp [intUnitsMap])

theorem entrywiseFrobGL_rootDiagUnit_of_sign (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ)
    {b : Fin τ.rank → kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) :
    entrywiseFrobGL τ k p e (rootDiagUnit τ b) = rootDiagUnit τ b := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_map]
  congr 1
  funext i
  rcases hb i with h | h <;> rw [h]
  · exact map_one _
  · exact Units.ext (by simp)


end Node

end CFSG.LieType.AlgebraicGroups
