module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusLeaf

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Leaf

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leaf_commutes_beta_gen {m : ℕ} (hm : 7 ≤ m) (c : TCtx p f .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z)
    (hF : OrthCross (Subgroup.center (modelUniv .POmegaMinus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D))
    {β M : Subgroup G} (nd : DNodes p f (m - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {W₀ : Subgroup G} {x₀ : G} (hW₀ : W₀ ∈ Ω) (hx₀ : IsClassicalMember p f W₀ x₀)
    (hW0 : ∀ a (h : a < m - 1), a ≤ 2 → Commutes (nd.J ⟨a, h⟩) W₀)
    {E : Subgroup G} {wE : G} (hEΩ : E ∈ Ω) (hwE : IsClassicalMember p f E wE)
    (hEW : Commutes E W₀) (hEK : Commutes E K) (hEJ : ¬ Commutes E (nd.J ⟨2, by omega⟩))
    (hEne : E ≠ nd.J ⟨2, by omega⟩) (hEw : Commute wE (nd.w ⟨2, by omega⟩))
    {D N : Subgroup G} {wD wN : G} (hDΩ : D ∈ Ω) (hNΩ : N ∈ Ω)
    (hwD : IsClassicalMember p f D wD) (hwN : IsClassicalMember p f N wN)
    (hDW : Commutes D W₀) (hNW : Commutes N W₀) (hDK : Commutes D K)
    (hD2 : Commutes D (nd.J ⟨2, by omega⟩)) (hNK : Commutes N K)
    (hN2 : Commutes N (nd.J ⟨2, by omega⟩)) (hDne : D ≠ N) (hDNn : ¬ Commutes D N)
    (hDNw : Commute wD wN) : Commutes N β := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hW₀ hx₀
  have hmem : ∀ a (h : a < m - 1), a ≤ 2 → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {x₀} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) hx₀.mem (hW0 a h ha)
  have a01 : DNodes.Adj (⟨0, by omega⟩ : Fin (m - 1)) ⟨1, by omega⟩ := by fr_idx
  have a12 : DNodes.Adj (⟨1, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have hK : K ∈ centralizingMembers Ω {x₀} := h0 ▸ hmem 0 (by omega) (by omega)
  have hβ : β ∈ centralizingMembers Ω {x₀} := h1 ▸ hmem 1 (by omega) (by omega)
  have hJ : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 2 (by omega) (by omega)
  have hEx : E ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hEΩ hx₀.mem hEW
  have hDx : D ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hDΩ hx₀.mem hDW
  have hNx : N ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hNΩ hx₀.mem hNW
  have hwK : IsClassicalMember p f K (nd.w ⟨0, by omega⟩) := h0 ▸ nd.cl _
  have hwβ : IsClassicalMember p f β (nd.w ⟨1, by omega⟩) := h1 ▸ nd.cl _
  have hKN : K ≠ N := fun e => by
    rw [← e] at hNK
    exact not_commutes_self_of_mem hΩ c.hK hNK
  have hJN : nd.J ⟨2, by omega⟩ ≠ N := fun e => by
    rw [← e] at hN2
    exact not_commutes_self_of_mem hΩ (nd.mem _) hN2
  have hKD : K ≠ D := fun e => by
    rw [← e] at hDK
    exact not_commutes_self_of_mem hΩ c.hK hDK
  have hJD : nd.J ⟨2, by omega⟩ ≠ D := fun e => by
    rw [← e] at hD2
    exact not_commutes_self_of_mem hΩ (nd.mem _) hD2
  have hKE : K ≠ E := fun e => by
    rw [← e] at hEK
    exact not_commutes_self_of_mem hΩ c.hK hEK
  have hKJ : Commutes K (nd.J ⟨2, by omega⟩) := by
    rw [← h0]
    exact nd.commutes_of_not_adj (by simp) (by fr_idx)
  refine cross_config cx hF (K := K) (β := β) (J := nd.J ⟨2, by omega⟩) (N := N) hK hβ hJ hNx
    hwK hwβ (nd.cl _) hwN ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
    (by rw [← h0]; exact nd.ne_J hΩ (by simp)) hKJ hKN hNK hJN hN2 ?_ ?_ ?_
  · rw [← h0, ← h1]
    exact nd.ne_J hΩ (by simp)
  · rw [← h0, ← h1]
    exact nd.not_commutes_of_adj a01
  · exact nd.commute_w h2 _ _
  · rw [← h0]
    exact nd.conjSub_w h2 a01
  · rw [← h1]
    exact nd.ne_J hΩ (by simp)
  · rw [← h1]
    exact nd.not_commutes_of_adj a12
  · exact nd.commute_w h2 _ _
  · rw [← h1]
    exact nd.conjSub_w h2 a12
  ·
    refine ⟨E, wE, hEx, hwE, hKE.symm, hEne, ?_, hEw, hEK, hEJ⟩
    exact hEK _ hwE.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
  ·
    refine ⟨D, wD, hDx, hwD, hKD.symm, hDne, ?_, hDNw, hDK, hDNn⟩
    exact hDK wD hwD.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
  ·
    refine ⟨D, wD, hDx, hwD, hJD.symm, hDne, ?_, hDNw, hD2, hDNn⟩
    exact hD2 wD hwD.mem _ (nd.cl ⟨2, by omega⟩).mem

end Leaf

end CFSG.ClassicalInvolution.RouteD.TwinSmall
