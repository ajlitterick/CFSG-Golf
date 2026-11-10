module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusCross
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodes
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

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

theorem leaf_commutes_beta {m : ℕ} (hm : 7 ≤ m) (c : TCtx p f .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z)
    (hF : OrthCross (Subgroup.center (modelUniv .POmegaMinus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D))
    {β : Subgroup G} {M : Subgroup G} (nd : DNodes p f (m - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {W₀ : Subgroup G} {x₀ : G} (hW₀ : W₀ ∈ Ω) (hx₀ : IsClassicalMember p f W₀ x₀)
    (hW0 : ∀ a (h : a < m - 1), a ≤ 3 → Commutes (nd.J ⟨a, h⟩) W₀)
    {D N : Subgroup G} (hDΩ : D ∈ Ω) (hNΩ : N ∈ Ω) (hDW : Commutes D W₀) (hNW : Commutes N W₀)
    (hDK : Commutes D K) (hD2 : Commutes D (nd.J ⟨2, by omega⟩)) (hNK : Commutes N K)
    (hN2 : Commutes N (nd.J ⟨2, by omega⟩))
    (hDN : ∃ W, LinearBlockStandardPair (GaloisField p f) W D N) :
    Commutes N β := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hW₀ hx₀
  obtain ⟨W, hW⟩ := hDN
  have hDne : D ≠ N := ne_of_linearBlockStandardPair hW
  have hDNn : ¬ Commutes D N := not_commutes_of_linearBlockStandardPair hW
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNΩ
  obtain ⟨wD, hwD⟩ := hΩ.classical D hDΩ
  have hmem : ∀ a (h : a < m - 1), a ≤ 3 → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {x₀} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) hx₀.mem (hW0 a h ha)
  have a01 : DNodes.Adj (⟨0, by omega⟩ : Fin (m - 1)) ⟨1, by omega⟩ := by fr_idx
  have a12 : DNodes.Adj (⟨1, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have a32 : DNodes.Adj (⟨3, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have hK : K ∈ centralizingMembers Ω {x₀} := h0 ▸ hmem 0 (by omega) (by omega)
  have hβ : β ∈ centralizingMembers Ω {x₀} := h1 ▸ hmem 1 (by omega) (by omega)
  have hJ : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 2 (by omega) (by omega)
  have hJ3 : nd.J ⟨3, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 3 (by omega) (by omega)
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
  refine cross_config cx hF (K := K) (β := β) (J := nd.J ⟨2, by omega⟩) (N := N) hK hβ hJ hNx
    hwK hwβ (nd.cl _) hwN ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ hKN hNK hJN hN2 ?_ ?_ ?_
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
  · rw [← h0]
    exact nd.ne_J hΩ (by simp)
  · rw [← h0]
    exact nd.commutes_of_not_adj (by simp) (by fr_idx)
  ·
    refine ⟨nd.J ⟨3, by omega⟩, nd.w ⟨3, by omega⟩, hJ3, nd.cl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h0]
      exact nd.ne_J hΩ (by simp)
    · exact nd.ne_J hΩ (by simp)
    · exact nd.commute_w h2 _ _
    · exact nd.commute_w h2 _ _
    · rw [← h0]
      exact nd.commutes_of_not_adj (by simp) (by fr_idx)
    · exact nd.not_commutes_of_adj a32
  ·
    refine ⟨D, wD, hDx, hwD, hKD.symm, hDne, ?_, ?_, hDK, hDNn⟩
    · exact hDK wD hwD.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
    · exact standardPair_involutions_commute h2 hW hwD.mem hwN.mem hwD.orderOf_eq_two
        hwN.orderOf_eq_two
  ·
    refine ⟨D, wD, hDx, hwD, hJD.symm, hDne, ?_, ?_, hD2, hDNn⟩
    · exact hD2 wD hwD.mem _ (nd.cl ⟨2, by omega⟩).mem
    · exact standardPair_involutions_commute h2 hW hwD.mem hwN.mem hwD.orderOf_eq_two
        hwN.orderOf_eq_two

end Leaf

section ShortConj

variable {G : Type} [Group G]

theorem map_conj_eq_of_commute (w : G) (R : Subgroup G) (h : ∀ r ∈ R, Commute w r) :
    R.map (MulAut.conj w).toMonoidHom = R := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have : (MulAut.conj w).toMonoidHom r = r := by
      show w * r * w⁻¹ = r
      rw [(h r hr).eq]
      group
    rw [this]
    exact hr
  · intro hy
    refine ⟨y, hy, ?_⟩
    show w * y * w⁻¹ = y
    rw [(h y hy).eq]
    group

theorem commutes_map_conj_of_commute (w : G) (A B : Subgroup G) (hB : ∀ b ∈ B, Commute w b)
    (hAB : Commutes A B) : Commutes (A.map (MulAut.conj w).toMonoidHom) B := by
  rintro _ ⟨a, ha, rfl⟩ b hb
  show w * a * w⁻¹ * b = b * (w * a * w⁻¹)
  have h1 : w⁻¹ * b = b * w⁻¹ := ((hB b hb).inv_left).eq
  calc w * a * w⁻¹ * b = w * a * (w⁻¹ * b) := by group
    _ = w * a * (b * w⁻¹) := by rw [h1]
    _ = w * (a * b) * w⁻¹ := by group
    _ = w * (b * a) * w⁻¹ := by rw [hAB a ha b hb]
    _ = (w * b) * a * w⁻¹ := by group
    _ = (b * w) * a * w⁻¹ := by rw [(hB b hb).eq]
    _ = b * (w * a * w⁻¹) := by group

private theorem map_conj_mul (x w : G) (A : Subgroup G) :
    A.map (MulAut.conj (x * w)).toMonoidHom =
      (A.map (MulAut.conj w).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  show x * w * y * (x * w)⁻¹ = x * (w * y * w⁻¹) * x⁻¹
  group

end ShortConj

section Short

variable {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem commute_twShortRoot_rootSL2 {a b' : ℕ} (ha : a < n - 1) (hb : b' < n - 1)
    (hab : a ≠ b') (k : Fin (n - 1)) (hka : k.val ≠ a) (hkb : k.val ≠ b') (s t u : Bool)
    (p : Fin 2 → K) :
    ∀ y ∈ rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab s t,
      Commute (twShortRoot n hirr k u (.ofAdd p)) y := by
  have hij : (⟨a, ha⟩ : Fin (n - 1)) ≠ ⟨b', hb⟩ := fun h => hab (congrArg Fin.val h)
  have hka' : k ≠ ⟨a, ha⟩ := fun h => hka (congrArg Fin.val h)
  have hkb' : k ≠ ⟨b', hb⟩ := fun h => hkb (congrArg Fin.val h)
  have hle : rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab s t ≤
      Subgroup.centralizer ({twShortRoot n hirr k u (.ofAdd p)} : Set _) := by
    unfold rootSL2
    rw [longSL2_range_eq_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective x
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_longRoot_twShortRoot_of_ne n hirr hij hka' hkb' s t u a' p).eq
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective x
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_longRoot_twShortRoot_of_ne n hirr hij.symm hkb' hka' (!t) (!s) u a' p).eq
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end Short

section LeafN


end LeafN

section LeafW


end LeafW

end CFSG.ClassicalInvolution.RouteD.Gaps
