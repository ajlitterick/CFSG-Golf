module

public import CFSG.ClassicalInvolution.Asc77.AscT8Zd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8

section Fuse

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem sylow_le_H274_of_mem {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S₂ : Sylow 2 G}
    {X M : Subgroup G} (hX : X ∈ RSet Ω) (hXS : X ≤ (S₂ : Subgroup G)) (hM : M ∈ Ω)
    (hXM : X ≤ M) {zM : G} (hzM : IsUniqueInvolution M zM) (hzH : zM ∈ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨g, hg⟩ := hs.stand.trans M hM
  have hzM' : zM = g * z * g⁻¹ := by
    have := hs.hz.conj g
    rw [hg] at this
    exact hzM.eq this
  have hgH : g⁻¹ ∈ H274 Ω K z := by
    refine mem_H274_of_conj_mem_H274 hs hcomp ?_
    rw [inv_inv, ← hzM']
    exact hzH
  have hgH' : g ∈ H274 Ω K z := by simpa using (H274 Ω K z).inv_mem hgH
  have hS₂ : (S₂ : Subgroup G) ≤ sigmaNorm Ω M :=
    sylow_le_sigmaNorm hp hq hΩ hM hX hXM hXS hzM
  intro s hsS
  have hsM : s ∈ sigmaNorm Ω M := hS₂ hsS
  have hsM' : conjSub s M ∈ dComp Ω M := (mem_sigmaNorm_iff hΩ.conjInvariant hM).1 hsM
  have h1 : g⁻¹ * s * g ∈ sigmaNorm Ω K := by
    rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
    have h2 := mem_dComp_conjSub hΩ.conjInvariant hsM' g⁻¹
    have e1 : conjSub g⁻¹ M = K := by rw [← hg, conjSub_inv_conjSub]
    have e2 : conjSub (g⁻¹ * s * g) K = conjSub g⁻¹ (conjSub s M) := by
      rw [conjSub_mul, conjSub_mul, hg]
    rw [e2]
    rwa [e1] at h2
  have h3 := (H274 Ω K z).mul_mem ((H274 Ω K z).mul_mem hgH' (sigmaNorm_le_H274 K z h1)) hgH
  simpa [mul_assoc] using h3

omit [Finite G] in
theorem centralizer_le_of_conj {H : Subgroup G} {u v : G} (hv : v ∈ H)
    (h : Subgroup.centralizer ({v⁻¹ * u * v} : Set G) ≤ H) :
    Subgroup.centralizer ({u} : Set G) ≤ H := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : v⁻¹ * c * v ∈ Subgroup.centralizer ({v⁻¹ * u * v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v⁻¹ * c * v * (v⁻¹ * u * v) = v⁻¹ * (c * u) * v := by group
      _ = v⁻¹ * (u * c) * v := by rw [hc]
      _ = v⁻¹ * u * v * (v⁻¹ * c * v) := by group
  have := H.mul_mem (H.mul_mem hv (h hc')) (H.inv_mem hv)
  simpa [mul_assoc] using this


omit [Finite G] in
theorem isPGroup_closure_pair {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  intro g
  refine ⟨1, ?_⟩
  have hg : (g : G) * g = 1 := by
    rcases mem_closure_pair_involutions hx hy hxy g.2 with h | h | h | h
    · rw [h]; group
    · rw [h]; exact hx
    · rw [h]; exact hy
    · rw [h]
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx, hy]; group
  apply Subtype.ext
  simpa [pow_two] using hg


theorem exists_mul_self_ne_one_of_mem_RSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {X : Subgroup G} (hX : X ∈ RSet Ω) : ∃ x ∈ X, x * x ≠ 1 := by
  classical
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hp hq hM
  have h8 := hΩ.eight_le_of_mem_RSet hp hX
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : ↥X => decide ((x : G) = 1)) := by
    intro a b hab
    simp only [decide_eq_decide] at hab
    by_cases ha : (a : G) = 1
    · exact Subtype.ext (ha.trans (hab.1 ha).symm)
    · have hb : (b : G) ≠ 1 := fun h => ha (hab.2 h)
      have ha' := hzM.unique a (hXM.1 a.2) (hcon a a.2)
      have hb' := hzM.unique b (hXM.1 b.2) (hcon b b.2)
      exact Subtype.ext ((ha'.resolve_left ha).trans (hb'.resolve_left hb).symm)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem sylow_le_H274_of_good_four {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S₂ : Sylow 2 G} {u v : G} (hu : u ∈ (S₂ : Subgroup G)) (hv : v ∈ (S₂ : Subgroup G))
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) (hgu : Subgroup.centralizer ({u} : Set G) ≤ H274 Ω K z)
    (hgv : Subgroup.centralizer ({v} : Set G) ≤ H274 Ω K z)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S₂
  have hXR : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ g
  have hXS : conjSub g R ≤ (S₂ : Subgroup G) := by
    have := conjSub_mono (n := g) hRS
    rwa [hg] at this
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_mul_self_ne_one_of_mem_RSet hp hq hΩ hXR
  have h310 := lemma_3_10 (S := (S₂ : Subgroup G)) S₂.isPGroup'
    (Δ := {Y | Y ∈ RSet Ω ∧ Y ≤ (S₂ : Subgroup G)}) (fun Y hY => hY.2)
    (fun Y hY s hs' => ⟨RSet.conj hΩ.conjInvariant hY.1 s, by
      have := conjSub_mono (n := s) hY.2
      rwa [conjSub_eq_self_of_mem hs'] at this⟩)
    (fun Y hY Y' hY' hne => l6_7_proved p f hp hq G Ω hΩ S₂ Y hY.1 Y' hY'.1 hY.2 hY'.2 hne)
    hu hv hu1 hv1 huv hu2 hv2 hc ⟨hXR, hXS⟩ ⟨x₀, hx₀, Or.inl hx₀1⟩
  have hγ : gamma1 (Subgroup.closure ({u, v} : Set G)) (S₂ : Subgroup G) ≤ H274 Ω K z := by
    refine iSup₂_le fun w hw => iSup_le fun hw1 => inf_le_right.trans ?_
    rcases mem_closure_pair_involutions hu2 hv2 hc hw with h | h | h | h
    · exact absurd h hw1
    · rw [h]; exact hgu
    · rw [h]; exact hgv
    · rw [h]; exact hguv
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h310
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyH : y ∈ H274 Ω K z := hγ hy.1
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hXR
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hp hq hM
  have hyX : y ∈ conjSub g R := hy.2
  have hzMy : zM ∈ Subgroup.zpowers y := by
    refine mem_of_isPGroup_of_unique_involution_subgroup (J := M) (fun t' ht' hord => ?_)
      (Subgroup.zpowers_le.mpr (hXM.1 hyX)) (hXM.2.1.to_le (Subgroup.zpowers_le.mpr hyX)) ?_
    · have h2 : t' * t' = 1 := by
        have := pow_orderOf_eq_one t'
        rwa [hord, pow_two] at this
      rcases hzM.unique t' ht' h2 with h | h
      · rw [h, orderOf_one] at hord
        omega
      · exact h
    · intro h
      exact hy1' (by simpa using h)
  have hzMH : zM ∈ H274 Ω K z := (Subgroup.zpowers_le.mpr hyH) hzMy
  exact sylow_le_H274_of_mem hs hcomp hXR hXS hM hXM.1 hzM hzMH

end Fuse

end T8

end CFSG.ClassicalInvolution.Asc77
