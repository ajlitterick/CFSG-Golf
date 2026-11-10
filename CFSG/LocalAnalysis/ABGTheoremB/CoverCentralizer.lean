module

public import CFSG.LocalAnalysis.ABGTheoremB.CoverEmbedding
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.ABGTheoremB.Setting

open CFSG.ABGQGroups CFSG.QuasiDihedralFusion
open scoped commutatorElement

universe u

section SL2

variable {F : Type*} [Field F] [Finite F]

private theorem sl2_isPerfect (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩

omit [Finite F] in
private theorem sl2_nontrivial (hF : 4 ≤ Nat.card F) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
  have : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF).toNontrivial
  (QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).nontrivial


variable {A : Type*} [Group A]

private theorem commutator_eq_self_of_mulEquiv {X : Subgroup A}
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 4 ≤ Nat.card F) : ⁅X, X⁆ = X := by
  have := sl2_isPerfect hF
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.commutator_eq_self

omit [Finite F] in
private theorem ne_bot_of_mulEquiv {X : Subgroup A}
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 4 ≤ Nat.card F) : X ≠ ⊥ := by
  have := sl2_nontrivial hF
  intro h
  obtain ⟨y, y', hyy'⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2) F)
  have h1 : ∀ x : X, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (h ▸ x.2))
  exact hyy' (e.symm.injective ((h1 _).trans (h1 _).symm))

private theorem not_isPGroup_of_mulEquiv [Finite A] {X : Subgroup A}
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 4 ≤ Nat.card F) : ¬ IsPGroup 2 X := by
  intro h2
  have := sl2_isPerfect hF
  have := sl2_nontrivial hF
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Nontrivial X := e.toEquiv.nontrivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Group.IsPerfect.not_isNilpotent X h2.isNilpotent


end SL2

variable {G : Type u} [Group G] (σ : Setting G)

theorem isPGroup_centralizer_L₀Bar [Finite G] (hσ : σ.IsValid) (hN : σ.NStructure) :
    IsPGroup 2 (Subgroup.centralizer (σ.L₀Bar : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N))) := by
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := σ.exists_L₀Bar_mulEquiv hσ
  have hF : 4 ≤ Nat.card F := by
    rw [hq]
    have := hσ.five_lt_q
    omega
  have := σ.L₀Bar_normal hσ
  have hCn : (Subgroup.centralizer (σ.L₀Bar : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N))).Normal :=
    inferInstance
  set Cb := Subgroup.centralizer (σ.L₀Bar : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N)) with hCb
  set π := QuotientGroup.mk' (σ.ON.subgroupOf σ.N) with hπ
  set K : Subgroup G := (Cb.comap π).map σ.N.subtype with hK
  have hKN : K ≤ σ.N := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf σ.N = Cb.comap π :=
    Subgroup.comap_map_eq_self_of_injective σ.N.subtype_injective _
  have hNK : σ.N ≤ Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKN, hKsub]
    exact Subgroup.Normal.comap hCn π
  have hKmap : (K.subgroupOf σ.N).map π = Cb := by
    rw [hKsub, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hZS : centerOf (σ.S : Subgroup G) ≤ σ.N := inf_le_left.trans (σ.S_le_N hσ)
  set Zb := ((centerOf (σ.S : Subgroup G)).subgroupOf σ.N).map π with hZb
  have hON : (σ.ON.subgroupOf σ.N).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hR : ((solvRadIn σ.N).subgroupOf σ.N).map π = Zb := by
    rw [hN.N_solvRad, Subgroup.subgroupOf_sup σ.ON_le_N hZS, Subgroup.map_sup, hON, bot_sup_eq]
  by_cases hKR : K ≤ solvRadIn σ.N
  · have hle : Cb ≤ Zb := by
      rw [← hKmap, ← hR]
      exact Subgroup.map_mono (Subgroup.comap_mono hKR)
    have hS2 : IsPGroup 2 (centerOf (σ.S : Subgroup G)) := σ.S.isPGroup'.to_le inf_le_left
    exact (hS2.comap_subtype.map π).to_le hle
  · exfalso
    have hL := hN.N_minimalNormal K hKN hNK hKR
    have hLb : σ.L₀Bar ≤ Cb ⊔ Zb := by
      rw [← hKmap, ← hR, ← Subgroup.map_sup,
        ← Subgroup.subgroupOf_sup hKN (solvRadIn_le σ.N)]
      exact Subgroup.map_mono (Subgroup.comap_mono hL)
    have hZcomm : ∀ a ∈ Zb, ∀ b ∈ Zb, a * b = b * a := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h1 : (z : G) ∈ centerOf (σ.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hz
      have h2 : (z' : G) ∈ centerOf (σ.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hz'
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h2).2 z
        (Subgroup.mem_inf.mp h1).1
    have hcomm : ∀ a ∈ σ.L₀Bar, ∀ b ∈ σ.L₀Bar, ⁅a, b⁆ ∈ Cb := by
      intro a ha b hb
      have hρ : ∀ x ∈ Cb ⊔ Zb, QuotientGroup.mk' Cb x ∈ Zb.map (QuotientGroup.mk' Cb) := by
        intro x hx
        have := Subgroup.mem_map_of_mem (QuotientGroup.mk' Cb) hx
        rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),
          bot_sup_eq] at this
      obtain ⟨z₁, hz₁, h₁⟩ := hρ a (hLb ha)
      obtain ⟨z₂, hz₂, h₂⟩ := hρ b (hLb hb)
      rw [← QuotientGroup.ker_mk' Cb, MonoidHom.mem_ker, map_commutatorElement, ← h₁, ← h₂,
        ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.mpr (hZcomm z₁ hz₁ z₂ hz₂), map_one]
    have hle : ⁅σ.L₀Bar, σ.L₀Bar⁆ ≤ Cb := Subgroup.commutator_le.mpr hcomm
    rw [commutator_eq_self_of_mulEquiv e hF] at hle
    have hbot : ⁅σ.L₀Bar, σ.L₀Bar⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [commutator_eq_self_of_mulEquiv e hF] at hbot
    exact ne_bot_of_mulEquiv e hF hbot

theorem isPGroup_centralizer_L₀Bar_comap [Finite G] (hσ : σ.IsValid) (hN : σ.NStructure)
    {H : Subgroup G} {ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N)}
    (hι : Function.Injective ι) (hL : σ.L₀Bar ≤ ι.range) :
    IsPGroup 2 (Subgroup.centralizer
      ((σ.L₀Bar.comap ι : Subgroup (↥H ⧸ CFSG.oddCore ↥H)) : Set (↥H ⧸ CFSG.oddCore ↥H))) := by
  obtain ⟨-, -, hmap⟩ := σ.L₀Bar_comap_properties hσ hι hL
  have h2 := σ.isPGroup_centralizer_L₀Bar hσ hN
  intro g
  have hg : ι g ∈ Subgroup.centralizer (σ.L₀Bar : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N)) := by
    have hmem : ι g ∈ (Subgroup.centralizer
        ((σ.L₀Bar.comap ι : Subgroup (↥H ⧸ CFSG.oddCore ↥H)) :
          Set (↥H ⧸ CFSG.oddCore ↥H))).map ι := ⟨g, g.2, rfl⟩
    rw [hmap] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  obtain ⟨k, hk⟩ := h2 ⟨ι g, hg⟩
  have hk' : (ι g) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  refine ⟨k, Subtype.ext (hι ?_)⟩
  rw [Subgroup.coe_pow, map_pow, hk', Subgroup.coe_one, map_one]


theorem exists_normal_isPGroup_centralizer_of_mem_familyL [Finite G] (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    {H : Subgroup G} (hH : H ∈ σ.familyL r) :
    ∃ J : Subgroup (↥H ⧸ CFSG.oddCore ↥H), J.Normal ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
        Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      IsPGroup 2 (Subgroup.centralizer (J : Set (↥H ⧸ CFSG.oddCore ↥H))) := by
  obtain ⟨ι, hι, -, -, -, hLB⟩ := σ.exists_quotient_embedding_of_mem_familyL hσ hII hr hdiv hH
  have hL := σ.L₀Bar_le_LBar.trans hLB
  obtain ⟨hn, hF, -⟩ := σ.L₀Bar_comap_properties hσ hι hL
  exact ⟨σ.L₀Bar.comap ι, hn, hF, σ.isPGroup_centralizer_L₀Bar_comap hσ hII.toNStructure hι hL⟩

end CFSG.ABGTheoremB.Setting
