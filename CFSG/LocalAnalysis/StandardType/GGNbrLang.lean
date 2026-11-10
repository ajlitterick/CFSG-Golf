module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Nbr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


@[expose] def GGNbrInnerWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I _ θ =>
          ggLAut K θ ⟨x, hxK⟩ ∈ I →
            ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
              w * x * w⁻¹ ∉ Subgroup.zpowers x

section Proofs

variable {G : Type} [Group G]

theorem mem_of_lang_torus [Finite G] {p : ℕ} (hp : p.Prime) {Bs B₀ : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs) {b₀ e : G} (hb₀ : b₀ ∈ Bs) (hb₀' : b₀ ∉ B₀)
    (he : e ∈ Subgroup.centralizer (B₀ : Set G)) (heb : b₀ * e = e * b₀) (hep : e ^ p = 1) :
    e ∈ Bs := by
  refine hSC e (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) hep
  obtain ⟨b₁, hb₁, j, rfl⟩ := NbrFieldLang.exists_mul_pow_of_card hp hBs hB₀ hcard hb₀ hb₀' hb
  have h1 : b₁ * e = e * b₁ := Subgroup.mem_centralizer_iff.mp he b₁ hb₁
  have h2 : b₀ ^ j * e = e * b₀ ^ j := ((Commute.pow_left heb j) : _)
  calc b₁ * b₀ ^ j * e = b₁ * (b₀ ^ j * e) := by rw [mul_assoc]
    _ = b₁ * (e * b₀ ^ j) := by rw [h2]
    _ = (b₁ * e) * b₀ ^ j := by rw [mul_assoc]
    _ = (e * b₁) * b₀ ^ j := by rw [h1]
    _ = e * (b₁ * b₀ ^ j) := by rw [mul_assoc]

theorem exists_index_prime_of_hom_cyclic [Finite G] {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {C : Type*} [Group C] [IsCyclic C] (χ : ↥Bs →* C) {b₀ : G}
    (hb₀ : b₀ ∈ Bs) (hχ : χ ⟨b₀, hb₀⟩ ≠ 1) :
    ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
      ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ χ ⟨b, hb⟩ = 1 := by
  refine ⟨χ.ker.map Bs.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, -, rfl⟩
    exact b.2
  · have h1 := Subgroup.card_ker_mul_card_range χ
    have h2 : Nat.card (χ.ker.map Bs.subtype) = Nat.card χ.ker :=
      Subgroup.card_map_of_injective Bs.subtype_injective
    have h3 : Nat.card χ.range = p := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := χ.range)
      have hord : orderOf g = Nat.card χ.range := orderOf_eq_card_of_forall_mem_zpowers hg
      have hgp : g ^ p = 1 := by
        obtain ⟨b, hb⟩ := g.2
        apply Subtype.ext
        have hbp : b ^ p = 1 := Subtype.ext (hBs.2 b b.2)
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hb, ← map_pow, hbp, map_one]
      have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exfalso
        have hg1 : g = 1 := orderOf_eq_one_iff.mp h
        have hmem : (⟨χ ⟨b₀, hb₀⟩, ⟨_, rfl⟩⟩ : χ.range) ∈ Subgroup.zpowers g := hg _
        rw [hg1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
        exact hχ (congrArg Subtype.val hmem)
      · rw [← hord, h]
    rw [h2, ← h3, h1]
  · rintro ⟨b, hb, hbb⟩
    apply hχ
    have hb' : b = ⟨b₀, hb₀⟩ := Subtype.ext hbb
    rw [← hb']
    exact hb
  · intro b hb
    constructor
    · rintro ⟨c, hc, hcb⟩
      have hc' : c = ⟨b, hb⟩ := Subtype.ext hcb
      rw [← hc']
      exact hc
    · intro h
      exact ⟨⟨b, hb⟩, h, rfl⟩

end Proofs


theorem ggNbrInnerXNotNormalInput_of_weyl (h : GGNbrInnerWeylInput) :
    GGNbrInnerXNotNormalInput := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN hxK P hP
  refine largeEvenMarking_mono ?_ (h G p B Bs x L D J hcfg y K hK hN hxK P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hxI => ?_⟩
  obtain ⟨w, hwK, hwC, hwx⟩ := hQ hxI
  have hBs := hcfg.2.1
  refine ⟨w, hwK, NbrLang.mem_normalizer_of_conj_mem_centralizer hBs.2.1.2 hBs.2.2.2 hwC,
    fun hwN => hwx ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp hwN x).mp (Subgroup.mem_zpowers x)


end CFSG.StandardType

end
