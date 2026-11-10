module

public import CFSG.LocalAnalysis.SectionRank.QTK.ExcRee
public import CFSG.Quasithin.Background.F6NQStructure

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.Quasithin.F6.F617Setting (exists_ne_one_commute exists_inv_mod_pCoreOf)

structure Setting {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  pPrimeCore_eq_bot : CFSG.pPrimeCore 3 D = ⊥
  pCore_eq_bot : Open.pCore 2 D = ⊥
  component : CFSG.IsComponent K
  normal : K.Normal
  le_left : twoResidual G₁ ≤ K
  not_le_right : ¬ twoResidual G₂ ≤ K
  card_left : Nat.card ↥(twoResidual G₁) = 3

namespace Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}


theorem normal_inf_centralizer (hS : Setting G₁ G₂ K) :
    (K ⊓ Subgroup.centralizer (K : Set D)).Normal := by
  have hKn := hS.normal
  refine ⟨fun z hz g => Subgroup.mem_inf.mpr ⟨hKn.conj_mem z hz.1 g, ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * k := by group

theorem not_le_inf_centralizer (hS : Setting G₁ G₂ K) :
    ¬ twoResidual G₁ ≤ K ⊓ Subgroup.centralizer (K : Set D) := by
  intro hle
  set Z := K ⊓ Subgroup.centralizer (K : Set D) with hZ
  have := hS.normal_inf_centralizer
  have hsup : Z ⊔ G₂ = ⊤ := sup_eq_top_of_twoResidual_le hS.triple hle
  have hZab : Group.IsSolvable ↥Z := Group.isSolvable_of_comm fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
  have : Group.IsSolvable ↥G₂ := isSolvable_vertex_right hS.triple
  have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp G₂.subtype) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hd : d ∈ Z ⊔ G₂ := hsup ▸ Subgroup.mem_top d
    rw [Subgroup.mem_sup_of_normal_left] at hd
    obtain ⟨z, hz, g, hg, rfl⟩ := hd
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := hS.normal_inf_centralizer.conj_mem z hz g⁻¹
    rw [inv_inv, mul_assoc] at h1
    exact h1
  have : Group.IsSolvable (D ⧸ Z) := Group.isSolvable_of_surjective hsurj
  have : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient Z
  have : Group.IsPerfect ↥K := hS.component.1.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hS.component.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance


theorem exists_generator (hS : Setting G₁ G₂ K) :
    ∃ x ∈ twoResidual G₁, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (K : Set D) ∧
      ∀ q ∈ pCoreOf 2 G₂, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  have h := hS.triple
  set L₁ := twoResidual G₁ with hL₁
  obtain ⟨x, hxL, hx1⟩ : ∃ x ∈ L₁, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have : L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    have h3 := hS.card_left
    rw [← hL₁, this, Subgroup.card_bot] at h3
    omega
  have hord : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hS.card_left ▸ Subgroup.orderOf_dvd_natCard L₁ hxL
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  refine ⟨x, hxL, hord, fun hxC => ?_, fun q hq => ?_⟩
  ·
    apply hS.not_le_inf_centralizer
    intro y hy
    refine ⟨hS.le_left hy, ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxC
    · exact Subgroup.inv_mem _ hxC
  · have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
    have hqN := le_normalizer_twoResidual G₁ (Subgroup.mem_inf.mp hqT).1
    have hmem := (Subgroup.mem_normalizer_iff.mp hqN x).mp hxL
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1


end Setting

end CFSG.Quasithin.RonanF617
