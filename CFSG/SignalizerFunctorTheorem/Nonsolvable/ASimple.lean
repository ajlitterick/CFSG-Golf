module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.Factors
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

@[expose] def IsASimple (A K : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (K : Set G) ∧ (∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) ∧
    ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → A ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = K

@[expose] def simpleComponents (K : Subgroup G) : Set (Subgroup G) :=
  {T | T ≤ K ∧ (T.subgroupOf K).Normal ∧ IsSimpleGroup T ∧ ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x}

variable [Finite G] {A K : Subgroup G}

omit [Finite G] in
private theorem simpleComponents_conj_mem {T : Subgroup G} (hT : T ∈ simpleComponents K) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) : k * t * k⁻¹ ∈ T :=
  (Subgroup.normal_subgroupOf_iff hT.1).mp hT.2.1 t k ht hk

omit [Finite G] in
private theorem simpleComponents_inf_eq_bot {T T' : Subgroup G} (hT : T ∈ simpleComponents K)
    (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') : T ⊓ T' = ⊥ := by
  have hTK := hT.1
  have hT'K := hT'.1
  have hTs : IsSimpleGroup T := hT.2.2.1
  have hT's : IsSimpleGroup T' := hT'.2.2.1
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hT.2.2.2
  have hD : ((T ⊓ T').subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro u v hu hv
    obtain ⟨huT, huT'⟩ := Subgroup.mem_inf.mp hu
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hv huT) (inv_mem hv),
      simpleComponents_conj_mem hT' huT' (hTK hv)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ T').subgroupOf T) with h | h
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : T) ∈ (T ⊓ T').subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    have hle : T ≤ T' := fun x hx => by
      have hmem : (⟨x, hx⟩ : T) ∈ (T ⊓ T').subgroupOf T := by rw [h]; trivial
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    have hN : (T.subgroupOf T').Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro u v hu hv
      exact simpleComponents_conj_mem hT hu (hT'K hv)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf T') with h' | h'
    · have hx₀1 : x₀ = 1 := by
        have hmem : (⟨x₀, hle hx₀⟩ : T') ∈ T.subgroupOf T' := hx₀
        rw [h', Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      exact hxy₀ (by rw [hx₀1, one_mul, mul_one])
    · refine hne (le_antisymm hle fun x hx => ?_)
      have hmem : (⟨x, hx⟩ : T') ∈ T.subgroupOf T' := by rw [h']; trivial
      exact hmem

omit [Finite G] in
private theorem simpleComponents_commute_elem {T T' : Subgroup G} (hT : T ∈ simpleComponents K)
    (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') {x y : G} (hx : x ∈ T) (hy : y ∈ T') :
    x * y = y * x := by
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ T' := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := simpleComponents_conj_mem hT (inv_mem hx) (hT'.1 hy)
      simpa [mul_assoc] using mul_mem hx this
    · exact mul_mem (simpleComponents_conj_mem hT' hy (hT.1 hx)) (inv_mem hy)
  rw [simpleComponents_inf_eq_bot hT hT' hne, Subgroup.mem_bot, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul] at hmem
  exact hmem

private theorem IsASimple.exists_factors (hK : IsASimple A K) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ (∀ i, S i ∈ simpleComponents K) ∧
      (∀ T ∈ simpleComponents K, ∃ i, T = S i) ∧
      (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) ∧
      (∀ i j, ∃ a ∈ A, S j = (S i).map (MulAut.conj a).toMonoidHom) ∧ (⨆ i, S i) = K := by
  obtain ⟨hA, hnc, hmin⟩ := hK
  obtain ⟨r, S, hr, hSK, hSn, hSs, hSnc, hSc, hSt, hSg⟩ := exists_aSimple_factors hA hnc hmin
  have hS : ∀ i, S i ∈ simpleComponents K := fun i => ⟨hSK i, hSn i, hSs i, hSnc i⟩
  refine ⟨r, S, hr, hS, fun T hT => ?_, hSc, hSt, hSg⟩
  by_contra hcon
  push Not at hcon
  have hKle : K ≤ Subgroup.centralizer (T : Set G) :=
    calc K = ⨆ i, S i := hSg.symm
      _ ≤ _ := iSup_le fun i y hy => by
        rw [Subgroup.mem_centralizer_iff]
        exact fun x hx => simpleComponents_commute_elem hT (hS i) (hcon i) hx hy
  have hTK : T ≤ K := hT.1
  obtain ⟨-, -, -, x, hx, y, hy, hxy⟩ := hT
  exact hxy (Subgroup.mem_centralizer_iff.mp (hKle (hTK hy)) x hx)

theorem IsASimple.simpleComponents_nonempty (hK : IsASimple A K) :
    (simpleComponents K).Nonempty := by
  obtain ⟨r, S, hr, hS, -⟩ := hK.exists_factors
  exact ⟨S ⟨0, hr⟩, hS _⟩

theorem IsASimple.components_commute (hK : IsASimple A K) {T T' : Subgroup G}
    (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) (hne : T ≠ T') :
    T ≤ Subgroup.centralizer (T' : Set G) ∧ T ⊓ T' = ⊥ := by
  obtain ⟨r, S, -, -, hSall, hSc, -⟩ := hK.exists_factors
  obtain ⟨i, rfl⟩ := hSall T hT
  obtain ⟨j, rfl⟩ := hSall T' hT'
  refine ⟨fun x hx => ?_, simpleComponents_inf_eq_bot hT hT' hne⟩
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => (hSc i j (fun h => hne (by rw [h])) x hx y hy).symm

theorem IsASimple.iSup_components (hK : IsASimple A K) :
    (⨆ T ∈ simpleComponents K, T) = K := by
  obtain ⟨r, S, -, hS, -, -, -, hSg⟩ := hK.exists_factors
  refine le_antisymm (iSup₂_le fun T hT => hT.1) ?_
  calc K = ⨆ i, S i := hSg.symm
    _ ≤ _ := iSup_le fun i => le_iSup₂_of_le (S i) (hS i) le_rfl

theorem IsASimple.components_transitive (hK : IsASimple A K) {T T' : Subgroup G}
    (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) :
    ∃ a ∈ A, T' = T.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨r, S, -, -, hSall, -, hSt, -⟩ := hK.exists_factors
  obtain ⟨i, rfl⟩ := hSall T hT
  obtain ⟨j, rfl⟩ := hSall T' hT'
  exact hSt i j

theorem IsASimple.normalizes_component_iff (hK : IsASimple A K) (hA : IsMulCommutative A)
    {T T' : Subgroup G} (hT : T ∈ simpleComponents K) (hT' : T' ∈ simpleComponents K) {a : G}
    (ha : a ∈ A) : T.map (MulAut.conj a).toMonoidHom = T ↔
      T'.map (MulAut.conj a).toMonoidHom = T' := by
  have key : ∀ {T T' : Subgroup G}, T ∈ simpleComponents K → T' ∈ simpleComponents K →
      T.map (MulAut.conj a).toMonoidHom = T → T'.map (MulAut.conj a).toMonoidHom = T' := by
    intro T T' hT hT' h
    obtain ⟨b, hb, rfl⟩ := hK.components_transitive hT hT'
    have hab : a * b = b * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
    have hcomp : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
      ext x
      change a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹
      calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
        _ = (b * a) * x * (b * a)⁻¹ := by rw [hab]
        _ = b * (a * x * a⁻¹) * b⁻¹ := by group
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h]
  exact ⟨key hT hT', key hT' hT⟩


end CFSG.SignalizerFunctorTheorem.Nonsolvable
