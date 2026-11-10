module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

abbrev conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

omit [Finite G] in
theorem conjHom_injective (g : G) : Function.Injective (conjHom g) := (MulAut.conj g).injective

omit [Finite G] in
theorem map_conj_mem_components (K : Subgroup G) (x g : G) {N : Subgroup G}
    (hN : N ≤ centralizer ({x} : Set G) ∧
      (N.subgroupOf (centralizer ({x} : Set G))).Normal ∧ Nonempty (N ≃* K)) :
    N.map (conjHom g) ≤ centralizer ({g * x * g⁻¹} : Set G) ∧
      ((N.map (conjHom g)).subgroupOf (centralizer ({g * x * g⁻¹} : Set G))).Normal ∧
        Nonempty (N.map (conjHom g) ≃* K) := by
  obtain ⟨hle, hnorm, ⟨e⟩⟩ := hN
  refine ⟨?_, ?_, ⟨(N.equivMapOfInjective (conjHom g) (conjHom_injective g)).symm.trans e⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.1 (hle hy)
    show g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy']
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · refine ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨n₀, hn₀, hn₀e⟩ := hn
    have hcx : g⁻¹ * (c : G) * g ∈ centralizer ({x} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      have hc : (c : G) * (g * x * g⁻¹) = g * x * g⁻¹ * (c : G) :=
        mem_centralizer_singleton_iff.1 c.2
      calc g⁻¹ * (c : G) * g * x = g⁻¹ * ((c : G) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (c : G)) * g := by rw [hc]
        _ = x * (g⁻¹ * (c : G) * g) := by group
    have h1 := hnorm.conj_mem ⟨n₀, hle hn₀⟩ (mem_subgroupOf.2 hn₀) ⟨g⁻¹ * (c : G) * g, hcx⟩
    rw [mem_subgroupOf] at h1
    refine ⟨(g⁻¹ * (c : G) * g) * n₀ * (g⁻¹ * (c : G) * g)⁻¹, h1, ?_⟩
    show g * ((g⁻¹ * (c : G) * g) * n₀ * (g⁻¹ * (c : G) * g)⁻¹) * g⁻¹ =
      (c : G) * (n : G) * (c : G)⁻¹
    rw [← hn₀e]
    show _ = (c : G) * (g * n₀ * g⁻¹) * (c : G)⁻¹
    group

omit [Finite G] in
theorem componentProduct_conj (K : Subgroup G) (x g : G) :
    componentProduct K (g * x * g⁻¹) = (componentProduct K x).map (conjHom g) := by
  apply le_antisymm
  · refine sSup_le fun N' hN' => ?_
    have hmem := map_conj_mem_components K (g * x * g⁻¹) g⁻¹ hN'
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at hmem
    have h1 : N'.map (conjHom g⁻¹) ≤ componentProduct K x := le_sSup hmem
    have h2 : N' ≤ (N'.map (conjHom g⁻¹)).map (conjHom g) := by
      intro y hy
      refine ⟨g⁻¹ * y * g, ⟨y, hy, by rw [conjHom_apply, inv_inv]⟩, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
    exact h2.trans (Subgroup.map_mono h1)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_conj_mem_components K x g hN)

omit [Finite G] in
theorem mem_center_map_iff {K : Subgroup G} {x : G} :
    x ∈ (center K).map K.subtype ↔ x ∈ K ∧ ∀ k ∈ K, x * k = k * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun k hk => congrArg Subtype.val (mem_center_iff.1 hz ⟨k, hk⟩).symm⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun k => Subtype.ext (hc k k.2).symm, rfl⟩

omit [Finite G] in
theorem conj_inv_mem_of_map_eq {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K) {k : G}
    (hk : k ∈ K) : g⁻¹ * k * g ∈ K := by
  have : k ∈ K.map (conjHom g) := by rw [hK]; exact hk
  obtain ⟨k₀, hk₀, rfl⟩ := this
  have e : g⁻¹ * (g * k₀ * g⁻¹) * g = k₀ := by group
  rw [conjHom_apply, e]
  exact hk₀

omit [Finite G] in
theorem conj_mem_of_map_eq {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K) {k : G}
    (hk : k ∈ K) : g * k * g⁻¹ ∈ K := by
  have : g * k * g⁻¹ ∈ K.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) hk
  rwa [hK] at this

omit [Finite G] in
theorem vCandidates_conj {K : Subgroup G} {u g : G} (hK : K.map (conjHom g) = K)
    (hu : g * u * g⁻¹ = u) {v : G} (hv : v ∈ vCandidates K u) : g * v * g⁻¹ ∈ vCandidates K u := by
  obtain ⟨hvK, hvZ, hv2⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · have : (K ⊔ zpowers u).map (conjHom g) = K ⊔ zpowers u := by
      rw [Subgroup.map_sup, hK, MonoidHom.map_zpowers, conjHom_apply, hu]
    exact this ▸ Subgroup.mem_map_of_mem (conjHom g) hvK
  · intro hz
    rw [mem_center_map_iff] at hz hvZ
    refine hvZ ⟨?_, fun k hk => ?_⟩
    · have := conj_inv_mem_of_map_eq hK hz.1
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rwa [e] at this
    · have h1 := hz.2 (g * k * g⁻¹) (conj_mem_of_map_eq hK hk)
      have : g * (v * k) * g⁻¹ = g * (k * v) * g⁻¹ := by
        calc g * (v * k) * g⁻¹ = g * v * g⁻¹ * (g * k * g⁻¹) := by group
          _ = g * k * g⁻¹ * (g * v * g⁻¹) := h1
          _ = g * (k * v) * g⁻¹ := by group
      have := mul_left_cancel (mul_right_cancel this)
      exact this
  · have := orderOf_injective (conjHom g) (conjHom_injective g) v
    rw [conjHom_apply] at this
    rw [this, hv2]

omit [Finite G] in
theorem twoAdic_inf_centralizer_conj {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K)
    (v : G) :
    twoAdic (K ⊓ centralizer ({g * v * g⁻¹} : Set G)) =
      twoAdic (K ⊓ centralizer ({v} : Set G)) := by
  have hc : (centralizer ({v} : Set G)).map (conjHom g) = centralizer ({g * v * g⁻¹} : Set G) := by
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have h1 : y₀ * v = v * y₀ := mem_centralizer_singleton_iff.1 hy₀
      show g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * y₀ * g⁻¹)
      calc g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * (y₀ * v) * g⁻¹ := by group
        _ = g * (v * y₀) * g⁻¹ := by rw [h1]
        _ = g * v * g⁻¹ * (g * y₀ * g⁻¹) := by group
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · refine mem_centralizer_singleton_iff.2 ?_
        have h1 : y * (g * v * g⁻¹) = g * v * g⁻¹ * y := mem_centralizer_singleton_iff.1 hy
        calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * v * g⁻¹ * y) * g := by rw [h1]
          _ = v * (g⁻¹ * y * g) := by group
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hmap : (K ⊓ centralizer ({v} : Set G)).map (conjHom g) =
      K ⊓ centralizer ({g * v * g⁻¹} : Set G) := by
    rw [Subgroup.map_inf _ _ (conjHom g) (conjHom_injective g), hK, hc]
  have hcard : Nat.card ((K ⊓ centralizer ({v} : Set G)).map (conjHom g)) =
      Nat.card (K ⊓ centralizer ({v} : Set G) : Subgroup G) :=
    Subgroup.card_map_of_injective (conjHom_injective g)
  unfold twoAdic
  rw [← hmap, hcard]

omit [Finite G] in
theorem vMaximal_conj {K : Subgroup G} {u g : G} (hK : K.map (conjHom g) = K)
    (hu : g * u * g⁻¹ = u) {v : G} (hv : v ∈ vMaximal K u) : g * v * g⁻¹ ∈ vMaximal K u := by
  refine ⟨vCandidates_conj hK hu hv.1, fun v' hv' => ?_⟩
  rw [twoAdic_inf_centralizer_conj hK]
  exact hv.2 v' hv'

@[expose] def Sol78Fusion39 (L K : Subgroup G) (u : G) : Prop :=
  ∀ v ∈ vMaximal K u, ∀ g ∈ centralizer ({u} : Set G),
    ∃ c ∈ L ⊓ centralizer ({u} : Set G), g * v * g⁻¹ = c * v * c⁻¹

@[expose] def Sol78Generate (L K : Subgroup G) (u : G) : Prop :=
  ∀ l ∈ L, l * u * l⁻¹ ∈ vPairs L K u → K ⊔ K.map (conjHom l) = L


end CFSG.EvenSporadicStandard.Solomon78
