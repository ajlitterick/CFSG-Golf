module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll centralizerPerfectCore_eq_map_of_le)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono mem_modelToG symm_mem_modelToG)

section Points

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)


end Points

section Equivariance

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

@[expose] def TorusEquivariant (N : Finset (Fin n)) (P : Subgroup (Fin n → Kˣ))
    (Φ : spBlock F N →* G) : Prop :=
  ∀ t ∈ P, ∀ x : spBlock F N,
    Φ (conjDiagSp N (liftParam ι t) x) =
      ((e.symm (diagSp K n t) : L) : G) * Φ x * ((e.symm (diagSp K n t) : L) : G)⁻¹

theorem TorusEquivariant.mono {N : Finset (Fin n)} {P Q : Subgroup (Fin n → Kˣ)} (hQP : Q ≤ P)
    {Φ : spBlock F N →* G} (hΦ : TorusEquivariant e ι N P Φ) : TorusEquivariant e ι N Q Φ :=
  fun t ht x => hΦ t (hQP ht) x

theorem TorusEquivariant.of_top {N : Finset (Fin n)} (P : Subgroup (Fin n → Kˣ))
    {Φ : spBlock F N →* G} (hΦ : TorusEquivariant e ι N ⊤ Φ) : TorusEquivariant e ι N P Φ :=
  hΦ.mono e ι le_top

theorem exists_param_of_mem_modelToG_diagTorusSp {P : Subgroup (Fin n → Kˣ)} {d : G}
    (hd : d ∈ modelToG e (diagTorusSp K P)) :
    ∃ t ∈ P, ((e.symm (diagSp K n t) : L) : G) = d := by
  obtain ⟨x, ⟨t, ht, rfl⟩, rfl⟩ := (mem_modelToG e).1 hd
  exact ⟨t, ht, rfl⟩

end Equivariance

section Piece

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

include ι in
theorem le_card_of_ringHom {c : ℕ} (hK : c ≤ Nat.card K) : c ≤ Nat.card F :=
  hK.trans (Nat.card_le_card_of_injective ι ι.injective)

omit [Finite G] [Finite F] in
theorem map_fixAll_conjDiagSp_eq {P : Subgroup (Fin n → Kˣ)} {N : Finset (Fin n)}
    (τ : modelToG e (diagTorusSp K P) → Fin n → Kˣ)
    (hτ : ∀ d, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d) :
    (fixAll fun d => conjDiagSp N (liftParam ι (τ d))).map (spBlock F N).subtype =
      spBlock F N ⊓ centralizer (diagSp F n '' (liftParam ι '' (P : Set (Fin n → Kˣ)))) := by
  have hsurj : ∀ t ∈ P, ∃ d, τ d = t := by
    intro t ht
    let d : modelToG e (diagTorusSp K P) :=
      ⟨((e.symm (diagSp K n t) : L) : G), symm_mem_modelToG e ⟨t, ht, rfl⟩⟩
    refine ⟨d, ?_⟩
    have h' : e.symm (diagSp K n (τ d)) = e.symm (diagSp K n t) := Subtype.ext (hτ d).2
    exact diagSp_injective (e.symm.injective h')
  ext x
  simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨d, rfl⟩ := hsurj t ht
    have h := congrArg Subtype.val (mem_fixAll.1 hy d)
    rw [coe_conjDiagSp_apply] at h
    calc diagSp F n (liftParam ι (τ d)) * (y : StatedSp n F) =
          diagSp F n (liftParam ι (τ d)) * (y : StatedSp n F) *
            (diagSp F n (liftParam ι (τ d)))⁻¹ * diagSp F n (liftParam ι (τ d)) := by group
      _ = (y : StatedSp n F) * diagSp F n (liftParam ι (τ d)) := by rw [h]
  · rintro ⟨hxN, hx⟩
    refine ⟨⟨x, hxN⟩, mem_fixAll.2 fun d => Subtype.ext ?_, rfl⟩
    rw [coe_conjDiagSp_apply]
    change diagSp F n (liftParam ι (τ d)) * x * (diagSp F n (liftParam ι (τ d)))⁻¹ = x
    rw [hx _ ⟨_, ⟨τ d, (hτ d).1, rfl⟩, rfl⟩, mul_inv_cancel_right]

theorem torusCore_eq_map_of_conjDiagSp {P : Subgroup (Fin n → Kˣ)} {N : Finset (Fin n)}
    {H : Subgroup (StatedSp n F)} (hHN : H ≤ spBlock F N)
    (hLevi : perfectCore (spBlock F N ⊓
      centralizer (diagSp F n '' (liftParam ι '' (P : Set (Fin n → Kˣ))))) = H)
    {X : Subgroup G} (hXP : X ≤ modelToG e (diagTorusSp K P))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦ : TorusEquivariant e ι N P Φ) :
    torusCore e P = (H.subgroupOf (spBlock F N)).map Φ := by
  set T := modelToG e (diagTorusSp K P)
  let τ : T → Fin n → Kˣ := fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose
  have hτ : ∀ d : T, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d :=
    fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose_spec
  have hα : ∀ (d : T) (x : spBlock F N),
      Φ (conjDiagSp N (liftParam ι (τ d)) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (hτ d).1 x, (hτ d).2]
  rw [torusCore, centralizerPerfectCore_eq_map_of_le Φ hker hXP hrange
    (fun d => conjDiagSp N (liftParam ι (τ d))) hα]
  congr 1
  apply Subgroup.map_injective (spBlock F N).subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, map_fixAll_conjDiagSp_eq e ι τ hτ, hLevi,
    subgroupOf_map_subtype, inf_of_le_left hHN]

theorem planeCore_eq_map_of_conjDiagSp {κ : Kˣ} (hκ : κ * κ ≠ 1) {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (hperf : ⁅spBlock F I, spBlock F I⁆ = spBlock F I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (planeTorusSp K I))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : TorusEquivariant e ι N (planeTorusParam K I) Φ) :
    planeCore e I = ((spBlock F I).subgroupOf (spBlock F N)).map Φ :=
  torusCore_eq_map_of_conjDiagSp e ι (spBlock_mono hIN)
    (perfectCore_spBlock_inf_centralizer_planeTorus ι hκ hIN hperf) hXI Φ hker hrange hΦ

theorem planeCore_eq_map_of_conjDiagSp_of_four_le (hK : 4 ≤ Nat.card K) {N I : Finset (Fin n)}
    (hIN : I ⊆ N) {X : Subgroup G} (hXI : X ≤ modelToG e (planeTorusSp K I))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : TorusEquivariant e ι N (planeTorusParam K I) Φ) :
    planeCore e I = ((spBlock F I).subgroupOf (spBlock F N)).map Φ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact planeCore_eq_map_of_conjDiagSp e ι hκ hIN
    (commutator_spBlock_eq (le_card_of_ringHom ι hK) I) hXI Φ hker hrange hΦ


omit [Finite G] [Finite F] in
theorem subset_compl_singleton_of_notMem {k : Fin n} {I : Finset (Fin n)} (hk : k ∉ I) :
    I ⊆ ({k}ᶜ : Finset (Fin n)) := fun i hi => by
  simp only [Finset.mem_compl, Finset.mem_singleton]
  exact fun h => hk (h ▸ hi)

omit [Finite G] [Finite F] in
theorem modelToG_rootTorusSp_le_planeTorusSp {k : Fin n} {I : Finset (Fin n)} (hk : k ∉ I) :
    modelToG e (rootTorusSp K k) ≤ modelToG e (planeTorusSp K I) := by
  refine modelToG_mono e ?_
  rw [rootTorusSp_eq_planeTorusSp]
  exact planeTorusSp_anti (subset_compl_singleton_of_notMem hk)

theorem planeCore_eq_map_of_neighbourCore (hK : 4 ≤ Nat.card K) {k : Fin n} {I : Finset (Fin n)}
    (hk : k ∉ I) (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Φ.range = neighbourCore e k)
    (hΦ : TorusEquivariant e ι {k}ᶜ (planeTorusParam K I) Φ) :
    planeCore e I = ((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map Φ :=
  planeCore_eq_map_of_conjDiagSp_of_four_le e ι hK (subset_compl_singleton_of_notMem hk)
    (modelToG_rootTorusSp_le_planeTorusSp e hk) Φ hker hrange hΦ


end Piece

end CFSG.SeitzReduction.SymplecticPilot
