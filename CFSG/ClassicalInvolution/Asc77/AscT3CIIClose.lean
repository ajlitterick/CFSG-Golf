module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIExact
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIInv
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexC

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Close

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

@[expose] def LamMem (z a₀ : G) (L : Subgroup G) : Prop :=
  ∃ n ∈ Subgroup.centralizer ({a₀} : Set G), ∃ e : G, IsUniqueInvolution L e ∧ n * e * n⁻¹ = z

omit [Finite G] in
theorem LamMem.of_conj {z a₀ n : G} {L : Subgroup G} (hn : n ∈ Subgroup.centralizer ({a₀} : Set G))
    (h : LamMem z a₀ (conjSub n L)) : LamMem z a₀ L := by
  obtain ⟨n₂, hn₂, e₂, he₂, hne₂⟩ := h
  refine ⟨n₂ * n, (Subgroup.centralizer _).mul_mem hn₂ hn, n⁻¹ * e₂ * n, ?_, ?_⟩
  · have := he₂.conj n⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at this
  · rw [← hne₂]
    group

omit [Finite G] in
theorem LamMem.cent {z a₀ : G} {L : Subgroup G} (h : LamMem z a₀ L)
    (hP : ∀ n ∈ Subgroup.centralizer ({a₀} : Set G), ∀ e : G, IsUniqueInvolution L e →
      n * e * n⁻¹ = z → ∀ l ∈ L, a₀ * (n * l * n⁻¹) = (n * l * n⁻¹) * a₀) :
    ∀ l ∈ L, a₀ * l = l * a₀ := by
  obtain ⟨n, hn, e, he, hne⟩ := h
  intro l hl
  have h2 := hP n hn e he hne l hl
  have h3 : a₀ * n = n * a₀ := (Subgroup.mem_centralizer_singleton_iff.mp hn).symm
  have h4 : a₀ * n⁻¹ = n⁻¹ * a₀ := by
    have := (Subgroup.centralizer ({a₀} : Set G)).inv_mem hn
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  calc a₀ * l = n⁻¹ * (a₀ * (n * l * n⁻¹)) * n := by
        calc a₀ * l = (n⁻¹ * n) * a₀ * l := by group
          _ = n⁻¹ * (n * a₀) * l := by group
          _ = n⁻¹ * (a₀ * n) * l := by rw [h3]
          _ = n⁻¹ * (a₀ * (n * l * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * l * n⁻¹) * a₀) * n := by rw [h2]
    _ = l * a₀ := by
        calc n⁻¹ * ((n * l * n⁻¹) * a₀) * n = l * (n⁻¹ * a₀ * n) := by group
          _ = l * (a₀ * n⁻¹ * n) := by rw [← h4]
          _ = l * a₀ := by group

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem exists_rho {a₀ : G} (haK : K ≤ Subgroup.centralizer ({a₀} : Set G))
    (haJ : J ≤ Subgroup.centralizer ({a₀} : Set G)) :
    ∃ ρ ∈ Subgroup.centralizer ({a₀} : Set G), ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hpair : pairNormalizers K J z t ≤ Subgroup.centralizer ({a₀} : Set G) :=
    sup_le (inf_le_left.trans haK) (inf_le_left.trans haJ)
  refine ⟨t₀ * r, (Subgroup.centralizer _).mul_mem (hpair hh.t₀_mem_pair) (hpair hh.r_mem_pair),
    ?_⟩
  calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
    _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
    _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
    _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
    _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem twinSet_K' : twinSet (CoreAssembly.conjClass K) K' = {K', K} := by
  ext L
  constructor
  · rintro ⟨hL, z', hz'K', hz'L⟩
    have hzz : z' = z := hz'K'.eq d.late_hzK'
    subst hzz
    have hm : L ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hL, z', d.viol.hzK, hz'L⟩
    rw [d.twins] at hm
    rcases hm with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · subst h
      exact ⟨d.late_mem_K', z, d.late_hzK', d.late_hzK'⟩
    · subst h
      exact ⟨d.late_mem_K, z, d.late_hzK', d.viol.hzK⟩


end Std20

theorem oddCoreOf_inf_le {L H : Subgroup G} (hHL : H ≤ L) : oddCoreOf L ⊓ H ≤ oddCoreOf H := by
  refine Balance.le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
  · intro g hg
    have hgL : g ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hHL hg))
    have hgM : g ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hg
    rw [mem_normalizer_iff_conjSub_eq] at hgL hgM ⊢
    rw [late_conjSub_inf, hgL, hgM]
  · exact (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem concl20_4_of_hex (hH : Hex20 (CoreAssembly.conjClass K) K J W) :
    Concl20_4 S K K' J z := by
  refine d.concl20_4_of_98 hH ?_ (d.late_tor hH.JW hH.hW)
  exact (d.late_98 hH.JW hH.hW (X := centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (S.isPGroup'.to_le (fun x hx => hx.1)) (fun x hx => hx.1) (fun x hx => d.cent_comm_t hx)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer hx))).2

theorem cent_le_normalizer' {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K' : Set G) := by
  have h1 := mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer ha)
  exact mem_normalizer_iff_conjSub_eq.mpr ((d.late_conj_iff (d.hSz ha.1)).mp h1)


end Std20

end Close

end CFSG.ClassicalInvolution.Asc77.T3CII
