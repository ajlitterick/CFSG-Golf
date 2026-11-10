module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.G2A5Iso

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement


theorem dss24_ncard_conj_orbit {G : Type} [Group G] [Finite G] (K Y : Subgroup G) :
    Set.ncard {X : Subgroup G | ∃ g ∈ K, X = Y.map (MulAut.conj g).toMonoidHom} =
      (K ⊓ Subgroup.normalizer (Y : Set G)).relIndex K := by
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  have hsmul : ∀ (f : MulAut G) (X : Subgroup G), f • X = X.map f.toMonoidHom :=
    fun _ _ => rfl
  have hstab : (MulAction.stabilizer (MulAut G) Y).comap MulAut.conj =
      Subgroup.normalizer (Y : Set G) := by
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]
  have horb : {X : Subgroup G | ∃ g ∈ K, X = Y.map (MulAut.conj g).toMonoidHom} =
      MulAction.orbit (K.map MulAut.conj) Y := by
    ext X
    simp only [Set.mem_setOf_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨MulAut.conj g, Subgroup.mem_map_of_mem _ hg⟩, rfl⟩
    · rintro ⟨⟨f, hf⟩, rfl⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf
      exact ⟨g, hg, rfl⟩
  rw [horb, ← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf,
    ← Subgroup.relIndex, ← Subgroup.relIndex_comap, hstab, inf_comm,
    Subgroup.inf_relIndex_right]

private abbrev cj {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

private theorem mem_cj {G : Type} [Group G] {g : G} {H : Subgroup G} {y : G} :
    y ∈ cj g H ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      group
    rw [e]
    exact hz
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by
      simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      group⟩

private theorem cj_mul {G : Type} [Group G] (g h : G) (H : Subgroup G) :
    cj (g * h) H = cj g (cj h H) := by
  ext y
  rw [mem_cj, mem_cj, mem_cj]
  have e : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
  rw [e]


private theorem cj_eq_of_mem_normalizer {G : Type} [Group G] {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cj g H = H := by
  ext y
  rw [mem_cj]
  have hn := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [e] at hn
  exact hn


end CFSG.GH74.QTGen4.DSGen4
