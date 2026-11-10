module

public import CFSG.Milestones.ASVolI.C135.NC
public import CFSG.Milestones.ASVolI.C135.P4a
public import CFSG.Milestones.ASVolI.C135.P4c
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Fin

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q mem_pCoreOf_iff')
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll msPair_facts)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]


namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H


@[expose] noncomputable def q0 : QC (centerOf (c134Q X L)) ⊥ F where
  κ u := Multiplicative.toAdd (βU u)
  mul u v := by
    show Multiplicative.toAdd (βU (u * v)) =
      Multiplicative.toAdd (βU u) + Multiplicative.toAdd (βU v)
    rw [map_mul, toAdd_mul]
  surj v := by
    obtain ⟨u, hu⟩ := H.dsg.natU_onto (Multiplicative.ofAdd v)
    exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
  ker u := by
    show Multiplicative.toAdd (βU u) = 0 ↔ (u : G) ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : βU u = βU 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h
      exact congrArg Subtype.val (burnsideC135_βU_injective H.dsg h1)
    · intro h
      have : u = 1 := Subtype.ext h
      rw [this, map_one]
      rfl

@[expose] noncomputable def q1 : QC (burnsideC135_Wc β 1) (centerOf (c134Q X L)) F where
  κ w := Multiplicative.toAdd (burnsideC135_βc β 1 w)
  mul u v := by
    show Multiplicative.toAdd (burnsideC135_βc β 1 (u * v)) =
      Multiplicative.toAdd (burnsideC135_βc β 1 u) + Multiplicative.toAdd (burnsideC135_βc β 1 v)
    rw [map_mul, toAdd_mul]
  surj v := by
    obtain ⟨u, hu⟩ := H.dsg.dual₁_onto (Multiplicative.ofAdd v)
    exact ⟨u, (congrArg Multiplicative.toAdd hu).trans (toAdd_ofAdd v)⟩
  ker w := by
    show Multiplicative.toAdd (burnsideC135_βc β 1 w) = 0 ↔ (w : G) ∈ centerOf (c134Q X L)
    have h := H.dsg.dual₁_ker
    constructor
    · intro h0
      have h3 : w ∈ (burnsideC135_βc β 1).ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective h0
      rw [h, Subgroup.mem_subgroupOf] at h3
      exact h3
    · intro h0
      have h3 : w ∈ (burnsideC135_βc β 1).ker := by
        rw [h, Subgroup.mem_subgroupOf]
        exact h0
      rw [MonoidHom.mem_ker] at h3
      rw [h3]
      rfl

@[expose] noncomputable def q2 : QC (c134Q X L) (burnsideC135_Wc β 1) F where
  κ q := Multiplicative.toAdd (β q) 1
  mul u v := by
    show Multiplicative.toAdd (β (u * v)) 1 =
      Multiplicative.toAdd (β u) 1 + Multiplicative.toAdd (β v) 1
    rw [map_mul, toAdd_mul, Pi.add_apply]
  surj v := by
    obtain ⟨u, hu⟩ := H.βs (Multiplicative.ofAdd (fun _ => v))
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd (β u) 1 = v
    rw [hu]
    rfl
  ker q := by
    show Multiplicative.toAdd (β q) 1 = 0 ↔ (q : G) ∈ burnsideC135_Wc β 1
    constructor
    · intro h0
      exact burnsideC135_mem_Wc.mpr ⟨q.2, h0⟩
    · intro h0
      obtain ⟨hh, h3⟩ := burnsideC135_mem_Wc.mp h0
      exact h3


end burnsideC135_H1

end CFSG.ASVolI

end
