module

public import CFSG.GH74.GLS.SP.Assembly
public import CFSG.GH74.GLS.SP.GlueMap
public import CFSG.GH74.GLS.SP.SpRGD

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem SPGlueData.of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {F : Type}
    [Field F] {hF : 4 ≤ Nat.card F} (h : SPGlueData G' F hF) : SPGlueData G F hF := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  have hker : (e.symm : G' →* G).ker ≤ H := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact bot_le
  have hU : U ⊓ (e.symm : G' →* G).ker = ⊥ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact inf_bot_eq U
  refine ⟨H.map (e.symm : G' →* G), (e.symm : G' →* G) r₁, (e.symm : G' →* G) r₂,
    U.map (e.symm : G' →* G), fun i => (root i).map (e.symm : G' →* G),
    R.map (e.symm : G' →* G) hker hU,
    R.map_gen (e.symm : G' →* G) e.symm.surjective hker hU hgen,
    (MulEquiv.subgroupMap e.symm U).symm.trans φ, ?_⟩
  intro i h1 h4 x
  have hyx : (((MulEquiv.subgroupMap e.symm U).symm x : U) : G') = e (x : G) := by
    simp [MulEquiv.subgroupMap_symm_apply]
  have key := hφ i h1 h4 ((MulEquiv.subgroupMap e.symm U).symm x)
  rw [hyx] at key
  have hx : (x : G) ∈ (root i).map (e.symm : G' →* G) ↔ e (x : G) ∈ root i := by
    have := Subgroup.mem_map_equiv (f := e.symm) (K := root i) (x := (x : G))
    simpa using this
  rw [hx]
  exact key


end CFSG.GH74.GLS.SP
