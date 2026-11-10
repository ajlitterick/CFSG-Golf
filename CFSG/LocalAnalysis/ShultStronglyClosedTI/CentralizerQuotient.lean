module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.OrderReductions.InvolutionGraph

variable {G : Type*} [Group G]

@[expose] def localCentralElement (u : G) : localCentralizer u :=
  ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem localCentralElement_mem_center (u : G) :
    localCentralElement u ∈ Subgroup.center (localCentralizer u) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp x.property

@[expose] def localCentralKernel (u : G) : Subgroup (localCentralizer u) :=
  Subgroup.zpowers (localCentralElement u)

theorem localCentralKernel_le_center (u : G) :
    localCentralKernel u ≤ Subgroup.center (localCentralizer u) :=
  Subgroup.zpowers_le.mpr (localCentralElement_mem_center u)

instance localCentralKernel_normal (u : G) : (localCentralKernel u).Normal :=
  Subgroup.normal_of_le_center (localCentralKernel_le_center u)


theorem quotient_injective_on_subgroup (U Z : Subgroup G) [Z.Normal]
    (hinj : Set.InjOn (QuotientGroup.mk' Z) ((U : Set G) \ {1}))
    (hdisjoint : U ⊓ Z = ⊥) : Set.InjOn (QuotientGroup.mk' Z) (U : Set G) := by
  intro x hx y hy heq
  by_cases hxone : x = 1
  · subst x
    have hyZ : y ∈ Z := (QuotientGroup.eq_one_iff y).mp
      ((map_one (QuotientGroup.mk' Z)).symm.trans heq).symm
    exact (Subgroup.mem_bot.mp (hdisjoint ▸ (show y ∈ U ⊓ Z from ⟨hy, hyZ⟩))).symm
  · by_cases hyone : y = 1
    · subst y
      have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp
        (heq.trans (map_one (QuotientGroup.mk' Z)))
      exact Subgroup.mem_bot.mp (hdisjoint ▸ (show x ∈ U ⊓ Z from ⟨hx, hxZ⟩))
    · exact hinj ⟨hx, by simpa only [Set.mem_singleton_iff] using hxone⟩
        ⟨hy, by simpa only [Set.mem_singleton_iff] using hyone⟩ heq


variable [Finite G]


omit [Finite G] in
theorem map_conj_natural {K : Type*} [Group K] (U : Subgroup G) (f : G →* K) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map f =
      (U.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]


end CFSG.ShultStronglyClosedTI
