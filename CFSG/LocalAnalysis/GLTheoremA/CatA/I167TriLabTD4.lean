module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10GTri

set_option linter.unusedSectionVars false


theorem td4_outer_data {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labK : GLALabel} (hT : labK.tag = .triD4) {α : MulAut S} (hfld : FieldKind S labK α)
    (hα : α ^ 3 = 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = (2 ^ labK.n) ^ 3) (Fr : K ≃+* K)
      (_ : ∀ c, Fr c = c ^ (2 ^ labK.n))
      (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)),
      φ ^ 3 = 1 ∧ φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)).range ∧
      Nonempty (↥(fixSubgroup α) ≃* ↥(fixSubgroup φ)) := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [hT] at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  obtain ⟨σ, hσ, ⟨eR⟩⟩ := triRecipe_equiv hlam'.1 hK
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eY := e.trans eR
  have hkey : ∀ s : S, (i * f) (e s) = e (α s) := fun s => hind s (α s) rfl
  have hαe : MulAut.congr e α = i * f := by
    ext r
    have h := hkey (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hnotI : i * f ∉ LargeEvenChevIDImage TwistTag.D4.tag.cartan K
      (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm lab'.n) :=
    fun h => hout ⟨i * f, h, hind⟩
  have hφ3 : MulAut.congr eY α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hcongr0 : MulAut.congr eY α = MulAut.congr eR (MulAut.congr e α) := MulEquiv.ext fun x => rfl
  have hcongr : MulAut.congr eY α = MulAut.congr eR (i * f) := by rw [hcongr0, hαe]
  have hφout : MulAut.congr eY α ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rw [hcongr]
    exact tri_not_inner_of_not_mem eR (tri_inn_mem_idImage _ K _) hnotI
  have hfix : (fixSubgroup α).map eY.toMonoidHom = fixSubgroup (MulAut.congr eY α) :=
    Y10F.fixSubgroup_map_congr eY α
  let eC : ↥(fixSubgroup α) ≃* ↥(fixSubgroup (MulAut.congr eY α)) :=
    (Subgroup.equivMapOfInjective _ eY.toMonoidHom eY.injective).trans (MulEquiv.subgroupCongr hfix)
  exact ⟨K, hKF, hKfin, hK, σ, hσ, MulAut.congr eY α, hφ3, hφout, ⟨eC⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
