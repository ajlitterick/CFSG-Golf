module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxR
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxMax

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem isSolvableSection_of_perfRes_le {X N : Subgroup G} (h : perfRes X ≤ N) :
    IsSolvableSection X N := by
  obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥X)
  refine ⟨n, ?_⟩
  rw [← hn]
  exact Subgroup.map_le_iff_le_comap.mp h

theorem thetaOf_mem_cset_bot
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) (hns : ¬ Group.IsSolvable (thetaOf θ B)) : thetaOf θ B ∈ cset p A θ ⊥ :=
  (h.mem_rSet_iff.mpr ⟨hB, hBA, hns⟩).2.2

theorem lemma63a
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≠ ⊥) (hBA : B ≤ A)
    (hns : ¬ Group.IsSolvable (thetaOf θ B)) :
    IsSolvableSection (thetaOf θ B) (kOf (thetaOf θ B)) :=
  isSolvableSection_of_perfRes_le (h.perfRes_le_kOf (h.thetaOf_mem_cset_bot hBA hB hns))


theorem sol_thetaOf_eq_bot
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≠ ⊥)
    (hBA : B ≤ A) (hns : ¬ Group.IsSolvable (thetaOf θ B)) : sol (thetaOf θ B) = ⊥ :=
  h.sol_eq_bot_of_mem_cset (h.thetaOf_mem_cset_bot hBA hB hns)


theorem perfRes_thetaOf_eq_kOf
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≠ ⊥)
    (hBA : B ≤ A) (hns : ¬ Group.IsSolvable (thetaOf θ B)) :
    perfRes (thetaOf θ B) = kOf (thetaOf θ B) :=
  h.perfRes_eq_kOf (h.thetaOf_mem_cset_bot hBA hB hns)


theorem exists_conj_eq_of_mem_lcal_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ≠ ⊥) (hBA : B ≤ A) (hns : ¬ Group.IsSolvable (thetaOf θ B)) {J J' : Subgroup G}
    (hJ : J ∈ lcal (kOf (thetaOf θ B))) (hJ' : J' ∈ lcal (kOf (thetaOf θ B))) :
    ∃ g ∈ dsub A θ ⊔ A, J' = J.map (MulAut.conj g).toMonoidHom :=
  h.exists_conj_eq_of_mem_lcal_kOf (h.thetaOf_mem_cset_bot hBA hB hns) hJ hJ'

theorem lemma64
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) :
    (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b)) = wsub p A θ :=
  h.iSup_kOf_apply_eq_wsub hB


theorem rSetN_two_nonempty
    (h : Counterexample p A θ) : (rSetN p A θ 2).Nonempty :=
  h.rSetN_two_nonempty_aux

theorem lemma66
    (h : Counterexample p A θ) {B B' : Subgroup G} (hB : B ∈ rSet p A θ)
    (hB' : B' ∈ rSet p A θ) :
    dsub A θ ⊓ kOf (thetaOf θ B) = dsub A θ ⊓ kOf (thetaOf θ B') :=
  h.inf_kOf_eq_of_mem_rSet hB hB'

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
