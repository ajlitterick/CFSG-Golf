module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem actionCommutator_top_eq_top_of_moving_theta_quotient {p : ℕ} (hp : p.Prime)
    {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (hLperf : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (a : A) (g : L)
    (hnt : ((a • g : L) : L ⧸ aschbacherSolvableCore p L) ≠
      (g : L ⧸ aschbacherSolvableCore p L)) :
    actionCommutator A (⊤ : Subgroup L) = ⊤ := by
  classical
  set N := aschbacherSolvableCore p L with hN
  obtain ⟨hNs, hNchar, hNp, hNmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L) hp
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  set V := actionCommutator A (⊤ : Subgroup L) with hV
  have hVn : V.Normal := actionCommutator_top_normal
  have hVπ : V.map π = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
      (hVn.map π (QuotientGroup.mk'_surjective N)) with h | h
    · exact h
    · exfalso
      have := hLq.1
      set σ : MulAut (L ⧸ N) := mulAutQuotientHom N (MulDistribMulAction.toMulEquiv L a) with hσ
      have hσmk : ∀ x : L, σ (x : L ⧸ N) = ((a • x : L) : L ⧸ N) := fun x => rfl
      have hid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        σ.toMonoidHom (fun q => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
          have hx : x⁻¹ * (a • x) ∈ V := gen_mem_actionCommutator (mem_top x) a
          have hmem := h (Subgroup.mem_map_of_mem π hx)
          have e : ((x : L ⧸ N))⁻¹ * σ.toMonoidHom (x : L ⧸ N) = π (x⁻¹ * (a • x)) := by
            rw [map_mul, map_inv]
            rfl
          rw [e]
          exact hmem)
      apply hnt
      have := congrArg (fun φ : (L ⧸ N) →* (L ⧸ N) => φ (g : L ⧸ N)) hid
      simpa [hσmk] using this
  have hVN : V ⊔ N = ⊤ := by
    have h := comap_map_eq π V
    rw [hVπ, comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' V).comp N.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V q
    have hg : x ∈ ((V ⊔ N : Subgroup L) : Set L) := hVN ▸ mem_top x
    rw [normal_mul] at hg
    obtain ⟨m, hm, o, ho, rfl⟩ := hg
    refine ⟨⟨o, ho⟩, ?_⟩
    have hm1 : QuotientGroup.mk' V m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [MonoidHom.comp_apply, map_mul, hm1, one_mul]
    rfl
  have hsolv : Group.IsSolvable (L ⧸ V) := Group.isSolvable_of_surjective hsurj
  have htop : commutator (L ⧸ V) = ⊤ := by
    rw [_root_.commutator_def, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective V),
      ← map_commutator, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hsub : Subsingleton (L ⧸ V) := by
    by_contra hnt'
    rw [not_subsingleton_iff_nontrivial] at hnt'
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L ⧸ V)).ne htop
  refine eq_top_iff.mpr fun x _ => ?_
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

theorem commutator_le_centralizer_of_normalizes {X : Type*} [Group X] {Q K S : Subgroup X}
    (hQK : Q ≤ normalizer (K : Set X)) (hSK : S ≤ Subgroup.centralizer (K : Set X)) :
    ⁅Q, S⁆ ≤ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.commutator_le]
  intro q hq s hs
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : q⁻¹ * k * q ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hQK (Q.inv_mem hq)) k).mp hk
    simpa using this
  have h1 : s * (q⁻¹ * k * q) = (q⁻¹ * k * q) * s :=
    (Subgroup.mem_centralizer_iff.mp (hSK hs) _ hk').symm
  have h2 : s * k = k * s := (Subgroup.mem_centralizer_iff.mp (hSK hs) _ hk).symm
  have h2' : k * s⁻¹ = s⁻¹ * k := by
    have h3 : s⁻¹ * (s * k) * s⁻¹ = s⁻¹ * (k * s) * s⁻¹ := by rw [h2]
    simpa [mul_assoc] using h3
  calc k * ⁅q, s⁆ = q * ((q⁻¹ * k * q) * s) * q⁻¹ * s⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = q * (s * (q⁻¹ * k * q)) * q⁻¹ * s⁻¹ := by rw [h1]
    _ = q * s * q⁻¹ * (k * s⁻¹) := by group
    _ = q * s * q⁻¹ * (s⁻¹ * k) := by rw [h2']
    _ = ⁅q, s⁆ * k := by simp only [commutatorElement_def]; group

theorem commutator_le_left_of_normalizes {X : Type*} [Group X] {Q S : Subgroup X}
    (hSQ : S ≤ normalizer (Q : Set X)) : ⁅Q, S⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq s hs
  have h := (Subgroup.mem_normalizer_iff.mp (hSQ hs) q).mp hq
  have h' := (Subgroup.mem_normalizer_iff.mp (hSQ (S.inv_mem hs)) q).mp hq
  rw [commutatorElement_def]
  have e : q * s * q⁻¹ * s⁻¹ = q * (s * q⁻¹ * s⁻¹) := by group
  rw [e]
  refine Q.mul_mem hq ?_
  have := Q.inv_mem ((Subgroup.mem_normalizer_iff.mp (hSQ hs) q).mp hq)
  simpa [mul_assoc] using this

theorem eq_bot_of_centralizes_pcore_and_layer {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hθ : aschbacherSolvableCore p X = ⊥) {T : Subgroup X} (hT : ¬ p ∣ Nat.card T)
    (hTP : T ≤ Subgroup.centralizer (pCore p X : Set X))
    (hTE : T ≤ Subgroup.centralizer (layer X : Set X)) : T = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hTF : T ≤ Subgroup.centralizer (fittingSubgroup X : Set X) :=
    hTP.trans (Subgroup.centralizer_le (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot
      hp hθ))
  have hTstar : T ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff, generalizedFitting, sup_le_iff]
    exact ⟨Subgroup.le_centralizer_iff.mp hTF, Subgroup.le_centralizer_iff.mp hTE⟩
  set Cs := Subgroup.centralizer (generalizedFitting X : Set X)
  have hCsle : Cs ≤ generalizedFitting X := centralizer_generalizedFitting_le X
  have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).1
  have hCsn : Cs.Normal := Subgroup.normal_centralizer
  have hCscomm : IsMulCommutative Cs := ⟨⟨fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp x.2 y (hCsle y.2)).symm⟩⟩
  have hCsF : Cs ≤ fittingSubgroup X :=
    CFSG.LocalCores.fitting_characteristic.2.2 Cs hCsn inferInstance
  have hTP' : T ≤ pCore p X :=
    hTstar.trans (hCsF.trans (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot hp hθ))
  have hTp : IsPGroup p T := pCore_isPGroup.to_le hTP'
  rcases hTp.card_eq_or_dvd with h1 | hdvd
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd hdvd hT


end CFSG.RankThree.PartOne
