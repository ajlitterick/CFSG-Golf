module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedLeviDescent
public import CFSG.RankThree.PartOne.D4RC.ParaConn
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.Chevalley.ParabolicSelfNormalizing
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral

public section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [IsAlgClosed k]

theorem entrywiseFrobGL_mem_parabolicSubgroup {τ : Tag} (e : ℕ) (J : Set (Fin τ.rank))
    {g : ModGL τ k} (hg : g ∈ parabolicSubgroup τ k J) :
    entrywiseFrobGL τ k p e g ∈ parabolicSubgroup τ k J := by
  have hσ : (iterateFrobeniusEquiv k p e).toRingHom = iterateFrobenius k p e :=
    RingHom.ext fun _ => rfl
  have hmap : (parabolicSubgroup τ k J).map (entrywiseFrobGL τ k p e) ≤
      parabolicSubgroup τ k J := by
    rw [parabolicSubgroup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro b hb
      have h := entrywise_mem_borelGroup (σ := iterateFrobeniusEquiv k p e) hb
      rw [hσ] at h
      exact borelGroup_le_parabolicSubgroup J h
    · rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, hj, rfl⟩
      change entrywiseFrobGL τ k p e (weylElt τ k j 1) ∈ parabolicSubgroup τ k J
      have h := entrywise_weylElt_one (iterateFrobeniusEquiv k p e) j
      rw [hσ] at h
      rw [h]
      exact weylElt_mem_parabolicSubgroup hj
  exact hmap (Subgroup.mem_map_of_mem _ hg)


theorem exists_frobTwistGL_fixed_mul_of_mem_normalizer_parabolic {τ : Tag} {e : ℕ} (he : 1 ≤ e)
    (Q : ModGL τ k) {J : Set (Fin τ.rank)}
    (hP : ∀ g ∈ parabolicSubgroup τ k J, frobTwistGL τ k p e Q g ∈ parabolicSubgroup τ k J)
    (hA : ∀ g ∈ adjointGroup τ k, frobTwistGL τ k p e Q g ∈ adjointGroup τ k)
    {x : ModGL τ k} (hx : x ∈ adjointGroup τ k)
    (hN : x * (frobTwistGL τ k p e Q x)⁻¹ ∈
      Subgroup.normalizer (parabolicSubgroup τ k J : Set (ModGL τ k))) :
    ∃ z ∈ parabolicSubgroup τ k J, frobTwistGL τ k p e Q (z * x) = z * x := by
  have hFx : frobTwistGL τ k p e Q x ∈ adjointGroup τ k := hA x hx
  have hc : x * (frobTwistGL τ k p e Q x)⁻¹ ∈
      adjointGroup τ k ⊓ Subgroup.normalizer (parabolicSubgroup τ k J : Set (ModGL τ k)) :=
    Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem hFx), hN⟩
  have hcP : x * (frobTwistGL τ k p e Q x)⁻¹ ∈ parabolicSubgroup τ k J :=
    (le_of_eq (adjointGroup_inf_normalizer_parabolicSubgroup (τ := τ) (K := k) J)) hc
  have hZconn : IsConnectedAlgebraicSubgroup k
      ((parabolicSubgroup τ k J).map (modGLPoint τ k).toMonoidHom) :=
    CFSG.RankThree.PartOne.D4RC.rcp_isConnectedAlgebraicSubgroup_parabolic (K := k) J
  obtain ⟨-, -, -, hlang⟩ :=
    exists_frobTwist_restriction (τ := τ) (k := k) p hZconn (Z := parabolicSubgroup τ k J) he Q hP
  obtain ⟨z, hz, hzc⟩ := hlang _ hcP
  refine ⟨z, hz, ?_⟩
  have hFz : frobTwistGL τ k p e Q z = z * (x * (frobTwistGL τ k p e Q x)⁻¹) := by
    rw [← hzc]
    group
  rw [map_mul, hFz]
  group

theorem exists_entrywiseFrobGL_fixed_mul_of_mem_normalizer_parabolic {τ : Tag} {e : ℕ} (he : 1 ≤ e)
    {J : Set (Fin τ.rank)} {x : ModGL τ k} (hx : x ∈ adjointGroup τ k)
    (hN : x * (entrywiseFrobGL τ k p e x)⁻¹ ∈
      Subgroup.normalizer (parabolicSubgroup τ k J : Set (ModGL τ k))) :
    ∃ z ∈ parabolicSubgroup τ k J, entrywiseFrobGL τ k p e (z * x) = z * x := by
  have hP : ∀ g ∈ parabolicSubgroup τ k J, frobTwistGL τ k p e 1 g ∈ parabolicSubgroup τ k J := by
    intro g hg
    rw [frobTwistGL_apply]
    simpa using entrywiseFrobGL_mem_parabolicSubgroup (p := p) (τ := τ) e J hg
  have hA : ∀ g ∈ adjointGroup τ k, frobTwistGL τ k p e 1 g ∈ adjointGroup τ k := by
    intro g hg
    rw [frobTwistGL_apply]
    simpa using entrywiseFrobGL_mem (τ := τ) (L := k) p e hg
  have hN' : x * (frobTwistGL τ k p e 1 x)⁻¹ ∈
      Subgroup.normalizer (parabolicSubgroup τ k J : Set (ModGL τ k)) := by
    rw [frobTwistGL_apply]
    simpa using hN
  obtain ⟨z, hz, hzx⟩ :=
    exists_frobTwistGL_fixed_mul_of_mem_normalizer_parabolic (p := p) (τ := τ) he 1 hP hA hx hN'
  refine ⟨z, hz, ?_⟩
  rw [frobTwistGL_apply] at hzx
  simpa using hzx


end CFSG.LieType.AlgebraicGroups
