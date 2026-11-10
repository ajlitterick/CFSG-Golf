module

public import CFSG.Timmesfeld.ARS.CaseHWeyl
public import CFSG.Timmesfeld.ARS.CaseHProj

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

theorem proj_conj_U5 {x : G} (hx : x ∈ shortRoot R A A₀ P') (g : ↥(M R A))
    (hg : x * g * x⁻¹ ∈ M R A) :
    ((S.proj ⟨x * g * x⁻¹, hg⟩).2.1 : G) = cxy S x (S.proj g).1 * (S.proj g).2.1 := by
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot hx)
  obtain ⟨hK, hUU, -, -, -, -⟩ := S.facts
  obtain ⟨hU13, hU1P', -⟩ :=
    positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  rw [S.proj_conj hxN g]
  simp only [Prod.snd_mul, Prod.fst_mul, Subgroup.coe_mul]
  set p := (S.proj g).1
  set u := (S.proj g).2.1
  set u' := (S.proj g).2.2.1
  set p' := (S.proj g).2.2.2
  have h1 : ((S.proj ⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P_le_M p.2)⟩).2.1 : G) = cxy S x p := by
    have hH := commutator_mem_H S hx p.2
    have e : (⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P_le_M p.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (p : G)⁆, hH.1⟩ * ⟨p, S.P_le_M p.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_P p.2, Prod.snd_mul, Prod.fst_mul, mul_one, (S.proj_H hH).2]
    rfl
  have h2 : ((S.proj ⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U5_le_M u.2)⟩).2.1 : G) = u := by
    have hk : ⁅x, (u : G)⁆ ∈ M R A ⊓ M R P' := hUU (Subgroup.commutator_mem_commutator hx u.2)
    have e : (⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U5_le_M u.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u : G)⁆, hk.1⟩ * ⟨u, U5_le_M u.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U5 u.2, Prod.snd_mul, Prod.fst_mul, (S.proj_K hk).2, one_mul]
  have h3 : ((S.proj ⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U3_le_M u'.2)⟩).2.1 : G) = 1 := by
    have hc : ⁅x, (u' : G)⁆ ∈ P' := hU13 (Subgroup.commutator_mem_commutator hx u'.2)
    have e : (⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U3_le_M u'.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u' : G)⁆, S.P'_le_M hc⟩ * ⟨u', U3_le_M u'.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U3 u'.2, S.proj_P' hc]
    simp
  have h4 : ((S.proj ⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P'_le_M p'.2)⟩).2.1 : G) = 1 := by
    have e : (⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P'_le_M p'.2)⟩ :
        ↥(M R A)) = ⟨p', S.P'_le_M p'.2⟩ :=
      Subtype.ext (by simp only; rw [(hU1P' x hx _ p'.2).eq, mul_inv_cancel_right])
    rw [e, S.proj_P' p'.2]
    rfl
  rw [h1, h2, h3, h4, mul_one, mul_one]


end Setup

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

theorem c5_zero_left (u : F) : c.c5 0 u = 1 := by
  rw [c5, cxy, c.x1_zero, commutatorElement_one_left]
  refine comp5_eq S ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩ (Subgroup.one_mem _) ?_
  rw [inv_one, mul_one]
  exact Subgroup.one_mem _

theorem x5_add (s s' : E) : c.x5 (s + s') = c.x5 s * c.x5 s' := c.c5_add_left s s' 1

theorem x5_zero : c.x5 0 = 1 := c.c5_zero_left 1

theorem x5_injective : Function.Injective c.x5 := c.c5_one_injective

theorem x5_surjective {y : G} (hy : y ∈ shortRoot R P' ⁅A₀, P⁆ A) : ∃ s, c.x5 s = y := by
  have := S.hyp.finite
  have hbij : Function.Bijective fun s : E => (⟨c.x5 s, c.x5_mem s⟩ :
      shortRoot R P' ⁅A₀, P⁆ A) :=
    (Function.Injective.bijective_of_nat_card_le
      (fun s s' e => c.x5_injective (congrArg Subtype.val e)) c.card_E.ge)
  obtain ⟨s, hs⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨s, congrArg Subtype.val hs⟩

theorem comm1_mem (s : E) : ⁅c.x1 s, c.x6 1⁆ ∈ M R A :=
  (commutator_mem_H S (c.x1_mem s) (c.x6_mem 1)).1

@[expose] noncomputable def n2 (s : E) : G := (S.proj ⟨_, c.comm1_mem s⟩).2.2.2

@[expose] noncomputable def N (s : E) : F :=
  Classical.choose (c.x2_surjective (S.proj ⟨_, c.comm1_mem s⟩).2.2.2.2)

theorem x2_N (s : E) : c.x2 (c.N s) = c.n2 s :=
  Classical.choose_spec (c.x2_surjective (S.proj ⟨_, c.comm1_mem s⟩).2.2.2.2)


section Weyl

variable [CharP E 2]

theorem x3_surjective {y : G} (hy : y ∈ shortRoot R P ⁅A₀, P'⁆ A) : ∃ s, c.x3 s = y := by
  obtain ⟨s, hs⟩ := c.x5_surjective (c.conj_m_mem c.conjSub_U3_m hy)
  refine ⟨s, ?_⟩
  rw [x3, hs, c.m_inv]
  simp only [← mul_assoc, c.m_mul_self, one_mul]
  rw [mul_assoc, c.m_mul_self, mul_one]

@[expose] noncomputable def n3 (s : E) : G := (S.proj ⟨_, c.comm1_mem s⟩).2.2.1

@[expose] noncomputable def sharp (s : E) : E :=
  Classical.choose (c.x3_surjective (S.proj ⟨_, c.comm1_mem s⟩).2.2.1.2)

theorem x3_sharp (s : E) : c.x3 (c.sharp s) = c.n3 s :=
  Classical.choose_spec (c.x3_surjective (S.proj ⟨_, c.comm1_mem s⟩).2.2.1.2)

theorem proj_m_conj (g : ↥(M R A)) (hg : c.m * g * c.m⁻¹ ∈ M R A) :
    ((S.proj ⟨c.m * g * c.m⁻¹, hg⟩).1 : G) = c.m * (S.proj g).2.2.2 * c.m⁻¹ ∧
      ((S.proj ⟨c.m * g * c.m⁻¹, hg⟩).2.1 : G) = c.m * (S.proj g).2.2.1 * c.m⁻¹ := by
  rw [S.proj_conj c.m_mem_normalizer g]
  have h1 := c.conj_m_mem c.conjSub_P_m (S.proj g).1.2
  have h2 := c.conj_m_mem c.conjSub_U5_m (S.proj g).2.1.2
  have h3 := c.conj_m_mem c.conjSub_U3_m (S.proj g).2.2.1.2
  have h4 := c.conj_m_mem c.conjSub_P'_m (S.proj g).2.2.2.2
  rw [S.proj_P' h1, S.proj_U3 h2, S.proj_U5 h3, S.proj_P h4]
  simp

theorem conjSub_P_km (μ : Eˣ) : conjSub P (c.k μ * c.m) = P' := by
  rw [conjSub_mul, c.conjSub_P_m, c.conjSub_P'_k]

theorem sharp_eq (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1) {τ : F} (hτ0 : τ ≠ 0)
    (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u)) {s : E} (hs : s ≠ 0) :
    c.sharp s = e (τ⁻¹ * c.N s) * s⁻¹ := by
  have hR := S.hyp.root
  set y := c.x1 s * c.x6 1 * (c.x1 s)⁻¹ with hy
  have hyc : y = ⁅c.x1 s, c.x6 1⁆ * c.x6 1 := by
    rw [hy, commutatorElement_def]
    group
  have hyM : y ∈ M R A := by
    rw [hyc]
    exact Subgroup.mul_mem _ (c.comm1_mem s) (S.P_le_M (c.x6_mem 1))
  have hz : c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹ ∈ P' := by
    have hkm := c.x1_mul_xm1_mul_x1 hs
    have h1 : c.k (Units.mk0 s hs) * c.m * c.x6 1 * (c.k (Units.mk0 s hs) * c.m)⁻¹ ∈ P' := by
      have := conj_mem_conjSub (c.k (Units.mk0 s hs) * c.m) (c.x6_mem 1)
      rwa [c.conjSub_P_km] at this
    rw [← hkm] at h1
    have h2 : (c.x1 s)⁻¹ * (c.x1 s * c.xm1 s⁻¹ * c.x1 s * c.x6 1 *
        (c.x1 s * c.xm1 s⁻¹ * c.x1 s)⁻¹) * ((c.x1 s)⁻¹)⁻¹ ∈ P' := by
      have := conj_mem_conjSub (c.x1 s)⁻¹ h1
      rwa [conjSub_of_forall_commute fun x hx =>
        ((commuting_shortRoot_mid S.hyp S.hP'.2.1 _ (c.x1_mem s) x hx).inv_left)] at this
    convert h2 using 1
    rw [hy]
    group
  have hmy : c.m * y * c.m⁻¹ ∈ M R A :=
    conj_mem_M_of_mem_normalizer hR c.m_mem_normalizer hyM
  have hw : c.x1 s⁻¹ * (c.m * y * c.m⁻¹) * (c.x1 s⁻¹)⁻¹ ∈ P := by
    have e : c.x1 s⁻¹ = c.m * c.xm1 s⁻¹ * c.m⁻¹ := by
      rw [← c.m_conj_x1, c.m_inv]
      simp only [← mul_assoc, c.m_mul_self, one_mul]
      rw [mul_assoc, c.m_mul_self, mul_one]
    rw [e, show c.m * c.xm1 s⁻¹ * c.m⁻¹ * (c.m * y * c.m⁻¹) * (c.m * c.xm1 s⁻¹ * c.m⁻¹)⁻¹ =
      c.m * (c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹) * c.m⁻¹ by group]
    exact c.conj_m_mem c.conjSub_P'_m hz
  have hwM : c.x1 s⁻¹ * (c.m * y * c.m⁻¹) * (c.x1 s⁻¹)⁻¹ ∈ M R A := S.P_le_M hw
  have hU5 := S.proj_conj_U5 (c.x1_mem s⁻¹) ⟨_, hmy⟩ hwM
  rw [show (⟨_, hwM⟩ : ↥(M R A)) = ⟨_, S.P_le_M hw⟩ from rfl, S.proj_P hw] at hU5
  obtain ⟨hm1, hm2⟩ := c.proj_m_conj ⟨y, hyM⟩ hmy
  rw [hm1, hm2] at hU5
  have hpy : S.proj ⟨y, hyM⟩ = S.proj ⟨_, c.comm1_mem s⟩ * S.proj ⟨_, S.P_le_M (c.x6_mem 1)⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hyc
  rw [hpy, S.proj_P (c.x6_mem 1)] at hU5
  simp only [Prod.snd_mul, Prod.fst_mul, mul_one, OneMemClass.coe_one] at hU5
  change 1 = cxy S (c.x1 s⁻¹) (c.m * c.n2 s * c.m⁻¹) * (c.m * c.n3 s * c.m⁻¹) at hU5
  have hm6 : c.m * c.n2 s * c.m⁻¹ = c.x6 (τ⁻¹ * c.N s) := by
    have h := hτ (τ⁻¹ * c.N s)
    rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul, c.x2_N] at h
    rw [← h, c.m_inv]
    simp only [← mul_assoc, c.m_mul_self, one_mul]
    rw [mul_assoc, c.m_mul_self, mul_one]
  rw [hm6, ← c.x3_sharp, c.m_conj_x3, ← c5, he, ← x5, ← c.x5_add, ← c.x5_zero] at hU5
  have := c.x5_injective hU5
  rw [eq_comm, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
  exact this.symm

end Weyl

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
