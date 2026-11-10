module

public import CFSG.Monster.Griess.TrilinearData
public import CFSG.Monster.Griess.Parity

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix Module

theorem eq_of_bform_eq {x y : SpaceB} (h : ∀ w, bform x w = bform y w) : x = y := by
  by_contra hne
  have hz : x - y ≠ 0 := sub_ne_zero.2 hne
  have h0 : bform (x - y) (x - y) = 0 := by
    rw [map_sub bform x y, LinearMap.sub_apply, h, sub_self]
  exact lt_irrefl _ (h0 ▸ bform_self_pos hz)

theorem bform_gmul (u v w : SpaceB) : bform (gmul u v) w = T u v w := rfl


theorem IsDyM.add {m n : Type*} {M N : Matrix m n ℚ} (hM : IsDyM M) (hN : IsDyM N) :
    IsDyM (M + N) := fun i j => add_mem (hM i j) (hN i j)

theorem IsDyM.sub {m n : Type*} {M N : Matrix m n ℚ} (hM : IsDyM M) (hN : IsDyM N) :
    IsDyM (M - N) := fun i j => sub_mem (hM i j) (hN i j)

theorem IsDyM.smul {m n : Type*} {M : Matrix m n ℚ} (hM : IsDyM M) {c : ℚ} (hc : c ∈ dyadic) :
    IsDyM (c • M) := fun i j => mul_mem hc (hM i j)

theorem isDyM_sum {m n ι : Type*} (s : Finset ι) {M : ι → Matrix m n ℚ}
    (h : ∀ k ∈ s, IsDyM (M k)) : IsDyM (∑ k ∈ s, M k) := fun i j => by
  rw [Matrix.sum_apply]
  exact sum_mem fun k hk => h k hk i j

theorem isDyM_one : IsDyM (1 : Matrix (Fin 24) (Fin 24) ℚ) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem Umat_isDyM (c : ShortIdx) : IsDyM (Umat c) := fun i j =>
  mul_mem (uQ_mem_dyadic c i) (uQ_mem_dyadic c j)

theorem two_mem_dyadic' : (2 : ℚ) ∈ dyadic := natCast_mem dyadic 2

theorem inv_two_mem_dyadic' : (2 : ℚ)⁻¹ ∈ dyadic := by
  have h := inv_two_pow_mem_dyadic 1
  rwa [pow_one] at h

theorem gmulA_isDyM {u v : SpaceB} (hu : IsDyadicVec u) (hv : IsDyadicVec v) :
    IsDyM (gmulA u v) := by
  have hAu : IsDyM (Am u) := hu.1
  have hAv : IsDyM (Am v) := hv.1
  have hNu : IsDyM (Nm u) := hu.2.2
  have hNv : IsDyM (Nm v) := hv.2.2
  unfold gmulA
  refine (((IsDyM.smul ((hAu.mul hAv).add (hAv.mul hAu)) two_mem_dyadic').add
    (IsDyM.smul (isDyM_sum _ fun c _ => (Umat_isDyM c).smul
      (mul_mem (hu.2.1 c) (hv.2.1 c))) inv_eight_mem_dyadic)).add
    (isDyM_one.smul (div_eight_mem_dyadic (hNu.transpose.mul hNv).trace_mem))).add
    (IsDyM.smul ((hNu.transpose.mul hNv).add (hNv.transpose.mul hNu)) inv_two_mem_dyadic')

theorem gmulX_mem_dyadic {u v : SpaceB} (hu : IsDyadicVec u) (hv : IsDyadicVec v) (c : ShortIdx) :
    gmulX u v c ∈ dyadic := by
  have hAu : IsDyM (Am u) := hu.1
  have hAv : IsDyM (Am v) := hv.1
  have hNu : IsDyM (Nm u) := hu.2.2
  have hNv : IsDyM (Nm v) := hv.2.2
  have hM : IsDyM ((Nm u)ᵀ * Rmat c * Nm v) := (hNu.transpose.mul (Rmat_isDyM c)).mul hNv
  unfold gmulX
  refine add_mem (add_mem (div_eight_mem_dyadic (add_mem (mul_mem (hv.2.1 c)
    (qf_mem_dyadic c hAu)) (mul_mem (hu.2.1 c) (qf_mem_dyadic c hAv))))
    (sum_mem fun d _ => sum_mem fun e _ => mul_mem (mul_mem (hu.2.1 d) (hv.2.1 e))
      (tau_mem_dyadic d e c)))
    (div_eight_mem_dyadic (sub_mem hM.trace_mem (div_four_mem_dyadic (qf_mem_dyadic c hM))))

theorem gmulWHalf_isDyM {u v : SpaceB} (hu : IsDyadicVec u) (hv : IsDyadicVec v) :
    IsDyM (gmulWHalf u v) := by
  have hAu : IsDyM (Am u) := hu.1
  have hNv : IsDyM (Nm v) := hv.2.2
  unfold gmulWHalf
  refine ((hNv.smul (div_eight_mem_dyadic hAu.trace_mem)).add (hNv.mul hAu)).add
    (IsDyM.smul (isDyM_sum _ fun c _ => IsDyM.smul (((Rmat_isDyM c).mul hNv).sub
      ((((Rmat_isDyM c).mul hNv).mul (Umat_isDyM c)).smul inv_four_mem_dyadic)) (hu.2.1 c))
      inv_eight_mem_dyadic)

theorem isDyadicVec_gmul {u v : SpaceB} (hu : IsDyadicVec u) (hv : IsDyadicVec v) :
    IsDyadicVec (gmul u v) :=
  ⟨gmulA_isDyM hu hv, gmulX_mem_dyadic hu hv,
    ((gmulWHalf_isDyM hu hv).add (gmulWHalf_isDyM hv hu) : IsDyM (gmulWHalf u v + gmulWHalf v u))⟩

theorem gmul_mem_BR {u v : SpaceB} (hu : u ∈ BR) (hv : v ∈ BR) : gmul u v ∈ BR :=
  mem_BR_iff.2 (isDyadicVec_gmul (mem_BR_iff.1 hu) (mem_BR_iff.1 hv))


theorem uQ_dotProduct_self (c : ShortIdx) : uQ c ⬝ᵥ uQ c = 32 := by
  have h : normSq (uvec c) = 32 := (mem_minVecs_iff.1 (uvec_mem c)).2
  unfold uQ dotProduct
  have h' : ((∑ i, uvec c i * uvec c i : ℤ) : ℚ) = 32 := by
    rw [show (∑ i, uvec c i * uvec c i) = normSq (uvec c) from rfl, h]
    norm_num
  push_cast at h'
  exact h'


end CFSG.Monster.Griess
