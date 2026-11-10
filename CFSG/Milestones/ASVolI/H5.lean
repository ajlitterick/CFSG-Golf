module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HSL3Pair
public import CFSG.Quasithin.H13.VolIH5
public import CFSG.Quasithin.MS93.ML3Syl
public import CFSG.Foundations.Catalog
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.MS93.ML3Ext2
public import CFSG.Quasithin.MS93.ML3Gen

public section

open scoped commutatorElement

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

abbrev V3 : Type := Fin 3 → ZMod 2


theorem inv_mulVec_mulVec (g : GL (Fin 3) (ZMod 2)) (v : V3) :
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


@[expose] def IsLine (r : Submodule (ZMod 2) V3) : Prop := Module.finrank (ZMod 2) r = 2


@[expose] def Lpt (p : V3) : Subgroup (GL (Fin 3) (ZMod 2)) := glFix {p}

@[expose] def Lln (l : Submodule (ZMod 2) V3) : Subgroup (GL (Fin 3) (ZMod 2)) :=
  glStab (l : Set V3)

structure HypH5 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3) : Prop where
  sylow : IsSylowIn 2 T ⊤
  p_ne : p ≠ 0
  p_fix : ∀ g ∈ T, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p
  l_line : IsLine l
  l_inv : ∀ g ∈ T, ∀ v ∈ l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l

@[expose] def modNat : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative V3) := natHom 3 (ZMod 2)

@[expose] def modDual : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative V3) :=
  (natHom 3 (ZMod 2)).comp CFSG.Quasithin.H.SL3Pair.dualHom

@[expose] def modTriv : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (ZMod 2)) := 1


end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH


section HBridge55
open CFSG.Quasithin.MS93 Matrix

set_option synthInstance.maxHeartbeats 400000
private abbrev e1 : Fin 3 → ZMod 2 := ![1, 0, 0]

private def line0 : Submodule (ZMod 2) (Fin 3 → ZMod 2) :=
  LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3))

private theorem mem_line0 {v : Fin 3 → ZMod 2} : v ∈ line0 ↔ v 2 = 0 := by
  simp [line0]

private theorem toGL_surjective' :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* GL (Fin 3) (ZMod 2)) := by
  intro g
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    have hne : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
    revert hne
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
    revert d
    decide
  exact ⟨⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩, Units.ext rfl⟩

private noncomputable def slGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, toGL_surjective'⟩

private theorem slGL_coe (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

private noncomputable def B0 : Subgroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.MS93.sStar.map slGL.toMonoidHom

private theorem mem_B0 (x : GL (Fin 3) (ZMod 2)) :
    x ∈ B0 ↔ ∃ a b c : ZMod 2,
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![1, a, b; 0, 1, c; 0, 0, 1] := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hy
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, hx⟩
    refine ⟨uniTri a b c, mem_sStar_iff.mpr ⟨a, b, c, rfl⟩, ?_⟩
    apply Units.ext
    exact hx.symm

private theorem sylow_smul_mem {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g x : G} :
    x ∈ (g • P : Sylow p G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  show x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

private theorem sylow_conj (T : Subgroup (GL (Fin 3) (ZMod 2))) (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) :
    ∃ c : GL (Fin 3) (ZMod 2), ∀ x : GL (Fin 3) (ZMod 2), x ∈ T ↔ c⁻¹ * x * c ∈ B0 := by
  classical
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  set Ts : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := T.comap slGL.toMonoidHom
    with hTs
  have hmap : Ts.map slGL.toMonoidHom = T :=
    Subgroup.map_comap_eq_self_of_surjective slGL.surjective T
  have hTsP : IsPGroup 2 Ts := by
    have h1 : IsPGroup 2 (Ts.map slGL.toMonoidHom) := by rw [hmap]; exact hT
    exact h1.of_injective (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).toMonoidHom
      (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).injective
  have hTsi : ¬ 2 ∣ Ts.index := by
    rw [hTs, Subgroup.index_comap_of_surjective T (f := slGL.toMonoidHom) slGL.surjective]
    exact hTi
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := hTsP.toSylow hTsi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) P' Q
  refine ⟨slGL g, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := slGL.surjective x
  have hQ : y ∈ Q ↔ y ∈ Ts := Iff.rfl
  have hA : slGL y ∈ T ↔ y ∈ Ts := by
    rw [hTs, Subgroup.mem_comap]
    rfl
  have hB : slGL y ∈ T ↔ g⁻¹ * y * g ∈ CFSG.Quasithin.MS93.sStar := by
    rw [hA, ← hQ, ← hg, sylow_smul_mem]
    rfl
  rw [hB, B0, Subgroup.mem_map_equiv]
  simp [map_inv, map_mul]

private theorem fix_decide : ∀ v : Fin 3 → ZMod 2,
    (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    v = 0 ∨ v = e1 := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem line_decide : ∀ F : Finset (Fin 3 → ZMod 2), (0 : Fin 3 → ZMod 2) ∈ F →
    (∀ a ∈ F, ∀ b ∈ F, a + b ∈ F) → F.card = 4 →
    (∀ v ∈ F, (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    (∀ v ∈ F, (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    F = Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
  decide +kernel

private theorem natCard_submod_field {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V]
    {inst : Module K V} [Finite V] (W : Submodule K V) :
    Nat.card W = Fintype.card K ^ Module.finrank K W := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := W), Nat.card_eq_fintype_card]

private theorem natCard_of_finrank_two (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (h : Module.finrank (ZMod 2) l = 2) : Nat.card l = 4 := by
  have hc : Nat.card l = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) l := natCard_submod_field l
  rw [hc, h, ZMod.card]
  norm_num

private theorem line_unique (P : (Fin 3 → ZMod 2) → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hcard : (Finset.univ.filter P).card = 4)
    (ht : ∀ v, P v → P ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v))
    (hu : ∀ v, P v → P ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)) :
    ∀ v, P v ↔ v 2 = 0 := by
  have key := line_decide (Finset.univ.filter P)
    (by simpa using h0)
    (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
      exact hadd a b ha hb)
    hcard
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ht v hv)
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hu v hv)
  intro v
  have hv : v ∈ Finset.univ.filter P ↔ v ∈ Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
    rw [key]
  simpa using hv


private theorem mem_Lpt (k : GL (Fin 3) (ZMod 2)) (p : Fin 3 → ZMod 2) :
    k ∈ Lpt p ↔ ∀ v ∈ ({p} : Set (Fin 3 → ZMod 2)), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v :=
  Iff.rfl

private theorem mem_Lln (k : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2)) :
    k ∈ Lln l ↔ ∀ v ∈ (l : Set (Fin 3 → ZMod 2)),
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ∧
        ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l :=
  Iff.rfl

private theorem mulVec_gl (g h : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem mem_Lp_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Lp ↔ slGL g ∈ Lpt e1 := by
  rw [CFSG.Quasithin.H6.Lp, MulAction.mem_stabilizer_iff, mem_Lpt]
  have hsm : ∀ v : Fin 3 → ZMod 2, g • v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v :=
    fun v => rfl
  constructor
  · intro h v hv
    rw [Set.mem_singleton_iff.mp hv, slGL_coe, ← hsm]
    exact h
  · intro h
    have h' := h e1 (Set.mem_singleton _)
    rw [slGL_coe, ← hsm] at h'
    exact h'

private theorem mem_Ll_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Ll ↔ slGL g ∈ Lln line0 := by
  have hL : g ∈ CFSG.Quasithin.H6.Ll ↔ CFSG.Quasithin.H6.IsLl g := Iff.rfl
  rw [hL, mem_Lln]
  have hg' : ∀ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), CFSG.Quasithin.H6.IsLl k →
      ∀ w : Fin 3 → ZMod 2, w 2 = 0 → (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w 2 = 0 := by
    rintro k ⟨k20, k21⟩ w hw
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, k20, k21, hw]
  constructor
  · rintro ⟨h20, h21⟩ v hv
    have hv' : v ∈ line0 := hv
    rw [mem_line0] at hv'
    refine ⟨?_, ?_⟩
    · rw [slGL_coe, mem_line0]
      exact hg' g ⟨h20, h21⟩ v hv'
    · rw [← map_inv, slGL_coe, mem_line0]
      exact hg' g⁻¹ (CFSG.Quasithin.H6.isLl_inv g ⟨h20, h21⟩) v hv'
  · intro h
    have h0 := (h (fun i => if i = 0 then 1 else 0) (by simp [mem_line0])).1
    have h1 := (h (fun i => if i = 1 then 1 else 0) (by simp [mem_line0])).1
    rw [slGL_coe, mem_line0] at h0 h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    exact ⟨h0, h1⟩

private theorem mem_Lln_conj (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hl : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (k : GL (Fin 3) (ZMod 2)) : k ∈ Lln line0 ↔ c * k * c⁻¹ ∈ Lln l := by
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : ∀ (k' : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2),
      ((c * k' * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((k' : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) := by
    intro k' w; rw [mulVec_gl, mulVec_gl, hcinv]
  have hinvconj : ∀ k' : GL (Fin 3) (ZMod 2), (c * k' * c⁻¹ : GL (Fin 3) (ZMod 2))⁻¹ = c * k'⁻¹ * c⁻¹ :=
    fun k' => by group
  rw [mem_Lln, mem_Lln]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ : ∃ w, v = (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w :=
      ⟨_, (hcc v).symm⟩
    have hw : w 2 = 0 := (hl w).1 hv
    obtain ⟨hk1, hk2⟩ := h w ((mem_line0).2 hw)
    rw [hconj]
    rw [hinvconj, hconj]
    exact ⟨(hl _).2 ((mem_line0).1 hk1), (hl _).2 ((mem_line0).1 hk2)⟩
  · intro h w hw
    have hwl : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l := (hl w).2 ((mem_line0).1 hw)
    obtain ⟨h1, h2⟩ := h _ hwl
    rw [hconj] at h1
    rw [hinvconj, hconj] at h2
    exact ⟨(mem_line0).2 ((hl _).1 h1), (mem_line0).2 ((hl _).1 h2)⟩

private theorem fixB0 (v : Fin 3 → ZMod 2)
    (hv : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) : v = 0 ∨ v = e1 := by
  have tmem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
  have umem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩
  exact fix_decide v (hv _ tmem) (hv _ umem)

private theorem tG_mem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
private theorem uG_mem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩

private theorem tG_mat : ((slGL (uniTri 1 0 0) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

private theorem uG_mat : ((slGL (uniTri 0 0 1) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl


end HBridge55

section H54
open CFSG.Quasithin.MS93 Matrix


end H54

section H5Lin

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 800000


end H5Lin


section H52pc


end H52pc

section H52tr


end H52tr


section H52asm


end H52asm


end CFSG.ASVolI
