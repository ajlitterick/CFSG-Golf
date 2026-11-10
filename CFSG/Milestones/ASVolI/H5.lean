module

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

abbrev PermV : Type := Multiplicative (V3 → ZMod 2)

theorem inv_mulVec_mulVec (g : GL (Fin 3) (ZMod 2)) (v : V3) :
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin 3) (ZMod 2)) (v : V3) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def gl3Act : GL (Fin 3) (ZMod 2) →* MulAut PermV where
  toFun g :=
    { toFun := fun f => Multiplicative.ofAdd fun v =>
        Multiplicative.toAdd f (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      invFun := fun f => Multiplicative.ofAdd fun v =>
        Multiplicative.toAdd f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext v
        simp
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext v
        simp
      map_mul' := fun f f' => by
        apply Multiplicative.toAdd.injective
        funext v
        simp }
  map_one' := by
    ext f v
    simp
  map_mul' g h := by
    ext f v
    simp [mul_inv_rev, Matrix.mulVec_mulVec]

@[expose] def U0sub : Subgroup PermV :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) 0))

@[expose] def Ucore : Subgroup PermV :=
  U0sub ⊓ AddSubgroup.toSubgroup (AddMonoidHom.ker (∑ v : V3, Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) v))

open scoped Classical in
@[expose] noncomputable def omegaVec : PermV :=
  Multiplicative.ofAdd fun v => if v = 0 then 0 else 1

open scoped Classical in
@[expose] noncomputable def uOf (S : Set V3) : PermV :=
  Multiplicative.ofAdd fun v => if v ≠ 0 ∧ v ∉ S then 1 else 0

@[expose] def IsLine (r : Submodule (ZMod 2) V3) : Prop := Module.finrank (ZMod 2) r = 2

@[expose] def O1set : Set PermV := {x | ∃ q : V3, q ≠ 0 ∧ x = uOf {q}}

@[expose] def O2set : Set PermV :=
  {x | ∃ r : Submodule (ZMod 2) V3, IsLine r ∧ x = uOf (r : Set V3)}

@[expose] def O3set : Set PermV :=
  {x | x ∈ U0sub ∧ Nat.card {v : V3 // Multiplicative.toAdd x v ≠ 0} = 2}

@[expose] def O4set : Set PermV :=
  {x | ∃ v₁ v₂ v₃ : V3, LinearIndependent (ZMod 2) ![v₁, v₂, v₃] ∧ x = uOf {v₁, v₂, v₃}}

@[expose] def Oset : Fin 4 → Set PermV
  | 0 => O1set
  | 1 => O2set
  | 2 => O3set
  | 3 => O4set

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

@[expose] def IsoSec {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (U Z : Subgroup X) (A : Type*) [CommGroup A] (act : G →* MulAut A) : Prop :=
  Z ≤ U ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) ∧
  ∃ β : ↥U →* A, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : X) ∈ Z) ∧
    ∀ (g : G) (u u' : ↥U), (u' : X) = ρ g u → β u' = act g (β u)

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_5_1 : Prop :=
  Ucore ⊔ Subgroup.zpowers omegaVec = U0sub ∧ Ucore ⊓ Subgroup.zpowers omegaVec = ⊥ ∧
  (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ U0sub, gl3Act g u ∈ U0sub) ∧
  (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ Ucore, gl3Act g u ∈ Ucore) ∧
  (∀ g : GL (Fin 3) (ZMod 2), gl3Act g omegaVec = omegaVec)


@[expose] def H_5_2 : Prop :=
  (∀ r s t : Submodule (ZMod 2) V3, IsLine r → IsLine s → IsLine t → r ≠ s → t ≠ r → t ≠ s →
    ∀ q : V3, q ≠ 0 → q ∈ r → q ∈ s → q ∈ t →
      uOf (r : Set V3) * uOf (s : Set V3) = uOf (t : Set V3)) ∧
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    (Ucore ⊓ fixV (T.map gl3Act) = Subgroup.closure {uOf {p}, uOf (l : Set V3)} ∧
      rk ↥(Ucore ⊓ fixV (T.map gl3Act)) = 2) ∧
    (rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 ∧
      rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3) ∧
    (rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 ∧
      rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3) ∧
    (Ucore ⊓ fixV ((Lpt p).map gl3Act) = Subgroup.zpowers (uOf {p}) ∧
      Ucore ⊓ fixV ((Lln l).map gl3Act) = Subgroup.zpowers (uOf (l : Set V3))) ∧
    (∃ β : PermV → PermV → ZMod 2,
      (∀ u ∈ Ucore, ∀ u' ∈ Ucore, ∀ w ∈ Ucore, β (u * u') w = β u w + β u' w) ∧
      (∀ u ∈ Ucore, ∀ w ∈ Ucore, ∀ w' ∈ Ucore, β u (w * w') = β u w + β u w') ∧
      (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ Ucore, ∀ w ∈ Ucore, β (gl3Act g u) (gl3Act g w) = β u w) ∧
      (∀ u ∈ Ucore, u ≠ 1 → ∃ w ∈ Ucore, β u w ≠ 0)) ∧
    (∀ (Y : Subgroup (GL (Fin 3) (ZMod 2))) (q : V3), IsSylowIn 3 Y (Lln l) → q ≠ 0 →
      (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q) →
      (∀ v : V3, (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = q) →
      Ucore ⊓ fixV (Y.map gl3Act) = Subgroup.closure {uOf (l : Set V3), uOf {q}})

@[expose] def H_5_3 : Prop :=
  ∃ Wg : Subgroup PermV, (Wg : Set PermV) = {1} ∪ O2set ∧
    (Wg ≤ Ucore ∧ (∀ g : GL (Fin 3) (ZMod 2), ∀ w ∈ Wg, gl3Act g w ∈ Wg) ∧
      IsoSec gl3Act Wg ⊥ (Multiplicative V3) modDual) ∧
    IsoSec gl3Act Ucore Wg (Multiplicative V3) modNat ∧
    ((∀ i : Fin 4, ∀ x ∈ Oset i, ∀ g : GL (Fin 3) (ZMod 2), gl3Act g x ∈ Oset i) ∧
      (∀ i : Fin 4, ∀ x ∈ Oset i, ∀ y ∈ Oset i, ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y) ∧
      (∀ i : Fin 4, ∀ x ∈ Oset i, x ∈ Ucore ∧ x ≠ 1) ∧
      (∀ x ∈ Ucore, x ≠ 1 → ∃ i : Fin 4, x ∈ Oset i) ∧
      (∀ i j : Fin 4, i ≠ j → Disjoint (Oset i) (Oset j))) ∧
    (Set.ncard O1set = 7 ∧ Set.ncard O2set = 7 ∧ Set.ncard O3set = 21 ∧ Set.ncard O4set = 28) ∧
    ((∀ A B : Subgroup PermV, A ≤ Ucore → B ≤ Ucore → (∀ g : GL (Fin 3) (ZMod 2), ∀ a ∈ A, gl3Act g a ∈ A) →
        (∀ g : GL (Fin 3) (ZMod 2), ∀ b ∈ B, gl3Act g b ∈ B) → A ⊔ B = Ucore → A ⊓ B = ⊥ →
        A = ⊥ ∨ B = ⊥) ∧
      Wg = ⨆ (N : Subgroup PermV) (_ : N ≤ Ucore)
        (_ : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
        (_ : IsIrredOn gl3Act.range N), N)

@[expose] def H_5_4 : Prop :=
  (∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    ¬ (Ucore ⊓ fixV ((Lpt p).map gl3Act) ≤
        commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lln l).map gl3Act)) ∧
    (Ucore ⊓ fixV ((Lln l).map gl3Act) ≤ commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act))) ∧
  (∀ a ∈ O1set, ∀ b ∈ O1set, ∀ c ∈ O1set, a ≠ b → a ≠ c → b ≠ c → a * b * c ≠ 1)

@[expose] def H_5_5 : Prop :=
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
  ∀ (A : Type) [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) →
  ∀ act : GL (Fin 3) (ZMod 2) →* MulAut A, ∀ x : A, x ≠ 1 →
    (∀ g ∈ Lpt p, act g x = x) →
    Subgroup.closure (Set.range fun g : GL (Fin 3) (ZMod 2) => act g x) = ⊤ →
    rk ↥(Subgroup.closure ((fun g : GL (Fin 3) (ZMod 2) => act g x) '' (Lln l : Set _))) = 2 →
      ∃ e : A ≃* Multiplicative V3, ∀ (g : GL (Fin 3) (ZMod 2)) (a : A), e (act g a) = modNat g (e a)

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

private theorem card_of_rk_two {A : Type} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 2 = 1)
    (W : Subgroup A) (h : CFSG.Quasithin.rk ↥W = 2) : Nat.card W = 4 := by
  have hP : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using hA (w : A))⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  unfold CFSG.Quasithin.rk at h
  rw [hn, padicValNat.prime_pow] at h
  rw [hn, h]
  rfl

private theorem natCard_toAddSubgroup {A : Type} [CommGroup A] (W : Subgroup A) :
    Nat.card ↥(W.toAddSubgroup) = Nat.card ↥W :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun a => Iff.rfl))

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


private theorem conj_data54 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) :
    ∃ c : GL (Fin 3) (ZMod 2), (∀ y ∈ B0, c * y * c⁻¹ ∈ T) ∧
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p ∧
      (∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) := by
  obtain ⟨-, hTp, hTi⟩ := hyp.sylow
  rw [Subgroup.relIndex_top_right] at hTi
  obtain ⟨c, hc⟩ := sylow_conj T hTp hTi
  have hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T := by
    intro y hy
    refine (hc _).2 ?_
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  have hcinv : ∀ w : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : V3,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = q := ⟨_, rfl⟩
  have hpq : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = p := by rw [← hq, hcc]
  have hfixq : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q := by
    intro y hy
    have h1 := hyp.p_fix _ (hconjT y hy)
    rw [mulVec_gl, mulVec_gl, hq] at h1
    calc (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q
        = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q)) :=
          (hcinv _).symm
      _ = q := by rw [h1, hq]
  have hq0 : q = e1 := by
    rcases fixB0 q hfixq with h | h
    · exfalso
      apply hyp.p_ne
      rw [← hpq, h, Matrix.mulVec_zero]
    · exact h
  have hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by rw [← hq0, hpq]
  have hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
    classical
    have hfr : Module.finrank (ZMod 2) l = 2 := hyp.l_line
    have hcardl : Nat.card l = 4 := natCard_of_finrank_two l hfr
    refine line_unique (fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [Matrix.mulVec_add]
      exact l.add_mem ha hb
    · let e' : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) :=
        { toFun := fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
          invFun := fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w
          left_inv := hcinv
          right_inv := hcc }
      have h1 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
            (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)).card =
          (Finset.univ.filter (fun w : Fin 3 → ZMod 2 => w ∈ l)).card :=
        Finset.card_equiv e' (fun i => by simp [e'])
      rw [h1, ← Fintype.card_subtype]
      have := hcardl
      rw [Nat.card_eq_fintype_card] at this
      exact this
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ tG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← tG_mat]
      exact h
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ uG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← uG_mat]
      exact h
  exact ⟨c, hconjT, hpc, hline⟩


end H54

section H5Lin

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 800000


private theorem sum_V3 {M : Type*} [AddCommMonoid M] (g : V3 → M) :
    ∑ v : V3, g v = g ![0, 0, 0] + g ![1, 0, 0] + g ![0, 1, 0] + g ![1, 1, 0] +
      g ![0, 0, 1] + g ![1, 0, 1] + g ![0, 1, 1] + g ![1, 1, 1] := by
  have h : (Finset.univ : Finset V3) = {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
      ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel


private def D3 (a b c : V3) : ZMod 2 :=
  a 0 * b 1 * c 2 - a 0 * c 1 * b 2 - b 0 * a 1 * c 2 + b 0 * c 1 * a 2 +
    c 0 * a 1 * b 2 - c 0 * b 1 * a 2


private def F4 : Finset (Finset V3) :=
  ((Finset.univ.erase (0 : V3)).powersetCard 3).filter (fun s =>
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → D3 x y z ≠ 0)


end H5Lin


section H52pc


end H52pc

section H52tr


end H52tr


section H52asm


end H52asm


end CFSG.ASVolI
