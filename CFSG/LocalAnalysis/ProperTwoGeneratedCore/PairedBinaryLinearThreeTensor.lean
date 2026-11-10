module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ProperTwoGeneratedCore.PairedTensor

open Matrix
open BinaryThreeSpace (Mat3 traceZero)

abbrev S : Type := GL (Fin 3) (ZMod 2)

@[expose] def invTranspose (g : S) : S :=
  ⟨((g⁻¹ : S) : Mat3)ᵀ, (g : Mat3)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

theorem invTranspose_invTranspose (g : S) : invTranspose (invTranspose g) = g := by
  apply Units.ext
  change (((invTranspose g)⁻¹ : S) : Mat3)ᵀ = g
  change ((g : Mat3)ᵀ)ᵀ = g
  rw [transpose_transpose]

theorem invTranspose_mul (g h : S) : invTranspose (g * h) = invTranspose g * invTranspose h := by
  apply Units.ext
  change (((g * h)⁻¹ : S) : Mat3)ᵀ = ((g⁻¹ : S) : Mat3)ᵀ * ((h⁻¹ : S) : Mat3)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]

@[expose] def tau : S ≃* S where
  toFun := invTranspose
  invFun := invTranspose
  left_inv := invTranspose_invTranspose
  right_inv := invTranspose_invTranspose
  map_mul' := invTranspose_mul

theorem tau_apply_val (g : S) : ((tau g : S) : Mat3) = ((g⁻¹ : S) : Mat3)ᵀ := rfl

theorem tau_tau (g : S) : tau (tau g) = g := invTranspose_invTranspose g


abbrev K : Type := S × S

@[ext] structure QFull : Type where
  e₁ : ZMod 2
  e₂ : ZMod 2
  σ : ZMod 2
deriving DecidableEq, Fintype

namespace QFull

@[expose] def mul (q r : QFull) : QFull :=
  ⟨q.e₁ + (if q.σ = 0 then r.e₁ else r.e₂), q.e₂ + (if q.σ = 0 then r.e₂ else r.e₁), q.σ + r.σ⟩

@[expose] def inv (q : QFull) : QFull := if q.σ = 0 then q else ⟨q.e₂, q.e₁, q.σ⟩

instance : Mul QFull := ⟨mul⟩
instance : One QFull := ⟨⟨0, 0, 0⟩⟩
instance : Inv QFull := ⟨inv⟩

theorem mul_def (q r : QFull) : q * r = mul q r := rfl
theorem one_def : (1 : QFull) = ⟨0, 0, 0⟩ := rfl

instance : Group QFull :=
  Group.ofLeftAxioms (by decide) (by decide) (by decide)

@[expose] def a : QFull := ⟨1, 0, 0⟩
@[expose] def b : QFull := ⟨0, 1, 0⟩
@[expose] def s : QFull := ⟨0, 0, 1⟩


theorem eq_word : ∀ q : QFull, q = (if q.e₁ = 0 then 1 else a) * (if q.e₂ = 0 then 1 else b) *
    (if q.σ = 0 then 1 else s) := by
  decide

theorem card_eq : Nat.card QFull = 8 := by
  rw [Nat.card_eq_fintype_card]
  rfl


section Lift

variable {H : Type*} [Monoid H] (x y z : H)

@[expose] def word (q : QFull) : H :=
  (if q.e₁ = 0 then 1 else x) * (if q.e₂ = 0 then 1 else y) * (if q.σ = 0 then 1 else z)

variable {x y z}

private theorem zmod2_forall {P : ZMod 2 → Prop} : (∀ t, P t) ↔ P 0 ∧ P 1 :=
  ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ t => by fin_cases t; exacts [h0, h1]⟩

theorem word_mul (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) (hxy : x * y = y * x)
    (hzx : z * x = y * z) (hzy : z * y = x * z) (q r : QFull) :
    word x y z (q * r) = word x y z q * word x y z r := by
  have hzx' : ∀ w : H, z * (x * w) = y * (z * w) := fun w => by rw [← mul_assoc, hzx, mul_assoc]
  have hzy' : ∀ w : H, z * (y * w) = x * (z * w) := fun w => by rw [← mul_assoc, hzy, mul_assoc]
  have hyx' : ∀ w : H, y * (x * w) = x * (y * w) := fun w => by
    rw [← mul_assoc, ← hxy, mul_assoc]
  have hx' : ∀ w : H, x * (x * w) = w := fun w => by rw [← mul_assoc, hx, one_mul]
  have hy' : ∀ w : H, y * (y * w) = w := fun w => by rw [← mul_assoc, hy, one_mul]
  have hyx : y * x = x * y := hxy.symm
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  obtain ⟨e₁, e₂, σ⟩ := q
  obtain ⟨f₁, f₂, ρ⟩ := r
  simp only [word, mul_def, mul]
  revert e₁ e₂ σ f₁ f₂ ρ
  simp only [zmod2_forall]
  simp [h11, mul_assoc, hx', hy', hzx', hzy', hyx', hx, hy, hz, hyx, hzx, hzy]

@[expose] def lift (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) (hxy : x * y = y * x)
    (hzx : z * x = y * z) (hzy : z * y = x * z) : QFull →* H where
  toFun := word x y z
  map_one' := by simp [word, one_def]
  map_mul' := word_mul hx hy hz hxy hzx hzy

end Lift

end QFull

@[expose] def autA : MulAut K := MulEquiv.prodCongr tau (MulEquiv.refl S)

@[expose] def autB : MulAut K := MulEquiv.prodCongr (MulEquiv.refl S) tau

@[expose] def autS : MulAut K := MulEquiv.prodComm

@[expose] def qAct : QFull →* MulAut K :=
  QFull.lift (x := autA) (y := autB) (z := autS)
    (MulEquiv.ext fun k => Prod.ext (tau_tau k.1) rfl)
    (MulEquiv.ext fun k => Prod.ext rfl (tau_tau k.2)) (MulEquiv.ext fun _ => rfl)
    (MulEquiv.ext fun _ => rfl) (MulEquiv.ext fun _ => rfl) (MulEquiv.ext fun _ => rfl)

abbrev Efull : Type := K ⋊[qAct] QFull


abbrev N : Type := Fin 3 → ZMod 2

abbrev Nd : Type := Fin 3 → ZMod 2

abbrev A : Type := ↥traceZero

@[expose] def rightN (g : S) : N →ₗ[ZMod 2] N := Matrix.vecMulLinear (g : Mat3)

@[expose] def rightNd (g : S) : Nd →ₗ[ZMod 2] Nd := Matrix.vecMulLinear ((tau g : S) : Mat3)

theorem conj_mem_traceZero (g : S) {X : Mat3} (hX : X ∈ traceZero) :
    ((g⁻¹ : S) : Mat3) * X * (g : Mat3) ∈ traceZero := by
  rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_mul_cycle,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  exact hX

@[expose] def rightA (g : S) : A →ₗ[ZMod 2] A where
  toFun X := ⟨((g⁻¹ : S) : Mat3) * (X : Mat3) * (g : Mat3), conj_mem_traceZero g X.2⟩
  map_add' X Y := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' c X := Subtype.ext (by simp)

theorem rightN_mul (g h : S) : rightN (g * h) = rightN h * rightN g :=
  LinearMap.ext fun v => by simp [rightN, Matrix.vecMul_vecMul]

theorem rightNd_mul (g h : S) : rightNd (g * h) = rightNd h * rightNd g :=
  LinearMap.ext fun v => by simp [rightNd, map_mul, Matrix.vecMul_vecMul]

theorem rightA_mul (g h : S) : rightA (g * h) = rightA h * rightA g := by
  ext X : 2
  simp [rightA, Matrix.mul_assoc]

theorem rightN_one : rightN 1 = 1 :=
  LinearMap.ext fun v => by simp [rightN]

theorem rightNd_one : rightNd 1 = 1 :=
  LinearMap.ext fun v => by simp [rightNd]

theorem rightA_one : rightA 1 = 1 := by
  ext X : 2
  simp [rightA]

@[expose] def ofRight {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]
    (r : S → W →ₗ[ZMod 2] W) (h1 : r 1 = 1) (hmul : ∀ g h, r (g * h) = r h * r g) :
    Representation (ZMod 2) S W where
  toFun g := r g⁻¹
  map_one' := by rw [inv_one, h1]
  map_mul' g h := by rw [_root_.mul_inv_rev, hmul]

@[expose] def repN : Representation (ZMod 2) S N := ofRight rightN rightN_one rightN_mul

@[expose] def repNd : Representation (ZMod 2) S Nd := ofRight rightNd rightNd_one rightNd_mul

@[expose] def repA : Representation (ZMod 2) S A := ofRight rightA rightA_one rightA_mul

theorem repN_apply (g : S) (v : N) : repN g v = v ᵥ* ((g⁻¹ : S) : Mat3) := rfl

theorem repNd_apply (g : S) (f : Nd) : repNd g f = f ᵥ* ((tau g⁻¹ : S) : Mat3) := rfl

theorem repA_apply (g : S) (X : A) :
    (repA g X : Mat3) = (g : Mat3) * (X : Mat3) * ((g⁻¹ : S) : Mat3) := by
  change ((g⁻¹⁻¹ : S) : Mat3) * (X : Mat3) * ((g⁻¹ : S) : Mat3) = _
  rw [inv_inv]


theorem finrank_N : Module.finrank (ZMod 2) N = 3 := by simp

theorem finrank_Nd : Module.finrank (ZMod 2) Nd = 3 := by simp

theorem finrank_A : Module.finrank (ZMod 2) A = 8 := by
  rw [Module.finrank_eq_card_basis BinaryThreeSpace.conjBasis]
  rfl

theorem transpose_mem_traceZero {X : Mat3} (hX : X ∈ traceZero) : Xᵀ ∈ traceZero := by
  rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_transpose]
  exact hX

@[expose] def transposeA : A →ₗ[ZMod 2] A where
  toFun X := ⟨(X : Mat3)ᵀ, transpose_mem_traceZero X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev V : Type := ZMod 2 × N × Nd × A

@[expose] def rho : Representation (ZMod 2) S V where
  toFun g := LinearMap.prodMap 1 (LinearMap.prodMap (repN g) (LinearMap.prodMap (repNd g) (repA g)))
  map_one' := by simp only [map_one, LinearMap.prodMap_one]
  map_mul' g h := by simp only [map_mul, LinearMap.prodMap_mul, mul_one]

@[expose] def graphV : V →ₗ[ZMod 2] V where
  toFun x := (x.1, x.2.2.1, x.2.1, transposeA x.2.2.2)
  map_add' _ _ := rfl
  map_smul' c x := Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (transposeA.map_smul c x.2.2.2)))

theorem graphV_mul_graphV : graphV * graphV = 1 := by
  refine LinearMap.ext fun x => ?_
  change (x.1, x.2.1, x.2.2.1, transposeA (transposeA x.2.2.2)) = x
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subtype.ext ?_)))
  exact Matrix.transpose_transpose _

theorem tau_inv_val (g : S) : (((tau g)⁻¹ : S) : Mat3) = (g : Mat3)ᵀ := rfl

theorem graphV_mul_rho (g : S) : graphV * rho g = rho (tau g) * graphV := by
  refine LinearMap.ext fun x => ?_
  change (x.1, repNd g x.2.2.1, repN g x.2.1, transposeA (repA g x.2.2.2)) =
    (x.1, repN (tau g) x.2.2.1, repNd (tau g) x.2.1, repA (tau g) (transposeA x.2.2.2))
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_)))
  · change x.2.2.1 ᵥ* ((tau g⁻¹ : S) : Mat3) = x.2.2.1 ᵥ* (((tau g)⁻¹ : S) : Mat3)
    rw [map_inv]
  · change x.2.1 ᵥ* ((g⁻¹ : S) : Mat3) = x.2.1 ᵥ* ((tau (tau g)⁻¹ : S) : Mat3)
    rw [← map_inv, tau_tau]
  · change ((repA g x.2.2.2 : A) : Mat3)ᵀ = (repA (tau g) (transposeA x.2.2.2) : Mat3)
    rw [repA_apply, repA_apply, Matrix.transpose_mul, Matrix.transpose_mul, tau_apply_val,
      tau_inv_val, Matrix.mul_assoc]
    rfl

abbrev T : Type := TensorProduct (ZMod 2) V V

@[expose] def repK : K →* Module.End (ZMod 2) T where
  toFun k := TensorProduct.map (rho k.1) (rho k.2)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_one]
  map_mul' k l := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, TensorProduct.map_mul]

@[expose] def flipT : Module.End (ZMod 2) T := (TensorProduct.comm (ZMod 2) V V).toLinearMap


@[expose] def repQ : QFull →* Module.End (ZMod 2) T :=
  QFull.lift (x := TensorProduct.map graphV 1) (y := TensorProduct.map 1 graphV) (z := flipT)
    (by rw [← TensorProduct.map_mul, graphV_mul_graphV, mul_one, TensorProduct.map_one])
    (by rw [← TensorProduct.map_mul, graphV_mul_graphV, mul_one, TensorProduct.map_one])
    (TensorProduct.ext' fun _ _ => rfl)
    (by rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, one_mul, mul_one])
    (TensorProduct.ext' fun _ _ => rfl) (TensorProduct.ext' fun _ _ => rfl)

theorem repQ_a : repQ QFull.a = TensorProduct.map graphV 1 := by
  simp [repQ, QFull.lift, QFull.word, QFull.a]

theorem repQ_b : repQ QFull.b = TensorProduct.map 1 graphV := by
  simp [repQ, QFull.lift, QFull.word, QFull.b]

theorem repQ_s : repQ QFull.s = flipT := by
  simp [repQ, QFull.lift, QFull.word, QFull.s]

theorem qAct_a : qAct QFull.a = autA := by
  simp [qAct, QFull.lift, QFull.word, QFull.a]

theorem qAct_b : qAct QFull.b = autB := by
  simp [qAct, QFull.lift, QFull.word, QFull.b]

theorem qAct_s : qAct QFull.s = autS := by
  simp [qAct, QFull.lift, QFull.word, QFull.s]

theorem repQ_mul_repK (q : QFull) (k : K) : repQ q * repK k = repK (qAct q k) * repQ q := by
  let P : QFull → Prop := fun q => ∀ k, repQ q * repK k = repK (qAct q k) * repQ q
  have hmul : ∀ q r, P q → P r → P (q * r) := fun q r hq hr k => by
    rw [map_mul, mul_assoc, hr, ← mul_assoc, hq, mul_assoc, ← map_mul, map_mul qAct,
      MulAut.mul_apply]
  have h1 : P 1 := fun k => by rw [map_one, map_one, one_mul, mul_one, MulAut.one_apply]
  have ha : P QFull.a := fun k => by
    rw [repQ_a, qAct_a]
    change TensorProduct.map graphV 1 * TensorProduct.map (rho k.1) (rho k.2) =
      TensorProduct.map (rho (tau k.1)) (rho k.2) * TensorProduct.map graphV 1
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, graphV_mul_rho, one_mul, mul_one]
  have hb : P QFull.b := fun k => by
    rw [repQ_b, qAct_b]
    change TensorProduct.map 1 graphV * TensorProduct.map (rho k.1) (rho k.2) =
      TensorProduct.map (rho k.1) (rho (tau k.2)) * TensorProduct.map 1 graphV
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, graphV_mul_rho, one_mul, mul_one]
  have hs : P QFull.s := fun k => by
    rw [repQ_s, qAct_s]
    exact TensorProduct.ext' fun _ _ => rfl
  have hite : ∀ (c : Prop) [Decidable c] (r : QFull), P r → P (if c then 1 else r) :=
    fun c _ r hr => by split_ifs; exacts [h1, hr]
  rw [QFull.eq_word q]
  exact hmul _ _ (hmul _ _ (hite _ _ ha) (hite _ _ hb)) (hite _ _ hs) k

@[expose] def repE : Representation (ZMod 2) Efull T where
  toFun e := repK e.left * repQ e.right
  map_one' := by
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, map_one, one_mul]
  map_mul' e f := by
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, map_mul, mul_assoc,
      mul_assoc, ← mul_assoc (repQ e.right), repQ_mul_repK, mul_assoc]

@[expose] def inc0 : ZMod 2 →ₗ[ZMod 2] V := LinearMap.inl _ _ _

@[expose] def inc1 : N →ₗ[ZMod 2] V := LinearMap.inr _ _ _ ∘ₗ LinearMap.inl _ _ _

@[expose] def inc2 : Nd →ₗ[ZMod 2] V :=
  LinearMap.inr _ _ _ ∘ₗ LinearMap.inr _ _ _ ∘ₗ LinearMap.inl _ _ _

@[expose] def inc3 : A →ₗ[ZMod 2] V :=
  LinearMap.inr _ _ _ ∘ₗ LinearMap.inr _ _ _ ∘ₗ LinearMap.inr _ _ _

@[expose] def labelSub : Fin 4 → Submodule (ZMod 2) V :=
  ![LinearMap.range inc0, LinearMap.range inc1, LinearMap.range inc2, LinearMap.range inc3]

theorem rho_mem_labelSub (g : S) (i : Fin 4) : ∀ x ∈ labelSub i, rho g x ∈ labelSub i := by
  intro x hx
  fin_cases i <;> obtain ⟨y, rfl⟩ := hx
  · exact ⟨y, Prod.ext rfl (Prod.ext (map_zero (repN g)).symm
      (Prod.ext (map_zero (repNd g)).symm (map_zero (repA g)).symm))⟩
  · exact ⟨repN g y, Prod.ext rfl (Prod.ext rfl
      (Prod.ext (map_zero (repNd g)).symm (map_zero (repA g)).symm))⟩
  · exact ⟨repNd g y, Prod.ext rfl (Prod.ext (map_zero (repN g)).symm
      (Prod.ext rfl (map_zero (repA g)).symm))⟩
  · exact ⟨repA g y, Prod.ext rfl (Prod.ext (map_zero (repN g)).symm
      (Prod.ext (map_zero (repNd g)).symm rfl))⟩


@[expose] def block (i j : Fin 4) : Submodule (ZMod 2) T :=
  Submodule.span (ZMod 2)
    (Set.image2 (fun x y => x ⊗ₜ[ZMod 2] y) (labelSub i : Set V) (labelSub j : Set V))


theorem map_block_le {f g : V →ₗ[ZMod 2] V} {i j i' j' : Fin 4}
    (hf : ∀ x ∈ labelSub i, f x ∈ labelSub i') (hg : ∀ y ∈ labelSub j, g y ∈ labelSub j') :
    (block i j).map (TensorProduct.map f g) ≤ block i' j' := by
  rw [block, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨f x, hf x hx, g y, hg y hy, rfl⟩


@[expose] def MapsBlocks (F : Module.End (ZMod 2) T) (π : Equiv.Perm (Fin 4 × Fin 4)) : Prop :=
  ∀ ij : Fin 4 × Fin 4, (block ij.1 ij.2).map F ≤ block (π ij).1 (π ij).2


theorem mapsBlocks_repK (k : K) : MapsBlocks (repK k) 1 := fun ij =>
  map_block_le (rho_mem_labelSub k.1 ij.1) (rho_mem_labelSub k.2 ij.2)


abbrev U3 : Subgroup S := BinaryThreeSpace.sylowT

@[expose] def Jmat : S :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩


end CFSG.ProperTwoGeneratedCore.PairedTensor
