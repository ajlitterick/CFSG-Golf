module

public import CFSG.Milestones.ASVolI.H5
public import CFSG.Quasithin.H13.L32AH63b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Classify
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def permModAct (G : Type*) [Group G] (X : Type*) [MulAction G X] :
    G →* MulAut (Multiplicative (X → ZMod 2)) where
  toFun g :=
    { toFun := fun f => Multiplicative.ofAdd fun x => Multiplicative.toAdd f (g⁻¹ • x)
      invFun := fun f => Multiplicative.ofAdd fun x => Multiplicative.toAdd f (g • x)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext x
        simp
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext x
        simp
      map_mul' := fun f f' => by
        apply Multiplicative.toAdd.injective
        funext x
        simp }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]


abbrev AdjAmb : Type := Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))

@[expose] def adjAmbAct : GL (Fin 3) (ZMod 2) →* MulAut AdjAmb where
  toFun g :=
    { toFun := fun X => Multiplicative.ofAdd
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      invFun := fun X => Multiplicative.ofAdd
          (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      left_inv := fun X => by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        have h1 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h3 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * Multiplicative.toAdd X *
            (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
          simp only [Matrix.mul_assoc]
        rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun X => by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h3 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
              (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) * Multiplicative.toAdd X *
            ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
          simp only [Matrix.mul_assoc]
        rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
      map_mul' := fun X Y => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mul_add, Matrix.add_mul] }
  map_one' := by
    ext X
    simp
  map_mul' g h := by
    ext X
    apply Multiplicative.toAdd.injective
    simp [Matrix.mul_assoc]

@[expose] def Adj3 : Subgroup AdjAmb :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)))

@[expose] def prodAct {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) : G →* MulAut (A × B) where
  toFun g :=
    { toFun := fun x => (a g x.1, b g x.2)
      invFun := fun x => (a g⁻¹ x.1, b g⁻¹ x.2)
      left_inv := fun x => by
        ext
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun x => by
        ext
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun x y => by
        ext <;> simp }
  map_one' := by
    ext x <;> simp
  map_mul' g h := by
    ext x <;> simp

@[expose] def ModIsoSub {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) (S : Subgroup B) : Prop :=
  ∃ e : A →* B, Function.Injective e ∧ e.range = S ∧ ∀ (g : G) (x : A), e (a g x) = b g (e x)

@[expose] def ModIso {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) : Prop :=
  ModIsoSub a b ⊤


@[expose] def IsMaxSub {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (W N : Subgroup X) : Prop :=
  N < W ∧ (∀ g, ∀ u ∈ N, ρ g u ∈ N) ∧
    ∀ N' : Subgroup X, N ≤ N' → N' ≤ W → (∀ g, ∀ u ∈ N', ρ g u ∈ N') → N' = N ∨ N' = W


end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_6_1 : Prop :=
  (IsIrredOn modTriv.range ⊤ ∧ IsIrredOn modNat.range ⊤ ∧ IsIrredOn modDual.range ⊤ ∧
    IsIrredOn (adjAmbAct.range) Adj3) ∧
  (Nat.card (Multiplicative (ZMod 2)) = 2 ^ 1 ∧ Nat.card (Multiplicative V3) = 2 ^ 3 ∧
    Nat.card Adj3 = 2 ^ 8) ∧
  (¬ ModIso modTriv modNat ∧ ¬ ModIso modTriv modDual ∧ ¬ ModIso modNat modDual ∧
    ¬ ModIsoSub modTriv adjAmbAct Adj3 ∧ ¬ ModIsoSub modNat adjAmbAct Adj3 ∧
    ¬ ModIsoSub modDual adjAmbAct Adj3) ∧
  (∀ (A : Type) [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) →
    ∀ act : GL (Fin 3) (ZMod 2) →* MulAut A, IsIrredOn act.range ⊤ →
      ModIso act modTriv ∨ ModIso act modNat ∨ ModIso act modDual ∨ ModIsoSub act adjAmbAct Adj3)

section H61

private abbrev H61_TZ : Type := ↥(CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZero)

private abbrev H61_M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

private theorem H61_zmod2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private def H61_subOfMul {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (U : Subgroup (Multiplicative E)) : Submodule (ZMod 2) E where
  carrier := {x | Multiplicative.ofAdd x ∈ U}
  add_mem' := fun {x y} hx hy => by
    show Multiplicative.ofAdd (x + y) ∈ U
    rw [ofAdd_add]
    exact U.mul_mem hx hy
  zero_mem' := by
    show Multiplicative.ofAdd (0 : E) ∈ U
    rw [ofAdd_zero]
    exact U.one_mem
  smul_mem' := fun c {x} hx => by
    show Multiplicative.ofAdd (c • x) ∈ U
    rcases H61_zmod2 c with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact U.one_mem
    · rw [one_smul]
      exact hx

private def H61_linRep {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) :
    GL (Fin 3) (ZMod 2) →* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun g :=
    { toFun := fun x => MulEquiv.toAdditive (act g) x
      map_add' := fun x y => map_add (MulEquiv.toAdditive (act g)) x y
      map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive (act g)) c x
      invFun := fun x => (MulEquiv.toAdditive (act g)).symm x
      left_inv := fun x => (MulEquiv.toAdditive (act g)).symm_apply_apply x
      right_inv := fun x => (MulEquiv.toAdditive (act g)).apply_symm_apply x }
  map_one' := LinearEquiv.ext fun x => by
    show Additive.ofMul (act 1 (Additive.toMul x)) = x
    rw [map_one, MulAut.one_apply]
    rfl
  map_mul' g h := LinearEquiv.ext fun x => by
    show Additive.ofMul (act (g * h) (Additive.toMul x)) =
      Additive.ofMul (act g (Additive.toMul (Additive.ofMul (act h (Additive.toMul x)))))
    rw [map_mul, MulAut.mul_apply]
    rfl

private theorem H61_isIrrRep_linRep {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    {act : GL (Fin 3) (ZMod 2) →* MulAut A} (hirr : IsIrredOn act.range ⊤) :
    CFSG.QuasithinUnique.Setup.Family.IsIrrRep (H61_linRep act) := by
  obtain ⟨hne, hU⟩ := hirr
  have hnt : Nontrivial (Additive A) := by
    by_contra hnt
    apply hne
    rw [eq_bot_iff]
    intro a _
    rw [Subgroup.mem_bot]
    by_contra ha
    exact hnt ⟨⟨Additive.ofMul a, 0, fun h => ha (ofMul_eq_zero.1 h)⟩⟩
  refine ⟨hnt, fun g => map_zero (H61_linRep act g), fun N hN => ?_⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup A, ∀ a, a ∈ U ↔ Additive.ofMul a ∈ N := by
    refine ⟨{ carrier := {a | Additive.ofMul a ∈ N}
              mul_mem' := fun {a b} ha hb => ?_
              one_mem' := ?_
              inv_mem' := fun {a} ha => ?_ }, fun a => Iff.rfl⟩
    · have ha' : Additive.ofMul a ∈ N := ha
      have hb' : Additive.ofMul b ∈ N := hb
      show Additive.ofMul (a * b) ∈ N
      rw [ofMul_mul]
      exact N.add_mem ha' hb'
    · show Additive.ofMul (1 : A) ∈ N
      rw [ofMul_one]
      exact N.zero_mem
    · have ha' : Additive.ofMul a ∈ N := ha
      show Additive.ofMul a⁻¹ ∈ N
      rw [ofMul_inv]
      exact N.neg_mem ha'
  have hUinv : ∀ l ∈ act.range, ∀ u ∈ U, l u ∈ U := by
    rintro l ⟨g, rfl⟩ u hu
    rw [hUdef] at hu ⊢
    exact hN g _ hu
  rcases hU U le_top hUinv with hUb | hUt
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxU : Additive.toMul x ∈ U := by
      rw [hUdef, ofMul_toMul]
      exact hx
    rw [hUb, Subgroup.mem_bot] at hxU
    exact Additive.toMul.injective (hxU.trans toMul_zero.symm)
  · right
    rw [eq_top_iff]
    intro x _
    have hxU : Additive.toMul x ∈ U := by
      rw [hUt]
      exact Subgroup.mem_top _
    rw [hUdef, ofMul_toMul] at hxU
    exact hxU

private theorem H61_isIrredOn_of_isIrrRep {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL (Fin 3) (ZMod 2) →* (E ≃ₗ[ZMod 2] E)}
    (hρ : CFSG.QuasithinUnique.Setup.Family.IsIrrRep ρ)
    {b : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative E)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative E),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x))) :
    IsIrredOn b.range ⊤ := by
  obtain ⟨hnt, -, hirr⟩ := hρ
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  refine ⟨fun htop => ?_, fun U _ hU => ?_⟩
  · have hmem : Multiplicative.ofAdd x0 ∈ (⊤ : Subgroup (Multiplicative E)) :=
      Subgroup.mem_top _
    rw [htop, Subgroup.mem_bot] at hmem
    exact hx0 (ofAdd_eq_one.1 hmem)
  · have hNinv : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ H61_subOfMul U, ρ g x ∈ H61_subOfMul U := by
      intro g x hx
      have hx' : Multiplicative.ofAdd x ∈ U := hx
      show Multiplicative.ofAdd (ρ g x) ∈ U
      have key : Multiplicative.ofAdd (ρ g x) = b g (Multiplicative.ofAdd x) := (hb g _).symm
      rw [key]
      exact hU (b g) (MonoidHom.mem_range.2 ⟨g, rfl⟩) _ hx'
    rcases hirr (H61_subOfMul U) hNinv with hN | hN
    · left
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      have h1 : Multiplicative.toAdd u ∈ H61_subOfMul U := by
        show Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U
        exact hu
      rw [hN, Submodule.mem_bot] at h1
      exact Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)
    · right
      rw [eq_top_iff]
      intro u _
      have h1 : Multiplicative.toAdd u ∈ H61_subOfMul U := by
        rw [hN]
        exact Submodule.mem_top
      have h2 : Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U := h1
      exact h2

private theorem H61_mem_Adj3 (X : AdjAmb) : X ∈ Adj3 ↔ (Multiplicative.toAdd X).trace = 0 :=
  Iff.rfl

private def H61_adjEquiv : ↥Adj3 ≃ H61_TZ where
  toFun x := ⟨Multiplicative.toAdd (x : AdjAmb),
    CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.2 ((H61_mem_Adj3 _).1 x.2)⟩
  invFun y := ⟨Multiplicative.ofAdd (y : H61_M3), (H61_mem_Adj3 _).2
    (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 y.2)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

private theorem H61_natCard_Adj3 : Nat.card Adj3 = 256 :=
  (Nat.card_congr H61_adjEquiv).trans CFSG.QuasithinUnique.Setup.Family.natCard_traceZero

private def H61_subOfAdj (U : Subgroup AdjAmb) : Submodule (ZMod 2) H61_TZ where
  carrier := {x | Multiplicative.ofAdd (x : H61_M3) ∈ U}
  add_mem' := fun {x y} hx hy => by
    show Multiplicative.ofAdd (((x + y : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_add, ofAdd_add]
    exact U.mul_mem hx hy
  zero_mem' := by
    show Multiplicative.ofAdd (((0 : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_zero, ofAdd_zero]
    exact U.one_mem
  smul_mem' := fun c {x} hx => by
    show Multiplicative.ofAdd (((c • x : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_smul]
    rcases H61_zmod2 c with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact U.one_mem
    · rw [one_smul]
      exact hx

private theorem H61_isIrredOn_adj : IsIrredOn adjAmbAct.range Adj3 := by
  obtain ⟨hnt, -, hN⟩ := CFSG.QuasithinUnique.Setup.Family.isIrr_repA
  refine ⟨fun h => ?_, fun U hUle hU => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne (0 : H61_TZ)
    have hmem : Multiplicative.ofAdd (y : H61_M3) ∈ Adj3 :=
      (H61_mem_Adj3 _).2 (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 y.2)
    have h1 : Multiplicative.ofAdd (y : H61_M3) = 1 :=
      (Subgroup.eq_bot_iff_forall Adj3).1 h _ hmem
    apply hy
    apply Subtype.ext
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd, toAdd_one] at h2
    exact h2
  · have hNinv : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ H61_subOfAdj U,
        CFSG.QuasithinUnique.Setup.Family.repA g x ∈ H61_subOfAdj U := by
      intro g x hx
      have hx' : Multiplicative.ofAdd (x : H61_M3) ∈ U := hx
      show Multiplicative.ofAdd (((CFSG.QuasithinUnique.Setup.Family.repA g x : H61_TZ)) :
        H61_M3) ∈ U
      rw [CFSG.QuasithinUnique.Setup.Family.repA_apply]
      exact hU (adjAmbAct g) ⟨g, rfl⟩ _ hx'
    rcases hN (H61_subOfAdj U) hNinv with hb | ht
    · left
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      have h1 : H61_adjEquiv ⟨u, hUle hu⟩ ∈ H61_subOfAdj U := by
        show Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U
        exact hu
      rw [hb, Submodule.mem_bot] at h1
      have h2 : Multiplicative.toAdd u = 0 := congrArg Subtype.val h1
      exact Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
    · right
      apply le_antisymm hUle
      intro u hu
      have h1 : H61_adjEquiv ⟨u, hu⟩ ∈ H61_subOfAdj U := by
        rw [ht]
        exact Submodule.mem_top
      have h2 : Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U := h1
      exact h2

private theorem H61_modIsoSub_of_equiv {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    {act : GL (Fin 3) (ZMod 2) →* MulAut A} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : GL (Fin 3) (ZMod 2) →* (W ≃ₗ[ZMod 2] W)}
    {b : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative W)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x)))
    (f : W ≃ₗ[ZMod 2] Additive A)
    (hf : ∀ (g : GL (Fin 3) (ZMod 2)) (x : W), f (ρ g x) = H61_linRep act g (f x)) :
    ModIsoSub act b ⊤ := by
  let e : A →* Multiplicative W :=
    { toFun := fun a => Multiplicative.ofAdd (f.symm (Additive.ofMul a))
      map_one' := by
        show Multiplicative.ofAdd (f.symm (Additive.ofMul (1 : A))) = 1
        rw [ofMul_one, map_zero, ofAdd_zero]
      map_mul' := fun a a' => by
        show Multiplicative.ofAdd (f.symm (Additive.ofMul (a * a'))) =
          Multiplicative.ofAdd (f.symm (Additive.ofMul a)) *
            Multiplicative.ofAdd (f.symm (Additive.ofMul a'))
        rw [ofMul_mul, map_add, ofAdd_add] }
  unfold ModIsoSub
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a a' h
    have h' : Multiplicative.ofAdd (f.symm (Additive.ofMul a)) =
        Multiplicative.ofAdd (f.symm (Additive.ofMul a')) := h
    have h1 : f.symm (Additive.ofMul a) = f.symm (Additive.ofMul a') :=
      Multiplicative.ofAdd.injective h'
    exact Additive.ofMul.injective (f.symm.injective h1)
  · rw [MonoidHom.range_eq_top]
    intro y
    refine ⟨Additive.toMul (f (Multiplicative.toAdd y)), ?_⟩
    show Multiplicative.ofAdd (f.symm (f (Multiplicative.toAdd y))) = y
    rw [LinearEquiv.symm_apply_apply, ofAdd_toAdd]
  · intro g a
    show Multiplicative.ofAdd (f.symm (Additive.ofMul (act g a))) =
      b g (Multiplicative.ofAdd (f.symm (Additive.ofMul a)))
    rw [hb]
    congr 1
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hf, toAdd_ofAdd, LinearEquiv.apply_symm_apply]
    rfl

private theorem H61_modIsoSub_adj_of_equiv {A : Type} [CommGroup A]
    [Module (ZMod 2) (Additive A)] {act : GL (Fin 3) (ZMod 2) →* MulAut A}
    (f : H61_TZ ≃ₗ[ZMod 2] Additive A)
    (hf : ∀ (g : GL (Fin 3) (ZMod 2)) (x : H61_TZ),
      f (CFSG.QuasithinUnique.Setup.Family.repA g x) = H61_linRep act g (f x)) :
    ModIsoSub act adjAmbAct Adj3 := by
  let e : A →* AdjAmb :=
    { toFun := fun a => Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3)
      map_one' := by
        show Multiplicative.ofAdd ((f.symm (Additive.ofMul (1 : A)) : H61_TZ) : H61_M3) = 1
        rw [ofMul_one, map_zero, Submodule.coe_zero, ofAdd_zero]
      map_mul' := fun a a' => by
        show Multiplicative.ofAdd ((f.symm (Additive.ofMul (a * a')) : H61_TZ) : H61_M3) =
          Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3) *
            Multiplicative.ofAdd ((f.symm (Additive.ofMul a') : H61_TZ) : H61_M3)
        rw [ofMul_mul, map_add, Submodule.coe_add, ofAdd_add] }
  unfold ModIsoSub
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a a' h
    have h' : Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3) =
        Multiplicative.ofAdd ((f.symm (Additive.ofMul a') : H61_TZ) : H61_M3) := h
    have h1 := Multiplicative.ofAdd.injective h'
    have h2 : f.symm (Additive.ofMul a) = f.symm (Additive.ofMul a') := Subtype.ext h1
    exact Additive.ofMul.injective (f.symm.injective h2)
  · ext X
    constructor
    · intro hX
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hX
      exact (H61_mem_Adj3 _).2
        (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 (f.symm (Additive.ofMul a)).2)
    · intro hX
      obtain ⟨y, hy1⟩ : ∃ y : H61_TZ, (y : H61_M3) = Multiplicative.toAdd X :=
        ⟨⟨Multiplicative.toAdd X,
          CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.2 ((H61_mem_Adj3 X).1 hX)⟩,
          rfl⟩
      refine MonoidHom.mem_range.2 ⟨Additive.toMul (f y), ?_⟩
      show Multiplicative.ofAdd ((f.symm (f y) : H61_TZ) : H61_M3) = X
      rw [LinearEquiv.symm_apply_apply, hy1]
      exact ofAdd_toAdd X
  · intro g a
    show Multiplicative.ofAdd ((f.symm (Additive.ofMul (act g a)) : H61_TZ) : H61_M3) =
      adjAmbAct g (Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3))
    have key : f.symm (Additive.ofMul (act g a)) =
        CFSG.QuasithinUnique.Setup.Family.repA g (f.symm (Additive.ofMul a)) := by
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
      rfl
    rw [key, CFSG.QuasithinUnique.Setup.Family.repA_apply]
    rfl

private theorem H61_modIso_of_modIsoSub {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ ρ' : GL (Fin 3) (ZMod 2) →* (W ≃ₗ[ZMod 2] W)}
    {b b' : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative W)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x)))
    (hb' : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b' g x = Multiplicative.ofAdd (ρ' g (Multiplicative.toAdd x)))
    (h : ModIsoSub b b' ⊤) :
    CFSG.QuasithinUnique.Setup.Family.ModIso ρ ρ' := by
  obtain ⟨e, hinj, hrange, heq⟩ := h
  have hsurj : Function.Surjective e := MonoidHom.range_eq_top.1 hrange
  let φ : W →+ W :=
    { toFun := fun w => Multiplicative.toAdd (e (Multiplicative.ofAdd w))
      map_zero' := by
        show Multiplicative.toAdd (e (Multiplicative.ofAdd 0)) = 0
        rw [ofAdd_zero, map_one, toAdd_one]
      map_add' := fun w w' => by
        show Multiplicative.toAdd (e (Multiplicative.ofAdd (w + w'))) =
          Multiplicative.toAdd (e (Multiplicative.ofAdd w)) +
            Multiplicative.toAdd (e (Multiplicative.ofAdd w'))
        rw [ofAdd_add, map_mul, toAdd_mul] }
  have hφinj : Function.Injective φ := by
    intro w w' h1
    have h2 : e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd w') :=
      Multiplicative.toAdd.injective h1
    exact Multiplicative.ofAdd.injective (hinj h2)
  have hφsurj : Function.Surjective φ := by
    intro w'
    obtain ⟨z, hz⟩ := hsurj (Multiplicative.ofAdd w')
    refine ⟨Multiplicative.toAdd z, ?_⟩
    show Multiplicative.toAdd (e (Multiplicative.ofAdd (Multiplicative.toAdd z))) = w'
    rw [ofAdd_toAdd, hz, toAdd_ofAdd]
  unfold CFSG.QuasithinUnique.Setup.Family.ModIso CFSG.QuasithinUnique.Setup.Family.ActIso
  refine ⟨LinearEquiv.ofBijective (φ.toZModLinearMap 2) ⟨hφinj, hφsurj⟩, fun g x => ?_⟩
  have h1 := heq g (Multiplicative.ofAdd x)
  rw [hb, hb', toAdd_ofAdd] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_ofAdd] at h2
  exact h2

private theorem H61_natCard_le {A B : Type} [CommGroup A] [CommGroup B] [Finite A]
    {a : GL (Fin 3) (ZMod 2) →* MulAut A} {b : GL (Fin 3) (ZMod 2) →* MulAut B}
    {S : Subgroup B} (h : ModIsoSub a b S) : Nat.card S ≤ Nat.card A := by
  obtain ⟨e, -, hrange, -⟩ := h
  have hmem : ∀ x : A, e x ∈ S := fun x => by
    rw [← hrange]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  refine Nat.card_le_card_of_surjective (fun x : A => (⟨e x, hmem x⟩ : S)) ?_
  rintro ⟨s, hs⟩
  rw [← hrange] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨x, Subtype.ext hx⟩

private theorem H61_natCard_top {G : Type} [Group G] :
    Nat.card (⊤ : Subgroup G) = Nat.card G :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

private theorem H61_natCard_F2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
  Nat.card_zmod 2

private theorem H61_natCard_V3 : Nat.card (Multiplicative V3) = 8 :=
  CFSG.QuasithinUnique.Setup.Family.natCard_Vec3

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem as_H_6_1 : H_6_1 := by
  refine ⟨⟨H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repTriv
      (b := modTriv) (fun _ _ => rfl),
    H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repV
      (b := modNat) (fun _ _ => rfl),
    H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repDual
      (b := modDual) (fun _ _ => rfl),
    H61_isIrredOn_adj⟩,
    ⟨H61_natCard_F2.trans (by norm_num), H61_natCard_V3.trans (by norm_num),
      H61_natCard_Adj3.trans (by norm_num)⟩,
    ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_⟩
  · have h' : Nat.card (Multiplicative V3) ≤ Nat.card (Multiplicative (ZMod 2)) :=
      (H61_natCard_top (G := Multiplicative V3)).symm.le.trans (H61_natCard_le h)
    rw [H61_natCard_V3, H61_natCard_F2] at h'
    omega
  · have h' : Nat.card (Multiplicative V3) ≤ Nat.card (Multiplicative (ZMod 2)) :=
      (H61_natCard_top (G := Multiplicative V3)).symm.le.trans (H61_natCard_le h)
    rw [H61_natCard_V3, H61_natCard_F2] at h'
    omega
  · exact CFSG.QuasithinUnique.Setup.Family.not_modIso_repV_repDual
      (H61_modIso_of_modIsoSub (ρ := CFSG.QuasithinUnique.Setup.Family.repV)
        (ρ' := CFSG.QuasithinUnique.Setup.Family.repDual) (b := modNat) (b' := modDual)
        (fun _ _ => rfl) (fun _ _ => rfl) h)
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative (ZMod 2)) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_F2] at h'
    omega
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative V3) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_V3] at h'
    omega
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative V3) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_V3] at h'
    omega
  · intro A _ _ h2 act hirr
    letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) (fun x => by
      rw [two_nsmul]
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zero, ← sq]
      exact h2 _)
    rcases CFSG.QuasithinUnique.Setup.Family.irreducible_binary_GL3_classification
        (E := Additive A) (H61_linRep act) (H61_isIrrRep_linRep hirr) with h | h | h | h
    · obtain ⟨f, hf⟩ := h
      exact Or.inl (H61_modIsoSub_of_equiv (ρ := CFSG.QuasithinUnique.Setup.Family.repTriv)
        (b := modTriv) (fun _ _ => rfl) f hf)
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inl (H61_modIsoSub_of_equiv (ρ := CFSG.QuasithinUnique.Setup.Family.repV)
        (b := modNat) (fun _ _ => rfl) f hf))
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inr (Or.inl (H61_modIsoSub_of_equiv
        (ρ := CFSG.QuasithinUnique.Setup.Family.repDual) (b := modDual) (fun _ _ => rfl) f hf)))
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inr (Or.inr (H61_modIsoSub_adj_of_equiv f hf)))

end H61


@[expose] def H_6_3 : Prop :=
  (∃ (ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2))
      (π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb),
      (∀ x : ↥Adj3, π (ι x) = (x : AdjAmb)) ∧ (∀ f, π f ∈ Adj3) ∧
      (∀ (g : GL (Fin 3) (ZMod 2)) (x x' : ↥Adj3), (x' : AdjAmb) = adjAmbAct g x →
        ι x' = permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g (ι x)) ∧
      (∀ (g : GL (Fin 3) (ZMod 2)) (f : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)),
        π (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g f) = adjAmbAct g (π f))) ∧
  ((∃ β : AdjAmb → AdjAmb → ZMod 2,
      (∀ u ∈ Adj3, ∀ u' ∈ Adj3, ∀ w ∈ Adj3, β (u * u') w = β u w + β u' w) ∧
      (∀ u ∈ Adj3, ∀ w ∈ Adj3, ∀ w' ∈ Adj3, β u (w * w') = β u w + β u w') ∧
      (∀ (g : GL (Fin 3) (ZMod 2)), ∀ u ∈ Adj3, ∀ w ∈ Adj3, β (adjAmbAct g u) (adjAmbAct g w) = β u w) ∧
      (∀ u ∈ Adj3, u ≠ 1 → ∃ w ∈ Adj3, β u w ≠ 0)) ∧
    (∀ α : MulAut (GL (Fin 3) (ZMod 2)),
      ∃ e : ↥Adj3 →* AdjAmb, Function.Injective e ∧ e.range = Adj3 ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (x y : ↥Adj3), (y : AdjAmb) = adjAmbAct (α g) x →
          e y = adjAmbAct g (e x))) ∧
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    (NoncentralChiefCount {f | ∃ g ∈ Lpt p, f = fun x => adjAmbAct g x} Adj3 3 ∧
      NoncentralChiefCount {f | ∃ g ∈ Lln l, f = fun x => adjAmbAct g x} Adj3 3) ∧
    (∃ m ∈ Adj3, m ≠ 1 ∧ (∀ g ∈ T, adjAmbAct g m = m) ∧
      (∀ m' ∈ Adj3, m' ≠ 1 → (∀ g ∈ T, adjAmbAct g m' = m') → m' = m) ∧
      ∀ g : GL (Fin 3) (ZMod 2), adjAmbAct g m = m → g ∈ T) ∧
    (commOn Adj3 ((Lln l).map adjAmbAct) = Adj3 ∧ commOn Adj3 ((Lpt p).map adjAmbAct) = Adj3)


section HBridge65
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


private noncomputable def kappa (p : Fin 3 → ZMod 2) : GL (Fin 3) (ZMod 2) ⧸ Lpt p → Fin 3 → ZMod 2 :=
  Quotient.lift (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p)
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ Lpt p := QuotientGroup.leftRel_apply.1 hab
      have h1 : ((a⁻¹ * b : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
        (mem_Lpt _ p).1 hab' p (Set.mem_singleton p)
      show (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = (b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p
      calc (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p
          = (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
              (((a⁻¹ * b : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p) := by
            rw [h1]
        _ = (a * (a⁻¹ * b) : GL (Fin 3) (ZMod 2)).val.mulVec p := (mulVec_gl a (a⁻¹ * b) p).symm
        _ = (b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p := by rw [mul_inv_cancel_left])


private noncomputable def cosetFintype (p : Fin 3 → ZMod 2) : Fintype (GL (Fin 3) (ZMod 2) ⧸ Lpt p) :=
  Fintype.ofFinite _

attribute [local instance] cosetFintype


private theorem gl_det_one (k : GL (Fin 3) (ZMod 2)) : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have hu : IsUnit (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
  have hne : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
  revert hne
  generalize (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
  revert d
  decide

private theorem zmod2_mul_eq_one : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide

private theorem Lpt_inter_le_B0 (k : GL (Fin 3) (ZMod 2))
    (hk1 : ∀ v ∈ ({e1} : Set (Fin 3 → ZMod 2)), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v)
    (hk2 : ∀ v ∈ (line0 : Set (Fin 3 → ZMod 2)),
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ line0) :
    k ∈ B0 := by
  rw [mem_B0]
  have hcol := hk1 e1 (Set.mem_singleton _)
  have e0 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ (line0 : Set (Fin 3 → ZMod 2)) := by
    simp [mem_line0]
  have e1' : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ (line0 : Set (Fin 3 → ZMod 2)) := by
    simp [mem_line0]
  have h20 := mem_line0.1 (hk2 _ e0)
  have h21 := mem_line0.1 (hk2 _ e1')
  have hdet := gl_det_one k
  have m00 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := by
    have := congrFun hcol 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m10 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 := by
    have := congrFun hcol 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m20 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := by
    have := congrFun hcol 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m21 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h21
  have hdet' : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 * (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1 := by
    rw [Matrix.det_fin_three, m00, m10, m20, m21] at hdet
    linear_combination hdet
  obtain ⟨h11, h22⟩ := zmod2_mul_eq_one _ _ hdet'
  refine ⟨(k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2,
    (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m00, m10, m20, m21, h11, h22]


private theorem sigma_mul {N : Type} [AddCommGroup N] (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (x y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ (x * y) n = σ x (σ y n) := by
  rw [map_mul]
  rfl


private theorem sigma_inv_left {N : Type} [AddCommGroup N]
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ g⁻¹ (σ g n) = n := by
  rw [← sigma_mul, inv_mul_cancel, map_one]
  rfl

private theorem sigma_inv_right {N : Type} [AddCommGroup N]
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ g (σ g⁻¹ n) = n := by
  rw [← sigma_mul, mul_inv_cancel, map_one]
  rfl


private theorem mem_Adj3_iff (y : AdjAmb) : y ∈ Adj3 ↔ (Multiplicative.toAdd y).trace = 0 := by
  simp [Adj3]


private theorem slGL_symm_coe (h : GL (Fin 3) (ZMod 2)) :
    ((slGL.symm h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have := slGL_coe (slGL.symm h)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

private theorem slGL_symm_inv_coe (h : GL (Fin 3) (ZMod 2)) :
    (((slGL.symm h)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [← map_inv slGL.symm h, slGL_symm_coe]


private noncomputable def iotaInv (y : ↥Adj3) : CFSG.Quasithin.H6.St :=
  ⟨Multiplicative.toAdd y.1, (CFSG.Quasithin.H6.mem_stSub).2 ((mem_Adj3_iff y.1).1 y.2)⟩

private def iotaOf (m : CFSG.Quasithin.H6.St) : ↥Adj3 :=
  ⟨Multiplicative.ofAdd m.1, (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 m.2)⟩

private theorem iotaInv_iotaOf (m : CFSG.Quasithin.H6.St) : iotaInv (iotaOf m) = m := rfl


private theorem adjAmbAct_mem (h : GL (Fin 3) (ZMod 2)) (X : AdjAmb) (hX : X ∈ Adj3) :
    adjAmbAct h X ∈ Adj3 := by
  rw [mem_Adj3_iff] at hX ⊢
  have hinv : ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  show ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
    ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))).trace = 0
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  exact hX

private theorem coe_rhoSt (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (x : CFSG.Quasithin.H6.St) :
    (CFSG.Quasithin.H6.ρSt g x).1 =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x.1 *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.H6.coe_smul_st g x

private theorem iotaInv_smul (h : GL (Fin 3) (ZMod 2)) (y : ↥Adj3) :
    iotaInv ⟨adjAmbAct h y.1, adjAmbAct_mem h y.1 y.2⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm h) (iotaInv y) := by
  apply Subtype.ext
  show Multiplicative.toAdd (adjAmbAct h y.1) = (CFSG.Quasithin.H6.ρSt (slGL.symm h) (iotaInv y)).1
  rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]
  rfl

private theorem iotaInv_mul (x y : ↥Adj3) : iotaInv (x * y) = iotaInv x + iotaInv y := by
  apply Subtype.ext
  rfl


end HBridge65


section H63
open CFSG.Quasithin.MS93 Matrix

private theorem zmod2_self_add' (a : ZMod 2) : a + a = 0 := by revert a; decide

private def h63a : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩
private def h63b : GL (Fin 3) (ZMod 2) := ⟨1, 1, by simp, by simp⟩
private def h63c : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩
private def h63d : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩
private def h63e : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩
private def h63f : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩
private def h63g : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide, by decide⟩
private def h63h : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 1, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 1, 1], by decide, by decide⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 65536 in
set_option maxRecDepth 10000 in
private theorem trace_detect63 : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    (X * ((h63a : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63a⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63b : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63b⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63d : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63d⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63e : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63e⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63f : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63f⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    X = 0 := by
  decide +kernel

private theorem rhoSt_slGL_symm_coe (h : GL (Fin 3) (ZMod 2)) (x : CFSG.Quasithin.H6.St) :
    (CFSG.Quasithin.H6.ρSt (slGL.symm h) x).1 =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x.1 *
        ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]

private noncomputable def stF63 : CFSG.Quasithin.H6.St →+ (GL (Fin 3) (ZMod 2) → ZMod 2) where
  toFun x h := CFSG.Quasithin.H6.stForm x (CFSG.Quasithin.H6.ρSt (slGL.symm h) CFSG.Quasithin.H6.stE13)
  map_zero' := by
    funext h
    simp
  map_add' x y := by
    funext h
    simp

private theorem stF63_apply (x : CFSG.Quasithin.H6.St) (h : GL (Fin 3) (ZMod 2)) :
    stF63 x h = (x.1 * ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace := by
  show CFSG.Quasithin.H6.stForm x (CFSG.Quasithin.H6.ρSt (slGL.symm h) CFSG.Quasithin.H6.stE13) = _
  rw [CFSG.Quasithin.H6.stForm_apply, rhoSt_slGL_symm_coe]

private theorem stF63_injective : Function.Injective stF63 := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ h : GL (Fin 3) (ZMod 2),
      (x.1 * ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
        ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 := by
    intro h
    have hh : stF63 x h = 0 := congrFun hx h
    rw [stF63_apply] at hh
    exact hh
  apply Subtype.ext
  exact trace_detect63 x.1 (CFSG.Quasithin.H6.mem_stSub.1 x.2) (key h63a) (key h63b) (key h63c)
    (key h63d) (key h63e) (key h63f) (key h63g) (key h63h)

private noncomputable def regAct63 :
    GL (Fin 3) (ZMod 2) →* AddMonoid.End (GL (Fin 3) (ZMod 2) → ZMod 2) where
  toFun k :=
    { toFun := fun φ h => φ (k⁻¹ * h)
      map_zero' := rfl
      map_add' := fun φ ψ => rfl }
  map_one' := by
    ext φ h
    show φ (1⁻¹ * h) = φ h
    simp
  map_mul' k l := by
    ext φ h
    show φ ((k * l)⁻¹ * h) = φ (l⁻¹ * (k⁻¹ * h))
    simp [mul_assoc, _root_.mul_inv_rev]


private noncomputable def regSL63 :
    CFSG.Quasithin.H6.Γ →* AddMonoid.End (GL (Fin 3) (ZMod 2) → ZMod 2) :=
  regAct63.comp slGL.toMonoidHom

private theorem regSL63_apply (g : CFSG.Quasithin.H6.Γ) (φ : GL (Fin 3) (ZMod 2) → ZMod 2)
    (h : GL (Fin 3) (ZMod 2)) : regSL63 g φ h = φ ((slGL g)⁻¹ * h) := rfl

private theorem trace_conj_GL63 (G : GL (Fin 3) (ZMod 2)) (x M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ((G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M).trace =
      (x * (((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M * (G : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace := by
  have e1 : (G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M =
      (G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M) := by
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private theorem stF63_equiv (g : CFSG.Quasithin.H6.Γ) (x : CFSG.Quasithin.H6.St) :
    stF63 (CFSG.Quasithin.H6.ρSt g x) = regSL63 g (stF63 x) := by
  funext h
  rw [regSL63_apply, stF63_apply, stF63_apply, coe_rhoSt]
  have h1 : ((g : CFSG.Quasithin.H6.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := (slGL_coe g).symm
  have h2 : (((g⁻¹ : CFSG.Quasithin.H6.Γ)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← slGL_coe, map_inv]
  rw [h1, h2]
  have hK : ((((slGL g)⁻¹ * h : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (slGL g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hK' : (((slGL g)⁻¹ * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    Units.val_mul _ _
  rw [hK, hK']
  rw [trace_conj_GL63 (slGL g) x.1]
  simp only [Matrix.mul_assoc]


open scoped Classical in
private noncomputable def betaAdj (u w : AdjAmb) : ZMod 2 :=
  if h : u ∈ Adj3 ∧ w ∈ Adj3 then
    CFSG.Quasithin.H6.stForm (iotaInv ⟨u, h.1⟩) (iotaInv ⟨w, h.2⟩) else 0

private theorem betaAdj_mul_left (u u' w : AdjAmb) (hu : u ∈ Adj3) (hu' : u' ∈ Adj3) (hw : w ∈ Adj3) :
    betaAdj (u * u') w = betaAdj u w + betaAdj u' w := by
  unfold betaAdj
  rw [dif_pos ⟨Subgroup.mul_mem _ hu hu', hw⟩, dif_pos ⟨hu, hw⟩, dif_pos ⟨hu', hw⟩]
  have h1 : iotaInv ⟨u * u', Subgroup.mul_mem _ hu hu'⟩ = iotaInv ⟨u, hu⟩ + iotaInv ⟨u', hu'⟩ :=
    iotaInv_mul ⟨u, hu⟩ ⟨u', hu'⟩
  rw [h1, map_add, AddMonoidHom.add_apply]

private theorem betaAdj_mul_right (u w w' : AdjAmb) (hu : u ∈ Adj3) (hw : w ∈ Adj3) (hw' : w' ∈ Adj3) :
    betaAdj u (w * w') = betaAdj u w + betaAdj u w' := by
  unfold betaAdj
  rw [dif_pos ⟨hu, Subgroup.mul_mem _ hw hw'⟩, dif_pos ⟨hu, hw⟩, dif_pos ⟨hu, hw'⟩]
  have h1 : iotaInv ⟨w * w', Subgroup.mul_mem _ hw hw'⟩ = iotaInv ⟨w, hw⟩ + iotaInv ⟨w', hw'⟩ :=
    iotaInv_mul ⟨w, hw⟩ ⟨w', hw'⟩
  rw [h1, map_add]

private theorem betaAdj_adj (g : GL (Fin 3) (ZMod 2)) (u w : AdjAmb) (hu : u ∈ Adj3) (hw : w ∈ Adj3) :
    betaAdj (adjAmbAct g u) (adjAmbAct g w) = betaAdj u w := by
  unfold betaAdj
  rw [dif_pos ⟨adjAmbAct_mem g u hu, adjAmbAct_mem g w hw⟩, dif_pos ⟨hu, hw⟩]
  have h1 : iotaInv ⟨adjAmbAct g u, adjAmbAct_mem g u hu⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv ⟨u, hu⟩) := iotaInv_smul g ⟨u, hu⟩
  have h2 : iotaInv ⟨adjAmbAct g w, adjAmbAct_mem g w hw⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv ⟨w, hw⟩) := iotaInv_smul g ⟨w, hw⟩
  rw [h1, h2]
  exact CFSG.Quasithin.H6.stForm_conj _ _ _

private theorem betaAdj_nondeg (u : AdjAmb) (hu : u ∈ Adj3) (hu1 : u ≠ 1) :
    ∃ w ∈ Adj3, betaAdj u w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hu1
  have hx : iotaInv ⟨u, hu⟩ = 0 := by
    apply CFSG.Quasithin.H6.stForm_nondeg
    intro y
    have hw : Multiplicative.ofAdd y.1 ∈ Adj3 := (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 y.2)
    have h0 := hcon _ hw
    unfold betaAdj at h0
    rw [dif_pos ⟨hu, hw⟩] at h0
    have hy : iotaInv ⟨Multiplicative.ofAdd y.1, hw⟩ = y := by
      apply Subtype.ext
      rfl
    rw [hy] at h0
    exact h0
  have h2 : Multiplicative.toAdd u = 0 := congrArg Subtype.val hx
  apply Multiplicative.toAdd.injective
  rw [h2, toAdd_one]


private theorem H63_part1 : ∃ (ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2))
    (π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb),
    (∀ x : ↥Adj3, π (ι x) = (x : AdjAmb)) ∧ (∀ f, π f ∈ Adj3) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (x x' : ↥Adj3), (x' : AdjAmb) = adjAmbAct g x →
      ι x' = permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g (ι x)) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (f : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)),
      π (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g f) = adjAmbAct g (π f)) := by
  obtain ⟨p, hp1, hp2⟩ := CFSG.Quasithin.H6.st_injective regSL63
    (fun φ => funext fun h => zmod2_self_add' _) stF63 stF63_injective stF63_equiv
  let ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (stF63 (iotaInv y))
      map_one' := by
        have h0 : iotaInv (1 : ↥Adj3) = 0 := by
          apply Subtype.ext
          rfl
        show Multiplicative.ofAdd (stF63 (iotaInv 1)) = 1
        rw [h0, map_zero, ofAdd_zero]
      map_mul' := fun y z => by
        show Multiplicative.ofAdd (stF63 (iotaInv (y * z))) =
          Multiplicative.ofAdd (stF63 (iotaInv y)) * Multiplicative.ofAdd (stF63 (iotaInv z))
        rw [iotaInv_mul, map_add, ofAdd_add] }
  let π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb :=
    { toFun := fun F => Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1)
      map_one' := by
        show Multiplicative.ofAdd ((p (Multiplicative.toAdd (1 : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)))).1) = 1
        rw [toAdd_one, map_zero]
        rfl
      map_mul' := fun F G => by
        show Multiplicative.ofAdd ((p (Multiplicative.toAdd (F * G))).1) =
          Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1) * Multiplicative.ofAdd ((p (Multiplicative.toAdd G)).1)
        rw [toAdd_mul, map_add, AddSubgroup.coe_add, ofAdd_add] }
  refine ⟨ι, π, ?_, ?_, ?_, ?_⟩
  · intro x
    show Multiplicative.ofAdd ((p (Multiplicative.toAdd (Multiplicative.ofAdd (stF63 (iotaInv x))))).1) = (x : AdjAmb)
    rw [toAdd_ofAdd, hp1]
    rfl
  · intro F
    exact (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 (p _).2)
  · intro g x x' hx'
    have hx2 : iotaInv x' = CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv x) := by
      have e : x' = ⟨adjAmbAct g x, adjAmbAct_mem g x x.2⟩ := Subtype.ext hx'
      rw [e]
      exact iotaInv_smul g x
    apply Multiplicative.toAdd.injective
    funext h
    show stF63 (iotaInv x') h = stF63 (iotaInv x) (g⁻¹ • h)
    rw [hx2, stF63_equiv, regSL63_apply, MulEquiv.apply_symm_apply, smul_eq_mul]
  · intro g F
    have hF : Multiplicative.toAdd (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g F) =
        regSL63 (slGL.symm g) (Multiplicative.toAdd F) := by
      funext h
      rw [regSL63_apply, MulEquiv.apply_symm_apply]
      rfl
    show Multiplicative.ofAdd ((p (Multiplicative.toAdd (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g F))).1) =
      adjAmbAct g (Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1))
    rw [hF, hp2, rhoSt_slGL_symm_coe]
    rfl

end H63


private theorem conj_data6 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    ∃ c : GL (Fin 3) (ZMod 2), (∀ g : GL (Fin 3) (ZMod 2), g ∈ T ↔ c⁻¹ * g * c ∈ B0) ∧
      (∀ y ∈ B0, c * y * c⁻¹ ∈ T) ∧
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
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → ZMod 2,
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
  have hline : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
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
  exact ⟨c, hc, hconjT, hpc, hline⟩


private theorem B0_fix_e1_6 (x : GL (Fin 3) (ZMod 2)) (hx : x ∈ B0) : x ∈ Lpt e1 := by
  obtain ⟨a, b, c, hx'⟩ := (mem_B0 x).1 hx
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, hx']
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1]

private theorem B0_le_Lln_line0_6 (x : GL (Fin 3) (ZMod 2)) (hx : x ∈ B0) : x ∈ Lln line0 := by
  have key : ∀ k : GL (Fin 3) (ZMod 2), k ∈ B0 → ∀ v : V3, v 2 = 0 →
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v 2 = 0 := by
    intro k hk v hv
    obtain ⟨a, b', c', hk'⟩ := (mem_B0 k).1 hk
    rw [hk']
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv]
  rw [mem_Lln]
  intro v hv
  have hv' : v 2 = 0 := mem_line0.1 (SetLike.mem_coe.1 hv)
  exact ⟨mem_line0.2 (key x hx v hv'), mem_line0.2 (key _ (Subgroup.inv_mem B0 hx) v hv')⟩

private theorem borel_iff_B0 (h : CFSG.Quasithin.H6.Γ) :
    h ∈ CFSG.Quasithin.H6.borel ↔ slGL h ∈ B0 := by
  rw [CFSG.Quasithin.H6.borel, Subgroup.mem_inf]
  constructor
  · rintro ⟨hLp, hLl⟩
    exact Lpt_inter_le_B0 (slGL h) ((mem_Lpt _ _).1 ((mem_Lp_iff h).1 hLp))
      (fun v hv => ((mem_Lln _ _).1 ((mem_Ll_iff h).1 hLl) v hv).1)
  · intro hB
    exact ⟨(mem_Lp_iff h).2 (B0_fix_e1_6 _ hB), (mem_Ll_iff h).2 (B0_le_Lln_line0_6 _ hB)⟩

private theorem mulVec_conj6 (c b : GL (Fin 3) (ZMod 2)) (y : V3) :
    ((c * b * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y)) := by
  rw [mulVec_gl, mulVec_gl]

private theorem mem_Lpt_conj6 (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (k : GL (Fin 3) (ZMod 2))
    (hk : k ∈ Lpt e1) : c * k * c⁻¹ ∈ Lpt p := by
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, ← hpc, mulVec_conj6, inv_mulVec_mulVec]
  rw [(mem_Lpt _ _).1 hk e1 (Set.mem_singleton _)]

private theorem rho_mul_apply6 (a b : CFSG.Quasithin.H6.Γ) (x : CFSG.Quasithin.H6.St) :
    CFSG.Quasithin.H6.ρSt (a * b) x = CFSG.Quasithin.H6.ρSt a (CFSG.Quasithin.H6.ρSt b x) :=
  sigma_mul CFSG.Quasithin.H6.ρSt a b x

private theorem iotaInv_inj6 {y z : ↥Adj3} (h : iotaInv y = iotaInv z) : y = z := by
  apply Subtype.ext
  have h4 : Multiplicative.toAdd y.1 = Multiplicative.toAdd z.1 :=
    congrArg (fun m : CFSG.Quasithin.H6.St => m.1) h
  exact Multiplicative.toAdd.injective h4

private theorem adj_fix_iff6 (g : GL (Fin 3) (ZMod 2)) (y : ↥Adj3) :
    adjAmbAct g (y : AdjAmb) = (y : AdjAmb) ↔
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv y) = iotaInv y := by
  have key : iotaInv (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv y) := iotaInv_smul g y
  constructor
  · intro h
    have e : (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) = y := Subtype.ext h
    rw [← key, e]
  · intro h
    have e : (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) = y :=
      iotaInv_inj6 (by rw [key, h])
    exact congrArg Subtype.val e


private theorem H63_part2b (α : MulAut (GL (Fin 3) (ZMod 2))) :
    ∃ e : ↥Adj3 →* AdjAmb, Function.Injective e ∧ e.range = Adj3 ∧
      ∀ (g : GL (Fin 3) (ZMod 2)) (x y : ↥Adj3), (y : AdjAmb) = adjAmbAct (α g) x →
        e y = adjAmbAct g (e x) := by
  let α' : CFSG.Quasithin.H6.Γ ≃* CFSG.Quasithin.H6.Γ := slGL.trans (α.trans slGL.symm)
  obtain ⟨f, hfbij, hfeq⟩ := CFSG.Quasithin.H6.isoMod_twist CFSG.Quasithin.H6.volI_H_6_5 α'
  let e : ↥Adj3 →* AdjAmb :=
    { toFun := fun y => Multiplicative.ofAdd ((f (iotaInv y)).1)
      map_one' := by
        have h0 : iotaInv (1 : ↥Adj3) = 0 := by
          apply Subtype.ext
          rfl
        show Multiplicative.ofAdd ((f (iotaInv 1)).1) = 1
        rw [h0, map_zero, AddSubgroup.coe_zero, ofAdd_zero]
      map_mul' := fun y z => by
        show Multiplicative.ofAdd ((f (iotaInv (y * z))).1) =
          Multiplicative.ofAdd ((f (iotaInv y)).1) * Multiplicative.ofAdd ((f (iotaInv z)).1)
        rw [iotaInv_mul, map_add, AddSubgroup.coe_add, ofAdd_add] }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro y z hyz
    have h1 : (f (iotaInv y)).1 = (f (iotaInv z)).1 := Multiplicative.ofAdd.injective hyz
    have h2 : f (iotaInv y) = f (iotaInv z) := Subtype.ext h1
    exact iotaInv_inj6 (hfbij.1 h2)
  · ext X
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 (f (iotaInv y)).2)
    · intro hX
      obtain ⟨z, hz⟩ := hfbij.2 ⟨Multiplicative.toAdd X, CFSG.Quasithin.H6.mem_stSub.2 ((mem_Adj3_iff X).1 hX)⟩
      refine ⟨iotaOf z, ?_⟩
      show Multiplicative.ofAdd ((f (iotaInv (iotaOf z))).1) = X
      rw [iotaInv_iotaOf, hz]
      rfl
  · intro g x y hy
    have hy' : iotaInv y = CFSG.Quasithin.H6.ρSt (slGL.symm (α g)) (iotaInv x) := by
      have e1 : y = ⟨adjAmbAct (α g) x.1, adjAmbAct_mem (α g) x.1 x.2⟩ := Subtype.ext hy
      rw [e1]
      exact iotaInv_smul (α g) x
    have hα : slGL.symm (α g) = α' (slGL.symm g) := by
      show slGL.symm (α g) = slGL.symm (α (slGL (slGL.symm g)))
      rw [MulEquiv.apply_symm_apply]
    have hfg : f (CFSG.Quasithin.H6.ρSt (α' (slGL.symm g)) (iotaInv x)) =
        CFSG.Quasithin.H6.ρSt (slGL.symm g) (f (iotaInv x)) := hfeq (slGL.symm g) (iotaInv x)
    show Multiplicative.ofAdd ((f (iotaInv y)).1) =
      adjAmbAct g (Multiplicative.ofAdd ((f (iotaInv x)).1))
    rw [hy', hα, hfg, rhoSt_slGL_symm_coe]
    rfl

private theorem conj_cancel6 {G : Type*} [Group G] (a b : G) : a * (a⁻¹ * b * a) * a⁻¹ = b := by
  simp [mul_assoc]

private theorem H63_part4 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    ∃ m ∈ Adj3, m ≠ 1 ∧ (∀ g ∈ T, adjAmbAct g m = m) ∧
      (∀ m' ∈ Adj3, m' ≠ 1 → (∀ g ∈ T, adjAmbAct g m' = m') → m' = m) ∧
      ∀ g : GL (Fin 3) (ZMod 2), adjAmbAct g m = m → g ∈ T := by
  obtain ⟨c, hc, -, -, -⟩ := conj_data6 T p l hyp
  obtain ⟨m0, hm0, hfix, huniq⟩ := CFSG.Quasithin.H6.st_fix_borel
  obtain ⟨sc, hsc⟩ : ∃ sc : CFSG.Quasithin.H6.Γ, slGL sc = c :=
    ⟨slGL.symm c, MulEquiv.apply_symm_apply slGL c⟩
  have hinv : ∀ w : CFSG.Quasithin.H6.St, CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt sc w) = w :=
    fun w => sigma_inv_left CFSG.Quasithin.H6.ρSt sc w
  have hfwd : ∀ w : CFSG.Quasithin.H6.St, CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹ w) = w :=
    fun w => sigma_inv_right CFSG.Quasithin.H6.ρSt sc w
  have hconv : ∀ g : GL (Fin 3) (ZMod 2),
      g ∈ T ↔ sc⁻¹ * slGL.symm g * sc ∈ CFSG.Quasithin.H6.borel := by
    intro g
    rw [borel_iff_B0, map_mul, map_mul, map_inv, hsc, MulEquiv.apply_symm_apply]
    exact hc g
  have hsymm : ∀ h : CFSG.Quasithin.H6.Γ, slGL.symm (c * slGL h * c⁻¹) = sc * h * sc⁻¹ := by
    intro h
    apply slGL.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hsc]
  have hm1ne : CFSG.Quasithin.H6.ρSt sc m0 ≠ 0 := by
    intro h0
    apply hm0
    calc m0 = CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt sc m0) := (hinv m0).symm
      _ = CFSG.Quasithin.H6.ρSt sc⁻¹ 0 := by rw [h0]
      _ = 0 := map_zero _
  have hkey : ∀ h : CFSG.Quasithin.H6.Γ, CFSG.Quasithin.H6.ρSt h m0 = m0 →
      CFSG.Quasithin.H6.ρSt (sc * h * sc⁻¹) (CFSG.Quasithin.H6.ρSt sc m0) =
        CFSG.Quasithin.H6.ρSt sc m0 := by
    intro h hh
    rw [rho_mul_apply6 (sc * h) sc⁻¹, hinv m0, rho_mul_apply6 sc h, hh]
  refine ⟨((iotaOf (CFSG.Quasithin.H6.ρSt sc m0) : ↥Adj3) : AdjAmb), (iotaOf (CFSG.Quasithin.H6.ρSt sc m0)).2,
    ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hm1ne
    have h2 : (CFSG.Quasithin.H6.ρSt sc m0).1 = 0 :=
      congrArg (fun y : AdjAmb => Multiplicative.toAdd y) h1
    exact Subtype.ext h2
  · intro g hg
    rw [adj_fix_iff6, iotaInv_iotaOf]
    have hb : sc⁻¹ * slGL.symm g * sc ∈ CFSG.Quasithin.H6.borel := (hconv g).1 hg
    have e2 : sc * (sc⁻¹ * slGL.symm g * sc) * sc⁻¹ = slGL.symm g := conj_cancel6 sc _
    have := hkey _ (hfix _ hb)
    rw [e2] at this
    exact this
  · intro m' hm' hne hfixT
    have hyne : iotaInv (⟨m', hm'⟩ : ↥Adj3) ≠ 0 := by
      intro h0
      apply hne
      have h1 : Multiplicative.toAdd m' = 0 := congrArg Subtype.val h0
      exact Multiplicative.toAdd.injective (by rw [h1, toAdd_one])
    have hfixz : ∀ h ∈ CFSG.Quasithin.H6.borel,
        CFSG.Quasithin.H6.ρSt h (CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3))) =
          CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by
      intro h hh
      have hT : c * slGL h * c⁻¹ ∈ T := (hc _).2 (by
        rw [show c⁻¹ * (c * slGL h * c⁻¹) * c = slGL h from conj_cancel6 c⁻¹ _ |>.symm ▸ rfl]
        exact (borel_iff_B0 h).1 hh)
      have e1 := (adj_fix_iff6 (c * slGL h * c⁻¹) ⟨m', hm'⟩).1 (hfixT _ hT)
      rw [hsymm h] at e1
      have e3 : sc⁻¹ * (sc * h * sc⁻¹) = h * sc⁻¹ := by simp [mul_assoc]
      calc CFSG.Quasithin.H6.ρSt h (CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)))
          = CFSG.Quasithin.H6.ρSt (h * sc⁻¹) (iotaInv (⟨m', hm'⟩ : ↥Adj3)) :=
            (rho_mul_apply6 h sc⁻¹ _).symm
        _ = CFSG.Quasithin.H6.ρSt (sc⁻¹ * (sc * h * sc⁻¹)) (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by
            rw [e3]
        _ = CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt (sc * h * sc⁻¹) (iotaInv (⟨m', hm'⟩ : ↥Adj3))) :=
            rho_mul_apply6 _ _ _
        _ = CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by rw [e1]
    have hzne : CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) ≠ 0 := by
      intro h0
      apply hyne
      calc iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹
              (iotaInv (⟨m', hm'⟩ : ↥Adj3))) := (hfwd _).symm
        _ = CFSG.Quasithin.H6.ρSt sc 0 := by rw [h0]
        _ = 0 := map_zero _
    have hz0 := huniq _ hzne hfixz
    have hw : iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc m0 := by
      calc iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹
              (iotaInv (⟨m', hm'⟩ : ↥Adj3))) := (hfwd _).symm
        _ = CFSG.Quasithin.H6.ρSt sc m0 := by rw [hz0]
    exact congrArg Subtype.val (iotaInv_inj6 (hw.trans (iotaInv_iotaOf _).symm))
  · intro g hg
    rw [adj_fix_iff6, iotaInv_iotaOf] at hg
    apply (hconv g).2
    apply CFSG.Quasithin.H6.st_stabilizer m0 hm0 hfix
    rw [rho_mul_apply6 (sc⁻¹ * slGL.symm g) sc, rho_mul_apply6 sc⁻¹ (slGL.symm g), hg, hinv m0]

private theorem H63_part2a : ∃ β : AdjAmb → AdjAmb → ZMod 2,
    (∀ u ∈ Adj3, ∀ u' ∈ Adj3, ∀ w ∈ Adj3, β (u * u') w = β u w + β u' w) ∧
    (∀ u ∈ Adj3, ∀ w ∈ Adj3, ∀ w' ∈ Adj3, β u (w * w') = β u w + β u w') ∧
    (∀ (g : GL (Fin 3) (ZMod 2)), ∀ u ∈ Adj3, ∀ w ∈ Adj3,
      β (adjAmbAct g u) (adjAmbAct g w) = β u w) ∧
    (∀ u ∈ Adj3, u ≠ 1 → ∃ w ∈ Adj3, β u w ≠ 0) :=
  ⟨betaAdj, fun u hu u' hu' w hw => betaAdj_mul_left u u' w hu hu' hw,
    fun u hu w hw w' hw' => betaAdj_mul_right u w w' hu hw hw',
    fun g u hu w hw => betaAdj_adj g u w hu hw,
    fun u hu hu1 => betaAdj_nondeg u hu hu1⟩

private theorem theta_rho (c : GL (Fin 3) (ZMod 2)) (g : CFSG.Quasithin.H6.Γ)
    (m : CFSG.Quasithin.H6.St) :
    adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m).1) =
      adjAmbAct (c * slGL g * c⁻¹) (adjAmbAct c (Multiplicative.ofAdd m.1)) := by
  have hm : (CFSG.Quasithin.H6.ρSt g m).1 =
      ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m.1 *
        (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [coe_rhoSt, slGL_coe, ← map_inv slGL g, slGL_coe]
  rw [← MulAut.mul_apply, ← map_mul, show c * slGL g * c⁻¹ * c = c * slGL g by group, map_mul,
    MulAut.mul_apply, hm]
  rfl

private theorem comm_full_gen (c : GL (Fin 3) (ZMod 2)) (Hs : Subgroup CFSG.Quasithin.H6.Γ)
    (A : Subgroup (MulAut AdjAmb)) (hA2 : ∀ a ∈ A, ∀ x ∈ Adj3, a x ∈ Adj3)
    (hA : ∀ g ∈ Hs, adjAmbAct (c * slGL g * c⁻¹) ∈ A)
    (hclos : AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
      y = CFSG.Quasithin.H6.ρSt g m - m} = ⊤) :
    commOn Adj3 A = Adj3 := by
  apply le_antisymm
  · unfold commOn
    apply (Subgroup.closure_le _).2
    rintro u ⟨a, ha, w, hw, rfl⟩
    exact Subgroup.mul_mem _ (hA2 a ha w hw) (Subgroup.inv_mem _ hw)
  · intro X hX
    let θ : CFSG.Quasithin.H6.St → AdjAmb := fun x => adjAmbAct c (Multiplicative.ofAdd x.1)
    have hθmem : ∀ x : CFSG.Quasithin.H6.St, θ x ∈ Adj3 := fun x =>
      adjAmbAct_mem c _ ((mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 x.2))
    have hθ : ∀ x ∈ AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
        y = CFSG.Quasithin.H6.ρSt g m - m}, θ x ∈ commOn Adj3 A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨g, hg, m, rfl⟩ := hy
        have e : θ (CFSG.Quasithin.H6.ρSt g m - m) = θ (CFSG.Quasithin.H6.ρSt g m) * (θ m)⁻¹ := by
          show adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m - m).1) =
            adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m).1) *
              (adjAmbAct c (Multiplicative.ofAdd m.1))⁻¹
          rw [AddSubgroup.coe_sub, ofAdd_sub, div_eq_mul_inv, map_mul, map_inv]
        rw [e]
        have e2 : θ (CFSG.Quasithin.H6.ρSt g m) = adjAmbAct (c * slGL g * c⁻¹) (θ m) :=
          theta_rho c g m
        rw [e2]
        exact Subgroup.subset_closure ⟨_, hA g hg, θ m, hθmem m, rfl⟩
      | zero =>
        have e : θ 0 = 1 := by
          show adjAmbAct c (Multiplicative.ofAdd (0 : CFSG.Quasithin.H6.St).1) = 1
          rw [AddSubgroup.coe_zero, ofAdd_zero, map_one]
        rw [e]
        exact one_mem _
      | add y z _ _ hy hz =>
        have e : θ (y + z) = θ y * θ z := by
          show adjAmbAct c (Multiplicative.ofAdd (y + z).1) =
            adjAmbAct c (Multiplicative.ofAdd y.1) * adjAmbAct c (Multiplicative.ofAdd z.1)
          rw [AddSubgroup.coe_add, ofAdd_add, map_mul]
        rw [e]
        exact mul_mem hy hz
      | neg y _ hy =>
        have e : θ (-y) = (θ y)⁻¹ := by
          show adjAmbAct c (Multiplicative.ofAdd (-y).1) = (adjAmbAct c (Multiplicative.ofAdd y.1))⁻¹
          rw [AddSubgroup.coe_neg, ofAdd_neg, map_inv]
        rw [e]
        exact inv_mem hy
    have hX' : adjAmbAct c⁻¹ X ∈ Adj3 := adjAmbAct_mem c⁻¹ X hX
    let x : CFSG.Quasithin.H6.St :=
      ⟨Multiplicative.toAdd (adjAmbAct c⁻¹ X), CFSG.Quasithin.H6.mem_stSub.2 ((mem_Adj3_iff _).1 hX')⟩
    have hxmem : x ∈ AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
        y = CFSG.Quasithin.H6.ρSt g m - m} := by
      rw [hclos]
      exact AddSubgroup.mem_top x
    have hx := hθ x hxmem
    have e : θ x = X := by
      show adjAmbAct c (Multiplicative.ofAdd (Multiplicative.toAdd (adjAmbAct c⁻¹ X))) = X
      rw [ofAdd_toAdd, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at hx
    exact hx

private theorem H63_part5 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    commOn Adj3 ((Lln l).map adjAmbAct) = Adj3 ∧ commOn Adj3 ((Lpt p).map adjAmbAct) = Adj3 := by
  obtain ⟨c, -, -, hpc, hline⟩ := conj_data6 T p l hyp
  constructor
  · refine comm_full_gen c CFSG.Quasithin.H6.Ll ((Lln l).map adjAmbAct) ?_ ?_
      CFSG.Quasithin.H6.st_comm_Ll
    · intro a ha x hx
      obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 ha
      exact adjAmbAct_mem g x hx
    · intro g hg
      exact Subgroup.mem_map_of_mem adjAmbAct
        ((mem_Lln_conj c l hline (slGL g)).1 ((mem_Ll_iff g).1 hg))
  · refine comm_full_gen c CFSG.Quasithin.H6.Lp ((Lpt p).map adjAmbAct) ?_ ?_
      CFSG.Quasithin.H6.st_comm_Lp
    · intro a ha x hx
      obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 ha
      exact adjAmbAct_mem g x hx
    · intro g hg
      exact Subgroup.mem_map_of_mem adjAmbAct (mem_Lpt_conj6 c p hpc (slGL g) ((mem_Lp_iff g).1 hg))


private theorem adj_cancel6 (c : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c (adjAmbAct c⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem adj_cancel6' (c : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c⁻¹ (adjAmbAct c x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem adj_conj_comm2 (c g : GL (Fin 3) (ZMod 2)) (y : AdjAmb) :
    adjAmbAct (c⁻¹ * g * c) y = adjAmbAct c⁻¹ (adjAmbAct g (adjAmbAct c y)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

private theorem adj_inv_act (c g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c⁻¹ (adjAmbAct g x) = adjAmbAct (c⁻¹ * g * c) (adjAmbAct c⁻¹ x) := by
  rw [adj_conj_comm2, adj_cancel6]

private theorem adj_conj_comm (c g : GL (Fin 3) (ZMod 2)) (y : AdjAmb) :
    adjAmbAct (c * g * c⁻¹) y = adjAmbAct c (adjAmbAct g (adjAmbAct c⁻¹ y)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

set_option maxHeartbeats 1000000 in
private theorem ncc_transport (c : GL (Fin 3) (ZMod 2)) (H H' : Subgroup (GL (Fin 3) (ZMod 2)))
    (hH : ∀ g : GL (Fin 3) (ZMod 2), g ∈ H ↔ c * g * c⁻¹ ∈ H') (k : ℕ)
    (hnc : NoncentralChiefCount {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} Adj3 k) :
    NoncentralChiefCount {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x} Adj3 k := by
  obtain ⟨n, S, h0, hn, hch, hcount⟩ := hnc
  obtain ⟨S', hS'def⟩ : ∃ S' : ℕ → Subgroup AdjAmb,
      S' = fun i => (S i).map (adjAmbAct c : MulAut AdjAmb).toMonoidHom := ⟨_, rfl⟩
  have hmem : ∀ i x, x ∈ S' i ↔ adjAmbAct c⁻¹ x ∈ S i := by
    intro i x
    rw [hS'def]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show adjAmbAct c⁻¹ (adjAmbAct c y) ∈ S i
      rw [adj_cancel6']
      exact hy
    · intro hx
      exact ⟨adjAmbAct c⁻¹ x, hx, adj_cancel6 c x⟩
  have hH' : ∀ g' : GL (Fin 3) (ZMod 2), g' ∈ H' → c⁻¹ * g' * c ∈ H := fun g' hg' => by
    rw [hH]
    simpa [mul_assoc] using hg'
  have hH'' : ∀ g : GL (Fin 3) (ZMod 2), g ∈ H → c * g * c⁻¹ ∈ H' := fun g hg => (hH g).1 hg
  have hS'0 : S' 0 = ⊥ := by
    ext x
    rw [hmem, h0, Subgroup.mem_bot, Subgroup.mem_bot]
    exact MulEquiv.map_eq_one_iff (adjAmbAct c⁻¹ : MulAut AdjAmb)
  have hS'n : S' n = Adj3 := by
    ext x
    rw [hmem, hn]
    constructor
    · intro h
      have := adjAmbAct_mem c _ h
      rwa [adj_cancel6] at this
    · intro h
      exact adjAmbAct_mem c⁻¹ x h
  have hactS' : ∀ j, IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} (S j) →
      IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x} (S' j) := by
    intro j hinv f hf x hx
    obtain ⟨g', hg', rfl⟩ := hf
    show adjAmbAct g' x ∈ S' j
    rw [hmem] at hx ⊢
    have e : adjAmbAct c⁻¹ (adjAmbAct g' x) = adjAmbAct (c⁻¹ * g' * c) (adjAmbAct c⁻¹ x) := by
      rw [adj_conj_comm2, adj_cancel6]
    rw [e]
    exact hinv (fun y => adjAmbAct (c⁻¹ * g' * c) y) ⟨c⁻¹ * g' * c, hH' g' hg', rfl⟩ _ hx
  have hchief : ∀ i, i < n → IsChiefFactorUnder {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x}
      (S' i) (S' (i + 1)) := by
    intro i hi
    obtain ⟨hlt, hinvX, hinvY, hmax⟩ := hch i hi
    refine ⟨?_, hactS' i hinvX, hactS' (i + 1) hinvY, ?_⟩
    · have hle : S' i ≤ S' (i + 1) := by
        rw [hS'def]
        exact Subgroup.map_mono hlt.le
      refine lt_of_le_of_ne hle ?_
      intro heq
      rw [hS'def] at heq
      exact hlt.ne (Subgroup.map_injective (f := (adjAmbAct c : MulAut AdjAmb).toMonoidHom)
        (MulEquiv.injective _) heq)
    · intro W hW1 hW2 hWact
      obtain ⟨W0, hW0def⟩ : ∃ W0 : Subgroup AdjAmb,
          W0 = W.comap (adjAmbAct c : MulAut AdjAmb).toMonoidHom := ⟨_, rfl⟩
      have hW0mem : ∀ x, x ∈ W0 ↔ adjAmbAct c x ∈ W := fun x => by rw [hW0def]; rfl
      have hW0a : S i ≤ W0 := by
        intro x hx
        rw [hW0mem]
        exact hW1 ((hmem i _).2 (by rw [adj_cancel6']; exact hx))
      have hW0b : W0 ≤ S (i + 1) := by
        intro x hx
        rw [hW0mem] at hx
        have h := (hmem (i + 1) _).1 (hW2 hx)
        rwa [adj_cancel6'] at h
      have hW0c : IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} W0 := by
        intro f hf x hx
        obtain ⟨g, hg, rfl⟩ := hf
        rw [hW0mem] at hx ⊢
        have e : adjAmbAct c (adjAmbAct g x) = adjAmbAct (c * g * c⁻¹) (adjAmbAct c x) := by
          rw [adj_conj_comm, adj_cancel6']
        show adjAmbAct c (adjAmbAct g x) ∈ W
        rw [e]
        exact hWact (fun y => adjAmbAct (c * g * c⁻¹) y) ⟨c * g * c⁻¹, hH'' g hg, rfl⟩ _ hx
      have key : ∀ y, y ∈ W ↔ adjAmbAct c⁻¹ y ∈ W0 := fun y => by
        rw [hW0mem, adj_cancel6]
      rcases hmax W0 hW0a hW0b hW0c with h | h
      · left
        ext y
        rw [key y, h, hmem]
      · right
        ext y
        rw [key y, h, hmem]
  refine ⟨n, S', hS'0, hS'n, hchief, ?_⟩
  have hset : {i : ℕ | i < n ∧ ∃ f ∈ {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x},
        ∃ u ∈ S' (i + 1), f u * u⁻¹ ∉ S' i} =
      {i : ℕ | i < n ∧ ∃ f ∈ {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x},
        ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hi, f, ⟨g', hg', rfl⟩, u, hu, hnot⟩
      refine ⟨hi, fun x => adjAmbAct (c⁻¹ * g' * c) x, ⟨c⁻¹ * g' * c, hH' g' hg', rfl⟩,
        adjAmbAct c⁻¹ u, (hmem (i + 1) u).1 hu, ?_⟩
      intro hin
      apply hnot
      rw [hmem]
      show adjAmbAct c⁻¹ (adjAmbAct g' u * u⁻¹) ∈ S i
      have hm : adjAmbAct c⁻¹ (adjAmbAct g' u * u⁻¹) =
          adjAmbAct c⁻¹ (adjAmbAct g' u) * adjAmbAct c⁻¹ u⁻¹ :=
        map_mul (adjAmbAct c⁻¹ : MulAut AdjAmb) _ _
      have hi : adjAmbAct c⁻¹ u⁻¹ = (adjAmbAct c⁻¹ u)⁻¹ := map_inv (adjAmbAct c⁻¹ : MulAut AdjAmb) u
      have ha : adjAmbAct c⁻¹ (adjAmbAct g' u) = adjAmbAct (c⁻¹ * g' * c) (adjAmbAct c⁻¹ u) :=
        adj_inv_act c g' u
      rw [hm, hi, ha]
      exact hin
    · rintro ⟨hi, f, ⟨g, hg, rfl⟩, u, hu, hnot⟩
      refine ⟨hi, fun x => adjAmbAct (c * g * c⁻¹) x, ⟨c * g * c⁻¹, hH'' g hg, rfl⟩,
        adjAmbAct c u, (hmem (i + 1) _).2 (by rw [adj_cancel6']; exact hu), ?_⟩
      intro hin
      rw [hmem] at hin
      apply hnot
      have e5 : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u) * (adjAmbAct c u)⁻¹) =
          adjAmbAct g u * u⁻¹ := by
        have hm : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u) * (adjAmbAct c u)⁻¹) =
            adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u)) * adjAmbAct c⁻¹ (adjAmbAct c u)⁻¹ :=
          map_mul (adjAmbAct c⁻¹ : MulAut AdjAmb) _ _
        have hi : adjAmbAct c⁻¹ (adjAmbAct c u)⁻¹ = (adjAmbAct c⁻¹ (adjAmbAct c u))⁻¹ :=
          map_inv (adjAmbAct c⁻¹ : MulAut AdjAmb) _
        have hc1 : adjAmbAct c⁻¹ (adjAmbAct c u) = u := adj_cancel6' c u
        have hc2 : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u)) = adjAmbAct g u := by
          rw [adj_conj_comm, adj_cancel6', adj_cancel6']
        rw [hm, hi, hc1, hc2]
      rw [← e5]
      exact hin
  exact (congrArg Set.ncard hset).trans hcount

end CFSG.ASVolI

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem ncc_entry_mul (a b : AdjAmb) (i j : Fin 3) :
    Multiplicative.toAdd (a * b) i j = Multiplicative.toAdd a i j + Multiplicative.toAdd b i j := by
  rw [toAdd_mul, Matrix.add_apply]

private theorem ncc_entry_inv (a : AdjAmb) (i j : Fin 3) :
    Multiplicative.toAdd a⁻¹ i j = -Multiplicative.toAdd a i j := by
  rw [toAdd_inv, Matrix.neg_apply]

private theorem ncc_entry_one (i j : Fin 3) : Multiplicative.toAdd (1 : AdjAmb) i j = 0 := by
  rw [toAdd_one, Matrix.zero_apply]

private def nccCut (Y : Subgroup AdjAmb) (i j : Fin 3) : Subgroup AdjAmb where
  carrier := {x | Multiplicative.toAdd x i j = 0 ∧ x ∈ Y}
  mul_mem' {a b} ha hb := ⟨by rw [ncc_entry_mul, ha.1, hb.1, add_zero], Y.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨ncc_entry_one i j, Y.one_mem⟩
  inv_mem' {a} ha := ⟨by rw [ncc_entry_inv, ha.1, neg_zero], Y.inv_mem ha.2⟩


private theorem ncc_mem_Adj3 {x : AdjAmb} :
    x ∈ Adj3 ↔ Multiplicative.toAdd x 0 0 + Multiplicative.toAdd x 1 1 +
      Multiplicative.toAdd x 2 2 = 0 := by
  simp [Adj3, Matrix.trace, Fin.sum_univ_three]

private instance nccDecCut (Y : Subgroup AdjAmb) [DecidablePred (· ∈ Y)] (i j : Fin 3) :
    DecidablePred (· ∈ nccCut Y i j) :=
  fun x => decidable_of_iff (Multiplicative.toAdd x i j = 0 ∧ x ∈ Y) Iff.rfl

private instance nccDecAdj3 : DecidablePred (· ∈ Adj3) :=
  fun _ => decidable_of_iff _ ncc_mem_Adj3.symm

private def nccActs (G : Subgroup (GL (Fin 3) (ZMod 2))) : Set (AdjAmb → AdjAmb) :=
  {f | ∃ g ∈ G, f = fun x => adjAmbAct g x}

private theorem ncc_inv_of {G : Subgroup (GL (Fin 3) (ZMod 2))} {S : Subgroup AdjAmb}
    (h : ∀ g ∈ G, ∀ x ∈ S, adjAmbAct g x ∈ S) : IsActsInv (nccActs G) S := by
  rintro f ⟨g, hg, rfl⟩ u hu
  exact h g hg u hu

private theorem ncc_hom {G : Subgroup (GL (Fin 3) (ZMod 2))} :
    ∀ f ∈ nccActs G, ∀ a b, f (a * b) = f a * f b := by
  rintro f ⟨g, -, rfl⟩ a b
  exact map_mul _ a b

private theorem ncc_toAdd_act (g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    Multiplicative.toAdd (adjAmbAct g x) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd x *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

private theorem ncc_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem ncc_z2_eq {a b : ZMod 2} (h : a + b = 0) : b = a := by
  revert a b; decide

private theorem ncc_four (c1 c2 e1 e2 d1 d2 : ZMod 2) (hc : ¬ (c1 = 0 ∧ c2 = 0))
    (he : ¬ (e1 = 0 ∧ e2 = 0)) (hce : ¬ (e1 = c1 ∧ e2 = c2)) :
    (d1 = 0 ∧ d2 = 0) ∨ (d1 = c1 ∧ d2 = c2) ∨ (d1 = e1 ∧ d2 = e2) ∨
      (d1 = c1 + e1 ∧ d2 = c2 + e2) := by
  revert hc he hce
  rcases ncc_z2 c1 with rfl | rfl <;> rcases ncc_z2 c2 with rfl | rfl <;>
    rcases ncc_z2 e1 with rfl | rfl <;> rcases ncc_z2 e2 with rfl | rfl <;>
    rcases ncc_z2 d1 with rfl | rfl <;> rcases ncc_z2 d2 with rfl | rfl <;> decide

private theorem ncc_mul3 (A X B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    (A * X * B) i j =
      (A i 0 * X 0 0 + A i 1 * X 1 0 + A i 2 * X 2 0) * B 0 j +
      (A i 0 * X 0 1 + A i 1 * X 1 1 + A i 2 * X 2 1) * B 1 j +
      (A i 0 * X 0 2 + A i 1 * X 1 2 + A i 2 * X 2 2) * B 2 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]

private theorem ncc_AB (g : GL (Fin 3) (ZMod 2)) (i j : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 0 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 j +
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 1 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 j +
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 2 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
  have h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← h, Matrix.mul_apply, Fin.sum_univ_three]

private theorem ncc_Adj3_inv (g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) (hx : x ∈ Adj3) :
    adjAmbAct g x ∈ Adj3 := by
  have key : Matrix.trace (Multiplicative.toAdd (adjAmbAct g x)) =
      Matrix.trace (Multiplicative.toAdd x) := by
    rw [ncc_toAdd_act, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  have h1 : ∀ y : AdjAmb, y ∈ Adj3 ↔ Matrix.trace (Multiplicative.toAdd y) = 0 := fun y => by
    simp only [Adj3, Multiplicative.mem_toSubgroup, AddMonoidHom.mem_ker,
      Matrix.traceAddMonoidHom_apply]
  rw [h1] at hx ⊢
  rw [key]
  exact hx

private theorem ncc_act_inv_act (g : GL (Fin 3) (ZMod 2)) (u : AdjAmb) :
    adjAmbAct g⁻¹ (adjAmbAct g u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem ncc_chief_one (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j : Fin 3) :
    ∀ W : Subgroup AdjAmb, nccCut Y i j ≤ W → W ≤ Y → IsActsInv acts W →
      W = nccCut Y i j ∨ W = Y := by
  intro W hXW hWY _
  by_cases h : W ≤ nccCut Y i j
  · exact Or.inl (le_antisymm h hXW)
  right
  refine le_antisymm hWY ?_
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp h
  have hwY : w ∈ Y := hWY hwW
  have hw1 : Multiplicative.toAdd w i j = 1 := by
    rcases ncc_z2 (Multiplicative.toAdd w i j) with h0 | h1
    · exact (hwX ⟨h0, hwY⟩).elim
    · exact h1
  intro y hy
  rcases ncc_z2 (Multiplicative.toAdd y i j) with h0 | h1
  · exact hXW ⟨h0, hy⟩
  · have hm : y * w⁻¹ ∈ nccCut Y i j :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, h1, hw1]; decide, Y.mul_mem hy (Y.inv_mem hwY)⟩
    simpa using W.mul_mem (hXW hm) hwW

private theorem ncc_chief_two (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j k l : Fin 3)
    (hhom : ∀ f ∈ acts, ∀ a b, f (a * b) = f a * f b)
    (hX : IsActsInv acts (nccCut (nccCut Y i j) k l))
    (hwit : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Y, Multiplicative.toAdd r i j = a ∧
      Multiplicative.toAdd r k l = b ∧ ∃ f ∈ acts,
        ¬ (Multiplicative.toAdd (f r) i j = 0 ∧ Multiplicative.toAdd (f r) k l = 0) ∧
        ¬ (Multiplicative.toAdd (f r) i j = a ∧ Multiplicative.toAdd (f r) k l = b)) :
    ∀ W : Subgroup AdjAmb, nccCut (nccCut Y i j) k l ≤ W → W ≤ Y → IsActsInv acts W →
      W = nccCut (nccCut Y i j) k l ∨ W = Y := by
  intro W hXW hWY hW
  by_cases h : W ≤ nccCut (nccCut Y i j) k l
  · exact Or.inl (le_antisymm h hXW)
  right
  refine le_antisymm hWY ?_
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp h
  have hwY : w ∈ Y := hWY hwW
  have hab : ¬ (Multiplicative.toAdd w i j = 0 ∧ Multiplicative.toAdd w k l = 0) :=
    fun hh => hwX ⟨hh.2, hh.1, hwY⟩
  obtain ⟨r, hrY, hra, hrb, f, hf, he0, hec⟩ := hwit _ _ hab
  have hx : r⁻¹ * w ∈ nccCut (nccCut Y i j) k l :=
    ⟨by rw [ncc_entry_mul, ncc_entry_inv, hrb, neg_add_cancel],
      by rw [ncc_entry_mul, ncc_entry_inv, hra, neg_add_cancel], Y.mul_mem (Y.inv_mem hrY) hwY⟩
  have hfx := hX f hf _ hx
  have hfw : f w = f r * f (r⁻¹ * w) := by rw [← hhom f hf, mul_inv_cancel_left]
  have hfwW : f w ∈ W := hW f hf w hwW
  have hfwY : f w ∈ Y := hWY hfwW
  have e1 : Multiplicative.toAdd (f w) i j = Multiplicative.toAdd (f r) i j := by
    rw [hfw, ncc_entry_mul, hfx.2.1, add_zero]
  have e2 : Multiplicative.toAdd (f w) k l = Multiplicative.toAdd (f r) k l := by
    rw [hfw, ncc_entry_mul, hfx.1, add_zero]
  intro y hy
  have key := ncc_four (Multiplicative.toAdd w i j) (Multiplicative.toAdd w k l)
    (Multiplicative.toAdd (f w) i j) (Multiplicative.toAdd (f w) k l)
    (Multiplicative.toAdd y i j) (Multiplicative.toAdd y k l) hab (by rwa [e1, e2])
    (by rwa [e1, e2])
  rcases key with ⟨d1, d2⟩ | ⟨d1, d2⟩ | ⟨d1, d2⟩ | ⟨d1, d2⟩
  · exact hXW ⟨d2, d1, hy⟩
  · have hm : y * w⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, d2, add_neg_cancel],
        by rw [ncc_entry_mul, ncc_entry_inv, d1, add_neg_cancel], Y.mul_mem hy (Y.inv_mem hwY)⟩
    simpa using W.mul_mem (hXW hm) hwW
  · have hm : y * (f w)⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, d2, add_neg_cancel],
        by rw [ncc_entry_mul, ncc_entry_inv, d1, add_neg_cancel], Y.mul_mem hy (Y.inv_mem hfwY)⟩
    simpa using W.mul_mem (hXW hm) hfwW
  · have hm : y * w⁻¹ * (f w)⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by simp only [ncc_entry_mul, ncc_entry_inv, d2]; ring,
        by simp only [ncc_entry_mul, ncc_entry_inv, d1]; ring,
        Y.mul_mem (Y.mul_mem hy (Y.inv_mem hwY)) (Y.inv_mem hfwY)⟩
    simpa [mul_assoc] using W.mul_mem (hXW hm) (W.mul_mem hfwW hwW)

private theorem ncc_cf_one (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j : Fin 3)
    (hY : IsActsInv acts Y) (hX : IsActsInv acts (nccCut Y i j)) (y : AdjAmb) (hy : y ∈ Y)
    (hyij : Multiplicative.toAdd y i j ≠ 0) : IsChiefFactorUnder acts (nccCut Y i j) Y :=
  ⟨SetLike.lt_iff_le_and_exists.2 ⟨fun _ hx => hx.2, y, hy, fun h => hyij h.1⟩, hX, hY,
    ncc_chief_one acts Y i j⟩

private theorem ncc_cf_two (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j k l : Fin 3)
    (hhom : ∀ f ∈ acts, ∀ a b, f (a * b) = f a * f b)
    (hY : IsActsInv acts Y) (hX : IsActsInv acts (nccCut (nccCut Y i j) k l))
    (hwit : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Y, Multiplicative.toAdd r i j = a ∧
      Multiplicative.toAdd r k l = b ∧ ∃ f ∈ acts,
        ¬ (Multiplicative.toAdd (f r) i j = 0 ∧ Multiplicative.toAdd (f r) k l = 0) ∧
        ¬ (Multiplicative.toAdd (f r) i j = a ∧ Multiplicative.toAdd (f r) k l = b)) :
    IsChiefFactorUnder acts (nccCut (nccCut Y i j) k l) Y := by
  refine ⟨SetLike.lt_iff_le_and_exists.2 ⟨fun _ hx => hx.2.2, ?_⟩, hX, hY,
    ncc_chief_two acts Y i j k l hhom hX hwit⟩
  obtain ⟨r, hr, hra, -, -⟩ := hwit 1 0 (by decide)
  exact ⟨r, hr, fun h => absurd (h.2.1.symm.trans hra) (by decide)⟩

private theorem ncc_central {G : Subgroup (GL (Fin 3) (ZMod 2))} {Y : Subgroup AdjAmb} {i j : Fin 3}
    (hY : ∀ g ∈ G, ∀ y ∈ Y, adjAmbAct g y ∈ Y)
    (hX : ∀ g ∈ G, ∀ y ∈ nccCut Y i j, adjAmbAct g y ∈ nccCut Y i j) :
    ∀ f ∈ nccActs G, ∀ u ∈ Y, f u * u⁻¹ ∈ nccCut Y i j := by
  rintro f ⟨g, hg, rfl⟩ u hu
  show adjAmbAct g u * u⁻¹ ∈ nccCut Y i j
  have hfu : adjAmbAct g u ∈ Y := hY g hg u hu
  refine ⟨?_, Y.mul_mem hfu (Y.inv_mem hu)⟩
  rcases ncc_z2 (Multiplicative.toAdd u i j) with h0 | h1
  · have := (hX g hg u ⟨h0, hu⟩).1
    rw [ncc_entry_mul, ncc_entry_inv, this, h0, neg_zero, add_zero]
  · rcases ncc_z2 (Multiplicative.toAdd (adjAmbAct g u) i j) with k0 | k1
    · exfalso
      have := (hX g⁻¹ (G.inv_mem hg) _ ⟨k0, hfu⟩).1
      rw [ncc_act_inv_act] at this
      rw [this] at h1
      exact absurd h1 (by decide)
    · rw [ncc_entry_mul, ncc_entry_inv, k1, h1]
      decide

private def nccSeq (S1 S2 S3 S4 : Subgroup AdjAmb) : ℕ → Subgroup AdjAmb
  | 0 => ⊥
  | 1 => S1
  | 2 => S2
  | 3 => S3
  | 4 => S4
  | _ => Adj3

private theorem ncc_chain (acts : Set (AdjAmb → AdjAmb)) (S1 S2 S3 S4 : Subgroup AdjAmb)
    (h0 : IsChiefFactorUnder acts ⊥ S1) (h1 : IsChiefFactorUnder acts S1 S2)
    (h2 : IsChiefFactorUnder acts S2 S3) (h3 : IsChiefFactorUnder acts S3 S4)
    (h4 : IsChiefFactorUnder acts S4 Adj3)
    (n0 : ∃ f ∈ acts, ∃ u ∈ S1, f u * u⁻¹ ∉ (⊥ : Subgroup AdjAmb))
    (c1 : ∀ f ∈ acts, ∀ u ∈ S2, f u * u⁻¹ ∈ S1)
    (n2 : ∃ f ∈ acts, ∃ u ∈ S3, f u * u⁻¹ ∉ S2)
    (c3 : ∀ f ∈ acts, ∀ u ∈ S4, f u * u⁻¹ ∈ S3)
    (n4 : ∃ f ∈ acts, ∃ u ∈ Adj3, f u * u⁻¹ ∉ S4) :
    NoncentralChiefCount acts Adj3 3 := by
  refine ⟨5, nccSeq S1 S2 S3 S4, rfl, rfl, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rw [Set.ncard_eq_three]
    refine ⟨0, 2, 4, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi, f, hf, u, hu, hfu⟩
      interval_cases i
      · exact Or.inl rfl
      · exact absurd (c1 f hf u hu) hfu
      · exact Or.inr (Or.inl rfl)
      · exact absurd (c3 f hf u hu) hfu
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨by norm_num, n0⟩
      · exact ⟨by norm_num, n2⟩
      · exact ⟨by norm_num, n4⟩

private def nccP23 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

private def nccT12 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

private theorem ncc_Lp_facts {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Lpt ![1, 0, 0]) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := by
  have h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![1, 0, 0] = ![1, 0, 0] :=
    hg ![1, 0, 0] (Set.mem_singleton _)
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

private theorem ncc_mem_Lp_of {g : GL (Fin 3) (ZMod 2)} (h0 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1)
    (h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0) : g ∈ Lpt ![1, 0, 0] := by
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2]

private theorem ncc_P23_mem : nccP23 ∈ Lpt ![1, 0, 0] := ncc_mem_Lp_of (by decide) (by decide) (by decide)

private theorem ncc_T12_mem : nccT12 ∈ Lpt ![1, 0, 0] := ncc_mem_Lp_of (by decide) (by decide) (by decide)

private abbrev nccLpD : Subgroup AdjAmb := nccCut (nccCut Adj3 1 0) 2 0
private abbrev nccLpC : Subgroup AdjAmb := nccCut nccLpD 0 0
private abbrev nccLpB : Subgroup AdjAmb := nccCut (nccCut nccLpC 1 2) 2 1
private abbrev nccLpA : Subgroup AdjAmb := nccCut nccLpB 1 1

private theorem ncc_Lp_bot : nccCut (nccCut nccLpA 0 1) 0 2 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨x02, x01, x11, x21, x12, x00, x20, x10, htr⟩ := hx
  have x22 : Multiplicative.toAdd x 2 2 = 0 := by
    rw [ncc_mem_Adj3, x00, x11, zero_add, zero_add] at htr; exact htr
  apply Multiplicative.toAdd.injective
  ext i j
  rw [toAdd_one, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> assumption

private theorem ncc_Lp_inv {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Lpt ![1, 0, 0]) :
    (∀ x ∈ nccLpD, adjAmbAct g x ∈ nccLpD) ∧ (∀ x ∈ nccLpC, adjAmbAct g x ∈ nccLpC) ∧
    (∀ x ∈ nccLpB, adjAmbAct g x ∈ nccLpB) ∧ (∀ x ∈ nccLpA, adjAmbAct g x ∈ nccLpA) := by
  obtain ⟨-, a10, a20⟩ := ncc_Lp_facts hg
  obtain ⟨-, b10, b20⟩ := ncc_Lp_facts ((Lpt ![1, 0, 0]).inv_mem hg)
  have h12 := ncc_AB g 1 2
  have h21 := ncc_AB g 2 1
  rw [Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide), a10, zero_mul, zero_add] at h12
  rw [Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), a20, zero_mul, zero_add] at h21
  have hD : ∀ x ∈ nccLpD, adjAmbAct g x ∈ nccLpD := by
    rintro x ⟨x20, x10, hx⟩
    refine ⟨?_, ?_, ncc_Adj3_inv g x hx⟩
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, b10, b20, x10, x20]
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a10, b10, b20, x10, x20]
  have hC : ∀ x ∈ nccLpC, adjAmbAct g x ∈ nccLpC := by
    rintro x ⟨x00, hxD⟩
    refine ⟨?_, hD x hxD⟩
    obtain ⟨x20, x10, -⟩ := hxD
    rw [ncc_toAdd_act, ncc_mul3]; simp [b10, b20, x00, x10, x20]
  have hB : ∀ x ∈ nccLpB, adjAmbAct g x ∈ nccLpB := by
    rintro x ⟨x21, x12, hxC⟩
    have hC' := hC x hxC
    obtain ⟨x00, x20, x10, htr⟩ := hxC
    have x22 : Multiplicative.toAdd x 2 2 = Multiplicative.toAdd x 1 1 := by
      rw [ncc_mem_Adj3, x00, zero_add] at htr; exact ncc_z2_eq htr
    refine ⟨?_, ?_, hC'⟩
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [a20, x00, x10, x20, x12, x21, x22, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 1 1) * h21
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [a10, x00, x10, x20, x12, x21, x22, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 1 1) * h12
  have hA : ∀ x ∈ nccLpA, adjAmbAct g x ∈ nccLpA := by
    rintro x ⟨x11, hxB⟩
    refine ⟨?_, hB x hxB⟩
    obtain ⟨x21, x12, x00, x20, x10, htr⟩ := hxB
    have x22 : Multiplicative.toAdd x 2 2 = 0 := by
      rw [ncc_mem_Adj3, x00, x11, zero_add, zero_add] at htr; exact htr
    rw [ncc_toAdd_act, ncc_mul3]
    simp [a10, x00, x10, x20, x11, x12, x21, x22]
  exact ⟨hD, hC, hB, hA⟩

private theorem ncc_Lp_w0 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLpA,
    Multiplicative.toAdd r 0 1 = a ∧ Multiplicative.toAdd r 0 2 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 0 1 = 0 ∧ Multiplicative.toAdd (f r) 0 2 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 1 = a ∧ Multiplicative.toAdd (f r) 0 2 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Lp_w2 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLpC,
    Multiplicative.toAdd r 1 2 = a ∧ Multiplicative.toAdd r 2 1 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 1 2 = 0 ∧ Multiplicative.toAdd (f r) 2 1 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 1 2 = a ∧ Multiplicative.toAdd (f r) 2 1 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Lp_w4 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Adj3,
    Multiplicative.toAdd r 1 0 = a ∧ Multiplicative.toAdd r 2 0 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 1 0 = 0 ∧ Multiplicative.toAdd (f r) 2 0 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 1 0 = a ∧ Multiplicative.toAdd (f r) 2 0 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_std_Lp : NoncentralChiefCount
    {f : AdjAmb → AdjAmb | ∃ g ∈ Lpt ![1, 0, 0], f = fun x => adjAmbAct g x} Adj3 3 := by
  show NoncentralChiefCount (nccActs (Lpt ![1, 0, 0])) Adj3 3
  have iAdj : IsActsInv (nccActs (Lpt ![1, 0, 0])) Adj3 :=
    ncc_inv_of fun g _ x hx => ncc_Adj3_inv g x hx
  have iD : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpD :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).1
  have iC : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpC :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.1
  have iB : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpB :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.2.1
  have iA : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpA :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.2.2
  have iBot : IsActsInv (nccActs (Lpt ![1, 0, 0])) (nccCut (nccCut nccLpA 0 1) 0 2) := by
    rw [ncc_Lp_bot]
    rintro f ⟨g, -, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    subst hu
    exact map_one _
  refine ncc_chain (nccActs (Lpt ![1, 0, 0])) nccLpA nccLpB nccLpC nccLpD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · rw [← ncc_Lp_bot]
    exact ncc_cf_two _ nccLpA 0 1 0 2 ncc_hom iA iBot ncc_Lp_w0
  · exact ncc_cf_one _ nccLpB 1 1 iB iA (Multiplicative.ofAdd !![0, 0, 0; 0, 1, 0; 0, 0, 1])
      (by decide) (by decide)
  · exact ncc_cf_two _ nccLpC 1 2 2 1 ncc_hom iC iB ncc_Lp_w2
  · exact ncc_cf_one _ nccLpD 0 0 iD iC (Multiplicative.ofAdd !![1, 0, 0; 0, 1, 0; 0, 0, 0])
      (by decide) (by decide)
  · exact ncc_cf_two _ Adj3 1 0 2 0 ncc_hom iAdj iD ncc_Lp_w4
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide,
      by rw [Subgroup.mem_bot]; decide⟩
  · exact ncc_central (fun _ hg => (ncc_Lp_inv hg).2.2.1) (fun _ hg => (ncc_Lp_inv hg).2.2.2)
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide⟩
  · exact ncc_central (fun _ hg => (ncc_Lp_inv hg).1) (fun _ hg => (ncc_Lp_inv hg).2.1)
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide⟩

private abbrev nccLlG : Subgroup (GL (Fin 3) (ZMod 2)) :=
  Lln (LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3)))

private def nccP12 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩

private def nccT01 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

private theorem ncc_Ll_facts {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ nccLlG) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 := by
  have h1 := (hg ![1, 0, 0] (by simp)).1
  have h2 := (hg ![0, 1, 0] (by simp)).1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

private theorem ncc_mem_Ll_of {g : GL (Fin 3) (ZMod 2)}
    (h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0)
    (h3 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0)
    (h4 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0) :
    g ∈ nccLlG := by
  intro v hv
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply] at hv ⊢
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h3, h4, hv, zero_mul,
    mul_zero, add_zero, and_self]

private theorem ncc_P12_mem : nccP12 ∈ nccLlG :=
  ncc_mem_Ll_of (by decide) (by decide) (by decide) (by decide)

private theorem ncc_T01_mem : nccT01 ∈ nccLlG :=
  ncc_mem_Ll_of (by decide) (by decide) (by decide) (by decide)

private abbrev nccLl4 : Subgroup AdjAmb := nccCut (nccCut Adj3 2 0) 2 1
private abbrev nccLl3 : Subgroup AdjAmb := nccCut nccLl4 2 2
private abbrev nccLl2 : Subgroup AdjAmb := nccCut (nccCut nccLl3 0 1) 1 0
private abbrev nccLl1 : Subgroup AdjAmb := nccCut nccLl2 0 0

private theorem ncc_Ll_bot : nccCut (nccCut nccLl1 0 2) 1 2 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨x12, x02, x00, x10, x01, x22, x21, x20, htr⟩ := hx
  have x11 : Multiplicative.toAdd x 1 1 = 0 := by
    rw [ncc_mem_Adj3, x00, x22, zero_add, add_zero] at htr; exact htr
  apply Multiplicative.toAdd.injective
  ext i j
  rw [toAdd_one, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> assumption

private theorem ncc_Ll_inv {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ nccLlG) :
    (∀ x ∈ nccLl4, adjAmbAct g x ∈ nccLl4) ∧ (∀ x ∈ nccLl3, adjAmbAct g x ∈ nccLl3) ∧
    (∀ x ∈ nccLl2, adjAmbAct g x ∈ nccLl2) ∧ (∀ x ∈ nccLl1, adjAmbAct g x ∈ nccLl1) := by
  obtain ⟨a20, a21⟩ := ncc_Ll_facts hg
  obtain ⟨b20, b21⟩ := ncc_Ll_facts (nccLlG.inv_mem hg)
  have h01 := ncc_AB g 0 1
  have h10 := ncc_AB g 1 0
  rw [Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide), b21, mul_zero, add_zero] at h01
  rw [Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide), b20, mul_zero, add_zero] at h10
  have h4 : ∀ x ∈ nccLl4, adjAmbAct g x ∈ nccLl4 := by
    rintro x ⟨x21, x20, hx⟩
    refine ⟨?_, ?_, ncc_Adj3_inv g x hx⟩
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, b21, x20, x21]
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, b20, x20, x21]
  have h3 : ∀ x ∈ nccLl3, adjAmbAct g x ∈ nccLl3 := by
    rintro x ⟨x22, hx4⟩
    refine ⟨?_, h4 x hx4⟩
    obtain ⟨x21, x20, -⟩ := hx4
    rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, x20, x21, x22]
  have h2 : ∀ x ∈ nccLl2, adjAmbAct g x ∈ nccLl2 := by
    rintro x ⟨x10, x01, hx3⟩
    have h3' := h3 x hx3
    obtain ⟨x22, x21, x20, htr⟩ := hx3
    have x11 : Multiplicative.toAdd x 1 1 = Multiplicative.toAdd x 0 0 := by
      rw [ncc_mem_Adj3, x22, add_zero] at htr; exact ncc_z2_eq htr
    refine ⟨?_, ?_, h3'⟩
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [b20, x10, x20, x01, x21, x22, x11, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 0 0) * h10
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [b21, x10, x20, x01, x21, x22, x11, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 0 0) * h01
  have h1 : ∀ x ∈ nccLl1, adjAmbAct g x ∈ nccLl1 := by
    rintro x ⟨x00, hx2⟩
    refine ⟨?_, h2 x hx2⟩
    obtain ⟨x10, x01, x22, x21, x20, htr⟩ := hx2
    have x11 : Multiplicative.toAdd x 1 1 = 0 := by
      rw [ncc_mem_Adj3, x00, x22, zero_add, add_zero] at htr; exact htr
    rw [ncc_toAdd_act, ncc_mul3]
    simp [b20, x00, x10, x20, x01, x11, x21]
  exact ⟨h4, h3, h2, h1⟩

private theorem ncc_Ll_w0 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLl1,
    Multiplicative.toAdd r 0 2 = a ∧ Multiplicative.toAdd r 1 2 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 0 2 = 0 ∧ Multiplicative.toAdd (f r) 1 2 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 2 = a ∧ Multiplicative.toAdd (f r) 1 2 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Ll_w2 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLl3,
    Multiplicative.toAdd r 0 1 = a ∧ Multiplicative.toAdd r 1 0 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 0 1 = 0 ∧ Multiplicative.toAdd (f r) 1 0 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 1 = a ∧ Multiplicative.toAdd (f r) 1 0 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Ll_w4 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Adj3,
    Multiplicative.toAdd r 2 0 = a ∧ Multiplicative.toAdd r 2 1 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 2 0 = 0 ∧ Multiplicative.toAdd (f r) 2 1 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 2 0 = a ∧ Multiplicative.toAdd (f r) 2 1 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_std_Ll : NoncentralChiefCount
    {f : AdjAmb → AdjAmb | ∃ g ∈ Lln (LinearMap.ker (LinearMap.proj (R := ZMod 2)
      (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3))), f = fun x => adjAmbAct g x} Adj3 3 := by
  show NoncentralChiefCount (nccActs nccLlG) Adj3 3
  have iAdj : IsActsInv (nccActs nccLlG) Adj3 :=
    ncc_inv_of fun g _ x hx => ncc_Adj3_inv g x hx
  have i4 : IsActsInv (nccActs nccLlG) nccLl4 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).1
  have i3 : IsActsInv (nccActs nccLlG) nccLl3 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.1
  have i2 : IsActsInv (nccActs nccLlG) nccLl2 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.2.1
  have i1 : IsActsInv (nccActs nccLlG) nccLl1 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.2.2
  have iBot : IsActsInv (nccActs nccLlG) (nccCut (nccCut nccLl1 0 2) 1 2) := by
    rw [ncc_Ll_bot]
    rintro f ⟨g, -, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    subst hu
    exact map_one _
  refine ncc_chain (nccActs nccLlG) nccLl1 nccLl2 nccLl3 nccLl4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← ncc_Ll_bot]
    exact ncc_cf_two _ nccLl1 0 2 1 2 ncc_hom i1 iBot ncc_Ll_w0
  · exact ncc_cf_one _ nccLl2 0 0 i2 i1 (Multiplicative.ofAdd !![1, 0, 0; 0, 1, 0; 0, 0, 0])
      (by decide) (by decide)
  · exact ncc_cf_two _ nccLl3 0 1 1 0 ncc_hom i3 i2 ncc_Ll_w2
  · exact ncc_cf_one _ nccLl4 2 2 i4 i3 (Multiplicative.ofAdd !![0, 0, 0; 0, 1, 0; 0, 0, 1])
      (by decide) (by decide)
  · exact ncc_cf_two _ Adj3 2 0 2 1 ncc_hom iAdj i4 ncc_Ll_w4
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide,
      by rw [Subgroup.mem_bot]; decide⟩
  · exact ncc_central (fun _ hg => (ncc_Ll_inv hg).2.2.1) (fun _ hg => (ncc_Ll_inv hg).2.2.2)
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide⟩
  · exact ncc_central (fun _ hg => (ncc_Ll_inv hg).1) (fun _ hg => (ncc_Ll_inv hg).2.1)
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide⟩

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

private theorem mem_Lpt_conj_iff6 (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (k : GL (Fin 3) (ZMod 2)) :
    k ∈ Lpt e1 ↔ c * k * c⁻¹ ∈ Lpt p := by
  refine ⟨mem_Lpt_conj6 c p hpc k, fun h => ?_⟩
  rw [mem_Lpt] at h ⊢
  intro v hv
  rw [Set.mem_singleton_iff.1 hv]
  have h1 := h p (Set.mem_singleton p)
  rw [← hpc, mulVec_conj6, inv_mulVec_mulVec] at h1
  have h2 := congrArg ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec h1
  rwa [inv_mulVec_mulVec, inv_mulVec_mulVec] at h2

private theorem H63_part3 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    NoncentralChiefCount {f | ∃ g ∈ Lpt p, f = fun x => adjAmbAct g x} Adj3 3 ∧
      NoncentralChiefCount {f | ∃ g ∈ Lln l, f = fun x => adjAmbAct g x} Adj3 3 := by
  obtain ⟨c, -, -, hpc, hline⟩ := conj_data6 T p l hyp
  exact ⟨ncc_transport c (Lpt e1) (Lpt p) (fun g => mem_Lpt_conj_iff6 c p hpc g) 3 CFSG.ASVolI.ChH.ncc_std_Lp,
    ncc_transport c (Lln line0) (Lln l) (fun g => mem_Lln_conj c l hline g) 3 CFSG.ASVolI.ChH.ncc_std_Ll⟩

theorem as_H_6_3 : H_6_3 :=
  ⟨H63_part1, ⟨H63_part2a, H63_part2b⟩, fun T p l hyp =>
    ⟨H63_part3 T p l hyp, H63_part4 T p l hyp, H63_part5 T p l hyp⟩⟩


namespace ArtH62

section Art

variable {G : Type*} [Group G] {M : Type*} [CommGroup M]


private structure Setup (ρ : G →* MulAut M) (U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M) : Prop where
  i₁ : ∀ g, ∀ u ∈ U₁, ρ g u ∈ U₁
  i₂ : ∀ g, ∀ u ∈ U₂, ρ g u ∈ U₂
  i₃ : ∀ g, ∀ u ∈ U₃, ρ g u ∈ U₃
  i₄ : ∀ g, ∀ u ∈ U₄, ρ g u ∈ U₄
  hsum : U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ = ⊤
  h₁ : U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) = ⊥
  h₂ : U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) = ⊥
  h₃ : U₃ ⊓ (U₁ ⊔ U₂ ⊔ U₄) = ⊥
  h₄ : U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) = ⊥
  hU₁ : U₁ ≠ ⊥
  hU₄ : U₄ ≠ ⊥
  s₁ : ∀ W : Subgroup M, W ≤ U₁ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U₁
  s₄ : ∀ W : Subgroup M, W ≤ U₄ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U₄
  k₂ : K₂ ≤ U₂
  k₂ne : K₂ ≠ ⊥
  k₂max : IsMaxSub ρ U₂ K₂
  soc₂ : ∀ W : Subgroup M, W ≤ U₂ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W ≠ ⊥ → K₂ ≤ W
  k₃ : K₃ ≤ U₃
  k₃ne : K₃ ≠ ⊥
  k₃max : IsMaxSub ρ U₃ K₃
  soc₃ : ∀ W : Subgroup M, W ≤ U₃ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W ≠ ⊥ → K₃ ≤ W

variable {ρ : G →* MulAut M} {U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M}


section Art2

variable {ρ : G →* MulAut M} {U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M}


end Art2

end Art

end ArtH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private abbrev Fl : Type := {p : V3 × V3 // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ⬝ᵥ p.1 = 0}

private instance : Fintype Fl := Subtype.fintype _

private def gPt (g : GL (Fin 3) (ZMod 2)) (x : V3) : V3 :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x

private def gDu (g : GL (Fin 3) (ZMod 2)) (a : V3) : V3 :=
  ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose.mulVec a

private theorem gPt_mul (g h : GL (Fin 3) (ZMod 2)) (x : V3) : gPt (g * h) x = gPt g (gPt h x) := by
  unfold gPt
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem gPt_one (x : V3) : gPt 1 x = x := by
  unfold gPt
  simp

private theorem gPt_zero (g : GL (Fin 3) (ZMod 2)) : gPt g 0 = 0 := by
  unfold gPt
  simp

private theorem gDu_mul (g h : GL (Fin 3) (ZMod 2)) (a : V3) : gDu (g * h) a = gDu g (gDu h a) := by
  unfold gDu
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

private theorem gDu_one (a : V3) : gDu 1 a = a := by
  unfold gDu
  simp

private theorem gDu_zero (g : GL (Fin 3) (ZMod 2)) : gDu g 0 = 0 := by
  unfold gDu
  simp

private theorem dot_gDu_gPt (g : GL (Fin 3) (ZMod 2)) (a x : V3) :
    gDu g a ⬝ᵥ gPt g x = a ⬝ᵥ x := by
  unfold gDu gPt
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


private theorem gPt_ne (g : GL (Fin 3) (ZMod 2)) {x : V3} (hx : x ≠ 0) : gPt g x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg (gPt g⁻¹) h
  rwa [← gPt_mul, inv_mul_cancel, gPt_one, gPt_zero] at h'

private theorem gDu_ne (g : GL (Fin 3) (ZMod 2)) {a : V3} (ha : a ≠ 0) : gDu g a ≠ 0 := by
  intro h
  apply ha
  have h' := congrArg (gDu g⁻¹) h
  rwa [← gDu_mul, inv_mul_cancel, gDu_one, gDu_zero] at h'

private instance flagAct : MulAction (GL (Fin 3) (ZMod 2)) Fl where
  smul g φ := ⟨(gPt g φ.1.1, gDu g φ.1.2),
    gPt_ne g φ.2.1, gDu_ne g φ.2.2.1, by rw [dot_gDu_gPt]; exact φ.2.2.2⟩
  one_smul φ := Subtype.ext (Prod.ext (gPt_one _) (gDu_one _))
  mul_smul g h φ := Subtype.ext (Prod.ext (gPt_mul g h _) (gDu_mul g h _))


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


private def mkInvol (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : M * M = 1) : GL (Fin 3) (ZMod 2) :=
  ⟨M, M, h, h⟩

private def gH : GL (Fin 3) (ZMod 2) := mkInvol !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide)
private def gT : GL (Fin 3) (ZMod 2) := mkInvol !![1, 1, 0; 0, 1, 0; 0, 0, 1] (by decide)

private def d2 (x : V3) : ZMod 2 := x 1 * (1 + x 2)


private def d12 (x : V3) : ZMod 2 :=
  (if x = ![1, 0, 0] then 1 else 0) + (if x = ![0, 1, 0] then 1 else 0)

private theorem I3 : ∀ x : V3, d12 x = d2 (gPt gH⁻¹ x) := by decide


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix


end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

section Transport

variable {G : Type*} [Group G] {X Y : Type*} [CommGroup X] [CommGroup Y]
  {ρ : G →* MulAut X} {ρ' : G →* MulAut Y}


end Transport


attribute [local instance] cosetFintype


private noncomputable def cosetFintypeLln (l : Submodule (ZMod 2) V3) :
    Fintype (GL (Fin 3) (ZMod 2) ⧸ Lln l) :=
  Fintype.ofFinite _

attribute [local instance] cosetFintypeLln


end FlagH62


end CFSG.ASVolI
