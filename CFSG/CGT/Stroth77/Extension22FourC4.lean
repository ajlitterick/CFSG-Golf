module

public import CFSG.CGT.Stroth77.Extension22FourProof

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem pow_four_mem_fourB {τ : StrothTypeIndex} (D : StrothTypeData B τ) (b : B) :
    b ^ 4 ∈ fourB D := by
  rw [mem_fourB_iff]
  exact ⟨D.ec b, by rw [ec_pow]⟩

@[expose] noncomputable def conjByHom (g : S) (hg : g ∈ Subgroup.normalizer C) : C →* C where
  toFun x := conjBy hg x
  map_one' := by
    ext
    simp [conjBy]
  map_mul' x y := by
    ext
    simp [conjBy]
    group

@[simp]
theorem conjByHom_apply (g : S) (hg : g ∈ Subgroup.normalizer C) (x : C) :
    conjByHom g hg x = conjBy hg x := rfl

theorem conjByHom_mul (g h : S) (hg : g ∈ Subgroup.normalizer C)
    (hh : h ∈ Subgroup.normalizer C) :
    conjByHom (g * h) (Subgroup.mul_mem _ hg hh) =
      (conjByHom h hh).comp (conjByHom g hg) := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy]
  group

theorem conjByHom_mul_eq {g h g' h' : S}
    (hg : g ∈ Subgroup.normalizer C) (hh : h ∈ Subgroup.normalizer C)
    (hg' : g' ∈ Subgroup.normalizer C) (hh' : h' ∈ Subgroup.normalizer C)
    (hgh : g * h = g' * h') :
    conjByHom (g * h) (Subgroup.mul_mem _ hg hh) =
      conjByHom (g' * h') (Subgroup.mul_mem _ hg' hh') := by
  ext x
  simp only [conjByHom_apply, conjBy]
  rw [hgh]

theorem conjByHom_comp_inv (g : S) (hg : g ∈ Subgroup.normalizer C) :
    (conjByHom g hg).comp (conjByHom g⁻¹ (Subgroup.inv_mem _ hg)) = MonoidHom.id C := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy, MonoidHom.id_apply]
  group

theorem conjByHom_inv_comp (g : S) (hg : g ∈ Subgroup.normalizer C) :
    (conjByHom g⁻¹ (Subgroup.inv_mem _ hg)).comp (conjByHom g hg) = MonoidHom.id C := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy, MonoidHom.id_apply]
  group

section QuotientAction

variable [hN : (B.subgroupOf C).Normal]

noncomputable def conjByQuotientMap (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    (C ⧸ B.subgroupOf C) →* (C ⧸ B.subgroupOf C) :=
  QuotientGroup.map (B.subgroupOf C) (B.subgroupOf C) (conjByHom g hgC) (by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [conjByHom_apply, conjBy]
    exact (Subgroup.mem_normalizer_iff''.mp hgB (x : S)).mp hx)

@[simp]
theorem conjByQuotientMap_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjByQuotientMap g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjByHom g hgC x) :=
  QuotientGroup.map_mk _ _ _ _ x

theorem conjByQuotientMap_left_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.LeftInverse
      (conjByQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjByQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjByQuotientMap_mk, conjByQuotientMap_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_inv_comp g hgC) x
    simpa using h

theorem conjByQuotientMap_right_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.RightInverse
      (conjByQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjByQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjByQuotientMap_mk, conjByQuotientMap_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_comp_inv g hgC) x
    simpa using h

noncomputable def conjByAutQuotient (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) : MulAut (C ⧸ B.subgroupOf C) :=
  MulEquiv.ofBijective (conjByQuotientMap g hgC hgB)
    ⟨(conjByQuotientMap_left_inv g hgC hgB).injective,
     (conjByQuotientMap_right_inv g hgC hgB).surjective⟩

@[simp]
theorem conjByAutQuotient_apply_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjByAutQuotient g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjByHom g hgC x) := by
  show conjByQuotientMap g hgC hgB (QuotientGroup.mk x) = _
  exact conjByQuotientMap_mk g hgC hgB x

theorem conjByAutQuotient_one :
    conjByAutQuotient (B := B) (C := C) (1 : S) (Subgroup.one_mem _) (Subgroup.one_mem _) = 1 := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [conjByAutQuotient_apply_mk, MulAut.one_apply, conjByHom_apply, conjBy,
      Subgroup.coe_mk, inv_one, one_mul, mul_one]

theorem conjByAutQuotient_mul (g h : S) (hgC : g ∈ Subgroup.normalizer C)
    (hhC : h ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hhB : h ∈ Subgroup.normalizer B) :
    conjByAutQuotient (g * h) (Subgroup.mul_mem _ hgC hhC)
        (Subgroup.mul_mem _ hgB hhB) =
      conjByAutQuotient h hhC hhB * conjByAutQuotient g hgC hgB := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, conjByAutQuotient_apply_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_mul g h hgC hhC) x
    simpa using h

theorem conjByAutQuotient_pow (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (n : ℕ) :
    conjByAutQuotient (g ^ n) (Subgroup.pow_mem _ hgC n) (Subgroup.pow_mem _ hgB n) =
      (conjByAutQuotient g hgC hgB) ^ n := by
  induction n with
  | zero =>
    simpa using (conjByAutQuotient_one (B := B) (C := C) (S := S))
  | succ n ih =>
    calc conjByAutQuotient (g ^ (n + 1)) (Subgroup.pow_mem _ hgC (n + 1))
          (Subgroup.pow_mem _ hgB (n + 1))
        = conjByAutQuotient g hgC hgB * conjByAutQuotient (g ^ n)
            (Subgroup.pow_mem _ hgC n) (Subgroup.pow_mem _ hgB n) := by
          simpa only [pow_succ] using conjByAutQuotient_mul (g ^ n) g
            (Subgroup.pow_mem _ hgC n) hgC (Subgroup.pow_mem _ hgB n) hgB
      _ = conjByAutQuotient g hgC hgB * (conjByAutQuotient g hgC hgB) ^ n := by rw [ih]
      _ = (conjByAutQuotient g hgC hgB) ^ (n + 1) := by rw [pow_succ']

theorem exists_mul_of_conjByAutQuotient_eq_one [IsMulCommutative C]
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hA : conjByAutQuotient g hgC hgB = 1) (x : C) :
    ∃ b : B, g⁻¹ * (x : S) * g = (x : S) * (b : S) := by
  classical
  let aC : C := conjByHom g hgC x
  have haC : (aC : S) = g⁻¹ * (x : S) * g := by
    simp [aC, conjByHom, conjBy]
  have hmk : QuotientGroup.mk' (B.subgroupOf C) aC = QuotientGroup.mk' (B.subgroupOf C) x := by
    have h := congrArg (fun σ : MulAut (C ⧸ B.subgroupOf C) =>
      σ (QuotientGroup.mk' (B.subgroupOf C) x)) hA
    simpa [aC, conjByAutQuotient_apply_mk] using h
  have hbH : aC⁻¹ * x ∈ B.subgroupOf C := QuotientGroup.eq.mp hmk
  have hb : aC * x⁻¹ ∈ B.subgroupOf C := by
    have h' : aC * x⁻¹ = (aC⁻¹ * x)⁻¹ := by
      calc aC * x⁻¹ = x⁻¹ * aC := mul_comm' _ _
        _ = (aC⁻¹ * x)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [h']
    exact (B.subgroupOf C).inv_mem hbH
  refine ⟨⟨aC * x⁻¹, hb⟩, ?_⟩
  change g⁻¹ * (x : S) * g = (x : S) * ((aC * x⁻¹ : C) : S)
  rw [← haC]
  have hCeq : aC = x * (aC * x⁻¹) := by
    calc aC = aC * (x⁻¹ * x) := by group
      _ = (aC * x⁻¹) * x := by group
      _ = x * (aC * x⁻¹) := by rw [mul_comm' (aC * x⁻¹) x]
  simpa using congrArg (fun y : C => (y : S)) hCeq

end QuotientAction

theorem conjBy_pow_four_mem_fourB
    {τ : StrothTypeIndex} {D : StrothTypeData B τ} {g : S}
    (hgB : g ∈ Subgroup.normalizer B) (z : C) (b : B)
    (hz4B : (z : S) ^ 4 ∈ B)
    (hgb : g⁻¹ * (z : S) * g = (z : S) * (b : S))
    (hcomm : Commute (z : S) (b : S)) :
    conjBy hgB (⟨(z : S) ^ 4, hz4B⟩ : B) * (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D := by
  let yB : B := ⟨(z : S) ^ 4, hz4B⟩
  have hconjpow : g⁻¹ * (z : S) ^ 4 * g = (z : S) ^ 4 * (b : S) ^ 4 := by
    have hpow : g⁻¹ * (z : S) ^ 4 * g = (g⁻¹ * (z : S) * g) ^ 4 := by
      simpa using (conj_pow (a := g⁻¹) (b := (z : S)) (i := 4)).symm
    rw [hpow, hgb]
    exact hcomm.mul_pow 4
  have hconj : conjBy hgB yB * yB⁻¹ = b ^ 4 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, conjBy, Subgroup.coe_mk]
    change (g⁻¹ * (yB : S) * g) * (yB : S)⁻¹ = (b : S) ^ 4
    have hy : (yB : S) = (z : S) ^ 4 := rfl
    rw [hy, hconjpow, (hcomm.pow_pow 4 4).eq]
    group
  rw [hconj]
  exact pow_four_mem_fourB D b


end CFSG.CGT.Stroth77
