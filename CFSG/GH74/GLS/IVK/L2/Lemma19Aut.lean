module

public import CFSG.GH74.GLS.IVK.L2.SLAut
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.ABGDGroups

section Aut19

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def thetaEquiv (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    PGammaL2 F ≃* MulAut (PSL2 F) :=
  have hK := isOddPrimePower_card_of_odd hodd
  haveI : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hK h3)
    ⟨pGammaL2ToMulAutPSL2_injective F hK h3,
      pGammaL2ToMulAutPSL2_surjective F (card_eq_ringChar_pow (F := F)).choose_spec.2 hK h3⟩

theorem thetaEquiv_inl (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (g : PGL2 F) :
    thetaEquiv hodd h3 (SemidirectProduct.inl g) =
      pgl2InnerAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3 g := by
  show pGammaL2ToMulAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3 (SemidirectProduct.inl g) = _
  rw [pGammaL2ToMulAutPSL2_inl]

theorem thetaEquiv_inr (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (σ : F ≃+* F) :
    thetaEquiv hodd h3 (SemidirectProduct.inr σ) = psl2FieldAut F σ := by
  show pGammaL2ToMulAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3 (SemidirectProduct.inr σ) = _
  rw [pGammaL2ToMulAutPSL2_inr]

@[expose] noncomputable def psl2AutHom :
    MulAut (SpecialLinearGroup (Fin 2) F) →* MulAut (PSL2 F) where
  toFun := psl2MulAutOf
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H b => rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with | H b => rfl

theorem psl2MulAutOf_conj (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (j : SpecialLinearGroup (Fin 2) F) :
    psl2MulAutOf (MulAut.conj j) = pgl2InnerAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk' _ j)) := by
  ext x
  induction x using QuotientGroup.induction_on with | H b => ?_
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply]
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (QuotientGroup.mk' _ (j * b * j⁻¹)) = _
  have e1 : (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) (j * b * j⁻¹)) =
      QuotientGroup.mk' _ j * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ j)⁻¹ := by
    simp
  rw [e1, map_mul, map_mul, map_inv]
  rfl


section Act

variable {H : Type} [Group H] {Khat : Subgroup H} [Khat.Normal]

@[expose] noncomputable def actHom (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) :
    H →* MulAut (SpecialLinearGroup (Fin 2) F) :=
  (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal

omit [Finite F] in
theorem actHom_apply (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) (h : H) (κ : ↥Khat) :
    actHom φ h (φ κ) = φ (MulAut.conjNormal h κ) := by
  simp [actHom]

omit [Finite F] in
theorem actHom_coe (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) (κ : ↥Khat) :
    actHom φ (κ : H) = MulAut.conj (φ κ) := by
  ext b
  obtain ⟨y, rfl⟩ := φ.surjective b
  rw [actHom_apply, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

@[expose] noncomputable def lam (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) : H →* PGammaL2 F :=
  (thetaEquiv hodd h3).symm.toMonoidHom.comp (psl2AutHom.comp (actHom φ))


end Act

section Psi

variable {H : Type} [Group H] {Khat : Subgroup H} [Khat.Normal]

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass)

@[expose] noncomputable def psiH (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) : H →* SquareClass F × (F ≃+* F) :=
  ((pGammaL2DetClass F (isOddPrimePower_card_of_odd hodd)).comp (lam hodd h3 φ)).prod
    (SemidirectProduct.rightHom.comp (lam hodd h3 φ))


end Psi


end Aut19


section GrpCyc

variable {Sq Γ : Type*} [Group Sq] [Group Γ] [IsCyclic Γ] [Finite Γ]

theorem isCyclic_of_sign (hSq : Nat.card Sq = 2) (A : Subgroup (Sq × Γ))
    (hA : ∀ a ∈ A, Even (orderOf a.2) → a.1 = 1) : IsCyclic A := by
  classical
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := Γ)).is_comm.comm a b
  by_cases hall : ∀ a ∈ A, a.1 = 1
  ·
    refine isCyclic_of_injective ((MonoidHom.snd Sq Γ).comp A.subtype) ?_
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · rw [hall a a.2, hall b b.2]
    · exact hab
  · obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A, a.1 ≠ 1 := by
      by_contra h
      exact hall (fun a ha => by
        by_contra h'
        exact h ⟨a, ha, h'⟩)
    have ha₀odd : Odd (orderOf a₀.2) := by
      by_contra h
      exact ha₀1 (hA a₀ ha₀ (Nat.not_odd_iff_even.1 h))
    set B : Subgroup Γ := A.map (MonoidHom.snd Sq Γ) with hB
    have hBodd : Odd (Nat.card B) := by
      by_contra h
      have h2 : 2 ∣ Nat.card B := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 h2
      obtain ⟨a, haA, hab⟩ := b.2
      have hb2 : orderOf a.2 = 2 := by
        have : orderOf (b : Γ) = 2 := by rw [Subgroup.orderOf_coe, hb]
        rw [← this, ← hab]
        rfl
      have h1 : a.1 = 1 := hA a haA (by rw [hb2]; exact even_two)
      have hcop : (orderOf a.2).Coprime (orderOf a₀.2) := by
        rw [hb2]
        exact (Nat.coprime_two_left).2 ha₀odd
      have hord : orderOf (a.2 * a₀.2) = 2 * orderOf a₀.2 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hcomm _ _) hcop, hb2]
      have h3 : (a * a₀).1 = 1 := hA (a * a₀) (A.mul_mem haA ha₀) (by
        show Even (orderOf (a.2 * a₀.2))
        rw [hord]
        exact even_two_mul _)
      apply ha₀1
      have : (a * a₀).1 = a.1 * a₀.1 := rfl
      rw [this, h1, one_mul] at h3
      exact h3
    have : IsCyclic B := inferInstance
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSqcyc : IsCyclic Sq := isCyclic_of_prime_card (p := 2) hSq
    have hprod : IsCyclic (Sq × B) := by
      rw [Group.isCyclic_prod_iff]
      refine ⟨hSqcyc, inferInstance, ?_⟩
      rw [hSq]
      exact (Nat.coprime_two_left).2 hBodd
    refine isCyclic_of_injective (G' := Sq × B)
      ((MonoidHom.fst Sq Γ |>.comp A.subtype).prod
        (MonoidHom.codRestrict ((MonoidHom.snd Sq Γ).comp A.subtype) B (fun a => ⟨a, a.2, rfl⟩))) ?_
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · have h1 := congrArg Prod.fst hab
      exact h1
    · have h2 := congrArg (fun p : Sq × B => (p.2 : Γ)) hab
      exact h2

end GrpCyc

section Main19a


end Main19a

end CFSG.GH74.GLS.IVK
