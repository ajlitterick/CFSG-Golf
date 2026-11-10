module

public import CFSG.Quasithin.Vol2.Ch11SecBE22NParam

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E22N

@[expose] def TypeOneOdd (Y : Type) [Group Y] : Prop :=
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 Y

theorem TypeOneOdd.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOneOdd Y') : TypeOneOdd Y := by
  rcases h with ⟨p, f, hp, hp2, h5, h⟩ | ⟨s, p, hp, hp2, h⟩
  · exact Or.inl ⟨p, f, hp, hp2, h5, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩
  · refine Or.inr ⟨s, p, hp, hp2, ?_⟩
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

theorem TypeOne.cases {Y : Type} [Group Y] (h : TypeOne Y) : TypeLie 1 Y ∨ TypeOneOdd Y := by
  rcases h with h | h | h | h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem typeOne_isoInv : IsoInv (fun X _ => TypeOne X) := by
  intro A B _ _ e h
  exact TypeOne.of_mulEquiv e h

@[expose] def TypeK : GrpPred := fun X _ => (∃ n : ℕ, TypeLie n X) ∨ TypeOne X

theorem typeK_isoInv : IsoInv TypeK := by
  intro A B _ _ e h
  rcases h with ⟨n, hn⟩ | h
  · exact Or.inl ⟨n, TypeLie.of_mulEquiv e hn⟩
  · exact Or.inr (TypeOne.of_mulEquiv e h)

@[expose] def E111ForQn (Q : GrpPred) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ASInputs.E111Hyp G n → SecAll G Q →
    E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)


variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_star {Q : GrpPred} {n : ℕ} (hQ : IsoInv Q) (h111 : E111ForQn Q n)
    {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hJs : Group.IsSolvable ↥(kerIn M H))
    (hKs : IsSimpleGroup ↥(E2.star M H K)) (hKK : Q ↥(E2.star M H K))
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Nonempty (X ≃* ↥(E2.star M H K)) → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
        (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n)
    (hRH : R ≤ H) : E1.nParam (R ⊔ oTwoUpper H) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := R ⊔ oTwoUpper H with hYdef
  have hYH : Y ≤ H := sup_le hRH (oTwoUpper_le H)
  have hKH : K ≤ H := by rw [hHK]; exact le_sup_left
  set J' := (kerIn M H).subgroupOf H with hJ'
  set π : ↥H →* E2.StarQuot M H := QuotientGroup.mk' J' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J'
  set Ks : Subgroup (E2.StarQuot M H) := (K.subgroupOf H).map π with hKsdef
  have hKs' : IsSimpleGroup ↥Ks := hKs
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hKab : ∃ a b : ↥Ks, a * b ≠ b * a :=
    nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hKsn : Ks.IsSubnormal := by
    have h1 := A4.subnormal_comap H.subtype hKc.2.2.1
    have h2 : H.comap H.subtype = ⊤ := Subgroup.subgroupOf_self H
    rw [h2] at h1
    exact (isSubnormal_of_open h1 Subgroup.IsSubnormal.top).map hπs
  set Ts : Subgroup (E2.StarQuot M H) := (T.subgroupOf H).map π with hTsdef
  have hTs : IsPGroup 2 ↥Ts := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map π
  have hKT : Ks ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [hKsdef, hTsdef, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set Os : Subgroup (E2.StarQuot M H) := ((oTwoUpper H).subgroupOf H).map π with hOsdef
  have hOn : Os.Normal := by
    have : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H)
    exact this.map π hπs
  have hKO : Ks ≤ Os := Subgroup.map_mono fun x hx =>
    B1Red.perfect_le_oTwoUpper' hKH hKp (Subgroup.mem_subgroupOf.mp hx)
  set f : ↥Y →* E2.StarQuot M H := π.comp (Subgroup.inclusion hYH) with hf
  have hOY : Os ≤ f.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o, le_sup_right (a := R) (Subgroup.mem_subgroupOf.mp ho)⟩, rfl⟩
  set P : GrpPred := fun (X : Type) [Group X] => Nonempty (X ≃* ↥Ks) with hPdef
  have hPi : IsoInv P := by
    intro A B _ _ e h
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  have hsecY' : SecAll ↥f.range P :=
    secAll_of_simple_subnormal hPi hKs' hKab hKsn ⟨MulEquiv.refl _⟩ hTs hKT hOn hKO hOY
  have hker : Group.IsSolvable ↥f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    let j : ↥f.ker →* ↥(kerIn M H) :=
      { toFun := fun y => ⟨((y : ↥Y) : G), by
          have hy : π (Subgroup.inclusion hYH (y : ↥Y)) = 1 := y.2
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hJ',
            Subgroup.mem_subgroupOf] at hy
          exact hy⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := j) fun a b hab => ?_
    apply Subtype.ext
    apply Subtype.ext
    simpa [j] using congrArg Subtype.val hab
  have hsecY : SecAll ↥Y P :=
    secAll_of_surjective hPi f.rangeRestrict f.rangeRestrict_surjective hker hsecY'
  have hE : ASInputs.E111Hyp ↥Y n := by
    intro H₁ K₁ _ _ hsn hsimple hnab B hB hBI
    have hsn' : H₁.IsSubnormal := isSubnormal_of_open hsn Subgroup.IsSubnormal.top
    obtain ⟨e⟩ := hsecY H₁ (K₁.subgroupOf H₁) hsn' hsimple hnab
    exact hP _ hnab ⟨e⟩ B hB hBI
  have hSecK : SecAll ↥Y Q := by
    intro H₁ N₁ _ hsn hsimple hnab
    obtain ⟨e⟩ := hsecY H₁ N₁ hsn hsimple hnab
    exact hQ _ _ e hKK
  have := h111 ↥Y hE hSecK
  rw [E1.nParam_subgroupOf]
  simpa using this


end E22N

end CFSG.Quasithin.E2
