module

public import CFSG.Quasithin.Background.F2Inner

public section

namespace CFSG.ASVolI.ChF

open CFSG.Quasithin CFSG.Quasithin.Amalgam CFSG.Quasithin.Amalgam.Completion

abbrev HypF_2_10 (D : Type) [Preorder D] (Y : Type) [Group Y] : Type := XYSetting D Y

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.Amalgam CFSG.Quasithin.Amalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_2_2 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G : Type) [Group G]
    (μ : Amalgam.Completion α G),
    ∃! f : gp α →* G, ∀ (d : D) (x : α.X d), f (ξ α d x) = μ.toHom d x


@[expose] def F_2_4 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    (∀ φ : G ≃* H, (∀ (d : D) (x : α.X d), φ (μ.toHom d x) = η.toHom d x) ↔
      φ.toMonoidHom.comp μ.hat = η.hat) ∧
    (IsEquivalent μ η ↔ μ.hat.ker = η.hat.ker)


@[expose] def F_2_5 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (a b : Aut α) (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    act 1 μ = μ ∧ act (a * b) μ = act a (act b μ) ∧ act a⁻¹ (act a μ) = μ ∧
    (∀ (d : D) (x : α.X d), (act a μ).toHom d x = μ.toHom d ((a⁻¹).1 d x)) ∧
    (IsEquivalent μ η → IsEquivalent (act a μ) (act a η))


@[expose] def F_2_6_sameAmalgam : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    IsQuasiEquivalent μ η ↔ ∃ a : Aut α, IsEquivalent (act a μ) η

@[expose] def F_2_6 : Prop :=
  (∀ (D : Type) [Preorder D] (α γ : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion γ H),
    IsQuasiEquivalent μ η ↔
      ∃ (φ : G ≃* H) (ψ : Iso α γ),
        ∀ (d : D) (x : α.X d), φ (μ.toHom d x) = η.toHom d (ψ.toEquiv d x)) ∧
    F_2_6_sameAmalgam


@[expose] def F_2_7 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D),
    (∀ a : Aut α, ∃! f : gp α →* gp α, ∀ (d : D) (x : α.X d), f (ξ α d x) = ξ α d (a.1 d x)) ∧
    (∀ a b : Aut α, hatPiHom (a * b) = (hatPiHom a).comp (hatPiHom b)) ∧
    hatPiHom (1 : Aut α) = MonoidHom.id (gp α) ∧
    (∀ a : Aut α, (hatPiHom a⁻¹).comp (hatPiHom a) = MonoidHom.id (gp α) ∧
      (hatPiHom a).comp (hatPiHom a⁻¹) = MonoidHom.id (gp α)) ∧
    (∀ (a : Aut α) (g : gp α), hatPi a g = hatPiHom a g)


@[expose] def F_2_8 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G : Type) [Group G]
    (μ : Amalgam.Completion α G) (a : Aut α),
    (act a μ).hat = μ.hat.comp (hatPi a⁻¹).toMonoidHom ∧
    (act a μ).hat.ker = μ.hat.ker.map (hatPi a).toMonoidHom ∧
    (IsEquivalent (act a μ) μ ↔ μ.hat.ker.map (hatPi a).toMonoidHom = μ.hat.ker) ∧
    (∀ h : a ∈ stabilizer μ,
      (∀ g : gp α, aPlus μ a h (QuotientGroup.mk g) = QuotientGroup.mk (hatPi a g)) ∧
      (∀ (d : D) (x : α.X d),
        aPlus μ a h (QuotientGroup.mk (ξ α d x)) = QuotientGroup.mk (ξ α d (a.1 d x))) ∧
      (∀ g : G, aMinus μ a h g = μ.plus (aPlus μ a h (μ.plus.symm g))) ∧
      (∀ (d : D) (x : α.X d), aMinus μ a h (μ.toHom d x) = μ.toHom d (a.1 d x)) ∧
      piMinus μ ⟨a, h⟩ = aMinus μ a h) ∧
    (∀ a b : stabilizer μ, piMinus μ (a * b) = piMinus μ a * piMinus μ b) ∧
    (∀ hμ : μ.IsFaithful,
      (∀ b : normAut μ, sigma μ hμ b ∈ stabilizer μ ∧
        IsEquivalent (act (sigma μ hμ b) μ) μ) ∧
      (∀ (b : normAut μ) (d : D) (x : α.X d),
        μ.toHom d ((sigma μ hμ b).1 d x) = b.1 (μ.toHom d x)) ∧
      (∀ b c : normAut μ, sigma μ hμ (b * c) =
        sigma μ hμ b * sigma μ hμ c) ∧
      (∀ c : stabilizer μ, piMinus μ c ∈ normAut μ) ∧
      (∀ (b : normAut μ) (h : sigma μ hμ b ∈ stabilizer μ),
        piMinus μ ⟨sigma μ hμ b, h⟩ = b.1) ∧
      (∀ (c : stabilizer μ) (h : piMinus μ c ∈ normAut μ),
        sigma μ hμ ⟨piMinus μ c, h⟩ = c.1) ∧
      (sigma μ hμ).range = stabilizer μ)


@[expose] def F_2_9 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (Yd : D → Subgroup Y) (hY : Monotone Yd),
    (⨆ d, Yd d) = ⊤ →
      ∃ η : Amalgam.Completion (ofSubgroups Yd hY) Y, η.IsFaithful ∧
        ∀ d, η.toHom d = (Yd d).subtype


@[expose] def F_2_10 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (S : HypF_2_10 D Y),
    (∀ (y : S.Yd S.least) (d : D) (x : S.Xd d),
      (((S.cAut y).1 d x : S.Xd d) : Y) = (y : Y) * (x : Y) * (y : Y)⁻¹) ∧
    (S.cAut 1 = 1 ∧ ∀ y y' : S.Yd S.least, S.cAut (y * y') = S.cAut y * S.cAut y') ∧
    (∀ y : S.Yd S.least, S.cAut y = 1 ↔
      ∀ (d : D) (x : Y), x ∈ S.Xd d → (y : Y) * x * (y : Y)⁻¹ = x) ∧
    (∀ x : S.Xd S.least,
      hatPi (S.cAut ⟨x, S.le _ x.2⟩) = MulAut.conj (ξ S.alpha S.least x)) ∧
    (∀ (G : Type) [Group G] (μ : Amalgam.Completion S.alpha G) (x : S.Xd S.least),
      S.cAut ⟨x, S.le _ x.2⟩ ∈ stabilizer μ) ∧
    (∀ (G : Type) [Group G] (μ : Amalgam.Completion S.alpha G), μ.IsFaithful →
      ∀ (x : S.Xd S.least) (h : S.cAut ⟨x, S.le _ x.2⟩ ∈ stabilizer μ),
        piMinus μ ⟨S.cAut ⟨x, S.le _ x.2⟩, h⟩ = MulAut.conj (μ.toHom S.least x))


@[expose] def F_2_11 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (S : HypF_2_10 D Y) (G : Type) [Group G]
    (μ : Amalgam.Completion S.alpha G) (h : S.Hyp211 μ),
    (∃ η : Amalgam.Completion S.gamma ↥h.G0,
      (∀ (d : D) (y : S.Yd S.least) (x : S.Xd d) (g : S.Yd d), (y : Y) * (x : Y) = (g : Y) →
        ((η.toHom d g : ↥h.G0) : MulAut G) = h.piC y * MulAut.conj (μ.toHom d x)) ∧
      (∀ (d : D) (x : S.Xd d),
        ((η.toHom d ⟨x, S.le d x.2⟩ : ↥h.G0) : MulAut G) = MulAut.conj (μ.toHom d x)) ∧
      (((∀ d, ∀ g ∈ S.Yd d, g ∈ Subgroup.centralizer (S.Xd d : Set Y) → g ∈ S.Xd d) ∧
          (∀ (d : D) (x : S.Xd d), μ.toHom d x ∈ Subgroup.center G → x = 1)) →
        η.IsFaithful) ∧
    (∃ η' : Amalgam.Completion S.alpha ↥(MulAut.conj : G →* MulAut G).range,
      (∀ (d : D) (x : S.Xd d),
        ((η.toHom d ⟨x, S.le d x.2⟩ : ↥h.G0) : MulAut G) =
          ((η'.toHom d x : ↥(MulAut.conj : G →* MulAut G).range) : MulAut G)) ∧
      (∀ (d : D) (x : S.Xd d), ((η'.toHom d x : ↥(MulAut.conj : G →* MulAut G).range) : MulAut G) =
        MulAut.conj (μ.toHom d x)) ∧
      (η'.IsFaithful ↔ ∀ (d : D) (x : S.Xd d), μ.toHom d x ∈ Subgroup.center G → x = 1) ∧
      (Subgroup.center G = ⊥ → IsEquivalent μ η')))


end CFSG.ASVolI
