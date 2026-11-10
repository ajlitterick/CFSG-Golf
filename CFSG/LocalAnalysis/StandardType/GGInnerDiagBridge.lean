module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inner

variable {U : Type*} [Group U] {G : Type*} [Group G]

theorem ggPsiInnerDiag_of_induces_conj (Δ : UniversalRootDatum U) (ψ : U →* G)
    (hperf : commutator ↥ψ.range = ⊤) {R : Type} [Group R]
    (θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {r : R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) (MulAut.conj r)) :
    GGPsiInnerDiag Δ ψ c := by
  obtain ⟨y, hy⟩ := θ.surjective r
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hmem : ∀ l : ↥ψ.range, c⁻¹ * (l : G) * c ∈ ψ.range := fun l => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) l).mp l.2
    rwa [inv_inv] at this
  let α : ↥ψ.range →* ↥ψ.range :=
    { toFun := fun l => ⟨c⁻¹ * (l : G) * c, hmem l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ l, ((α l : ↥ψ.range) : G) = c⁻¹ * (l : G) * c := fun _ => rfl
  have hβα : (MulAut.conj g₀).toMonoidHom = α := by
    refine TypeA.eq_of_inv_mul_mem_center hperf _ _ fun l => ?_
    have hl := h l (α l) (hα l).symm
    rw [MulAut.conj_apply, ← hy, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hl
    exact QuotientGroup.eq.mp (θ.injective hl)
  have key : ∀ z : U, (g₀ : G) * ψ z * (g₀ : G)⁻¹ = c⁻¹ * ψ z * c := fun z => by
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hβα (⟨ψ z, z, rfl⟩ : ↥ψ.range))
    rw [hα] at h1
    exact h1
  refine ⟨g₀, g₀.2, fun γ _ => ⟨1, Subgroup.one_mem _, fun z _ => ?_⟩⟩
  rw [one_mul, inv_one, mul_one]
  calc (c * (g₀ : G))⁻¹ * ψ z * (c * g₀) = (g₀ : G)⁻¹ * (c⁻¹ * ψ z * c) * g₀ := by group
    _ = (g₀ : G)⁻¹ * ((g₀ : G) * ψ z * (g₀ : G)⁻¹) * g₀ := by rw [key z]
    _ = ψ z := by group

theorem ggPsiInnerDiag_of_induces_mem_inn (Δ : UniversalRootDatum U) (ψ : U →* G)
    (hperf : commutator ↥ψ.range = ⊤) {R : Type} [Group R]
    (θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R) {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (h : ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) :
    GGPsiInnerDiag Δ ψ c := by
  obtain ⟨φ, hφ, hind⟩ := h
  obtain ⟨r, rfl⟩ := hI hφ
  exact ggPsiInnerDiag_of_induces_conj Δ ψ hperf θ hc hind

end Inner

@[expose] def GGInnerDiagOpenTag (t : StatedLieTag) : Prop :=
  t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨
    t = .E8 ∨ t = .twistedE6

section Genuine

@[expose] def GGInnerDiagMarkingAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
      LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU t n f).D ψ c →
          ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)

@[expose] def GGInnerDiagMarkingInput : Prop :=
  ∀ t : StatedLieTag, GGInnerDiagMarkingAt t

theorem ggInnerDiagMarkingAt_of_rank {t : StatedLieTag} (h : ∀ n f, (ggU t n f).D.rank < 2) :
    GGInnerDiagMarkingAt t := by
  intro G _ _ n f ψ G₀ hpres
  exact absurd hpres.1.2 (by have := h n f; omega)

theorem ggInnerDiagMarkingAt_POmegaOdd : GGInnerDiagMarkingAt .POmegaOdd := by
  intro G _ _ n f ψ G₀ hpres
  exact absurd rfl hpres.1.1.2.2.2

theorem ggInnerDiagMarkingInput_of_open (hA : GGInnerDiagMarkingAt .PSL)
    (h : ∀ t, GGInnerDiagOpenTag t → GGInnerDiagMarkingAt t) : GGInnerDiagMarkingInput := by
  have h0 : ∀ t, (∀ n f, (ggU t n f).D.rank = 0) → GGInnerDiagMarkingAt t := fun t ht =>
    ggInnerDiagMarkingAt_of_rank fun n f => by rw [ht n f]; omega
  intro t
  cases t
  · exact hA
  · exact h _ (.inl rfl)
  · exact h _ (.inr (.inl rfl))
  · exact ggInnerDiagMarkingAt_POmegaOdd
  · exact h _ (.inr (.inr (.inl rfl)))
  · exact h _ (.inr (.inr (.inr (.inl rfl))))
  · exact h0 _ fun _ _ => rfl
  · exact h _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl

variable {G : Type} [Group G] [Finite G]

theorem ggInnerDiagOn_of_presents_mk (hR : GGInnerDiagMarkingInput) {G₀ Bs : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hVI : ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) : GGInnerDiagOn Bs G₀ :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hBsN, fun b hb => hP b (hBsN hb) (hVI b hb)⟩)
    (hR t G n f ψ G₀ hpres)


end Genuine

section Bridge


end Bridge

section Assembly


end Assembly

end CFSG.StandardType
