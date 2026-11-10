module

public import CFSG.Quasithin.Background.F3Compare
public import CFSG.Quasithin.Background.F3Geometry

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.RankTwoAmalgam
open CFSG.Quasithin.RankTwoAmalgam.Completion

structure HypF_3 {G : Type} [Group G] (G₁ G₂ : Subgroup G) : Prop where
  finite₁ : Finite G₁
  finite₂ : Finite G₂
  gen : G₁ ⊔ G₂ = ⊤

noncomputable abbrev incl {G : Type} [Group G] (G₁ G₂ : Subgroup G) :
    (RankTwoAmalgam.ofSubgroups G₁ G₂).Completion ↥(G₁ ⊔ G₂) :=
  RankTwoAmalgam.inclusionCompletion G₁ G₂ (G₁ ⊔ G₂) rfl

theorem incl_faithful {G : Type} [Group G] (G₁ G₂ : Subgroup G) : (incl G₁ G₂).IsFaithful :=
  RankTwoAmalgam.inclusionCompletion_isFaithful G₁ G₂ (G₁ ⊔ G₂) rfl

@[expose] def F33Conclusion {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (hc : c.IsFaithful) (uh : α.Γhat) : Prop :=
  (Function.Bijective ((c.graphCovering hc).pathSetMap uh) ∧
    (∀ n, Set.BijOn (c.graphCovering hc).pathMap (GPath.paths α.graphHat uh n)
      (GPath.paths c.graph (c.Θ hc uh) n)) ∧
    Set.BijOn ((c.graphCovering hc).pathSetMap uh) {p | p.NoBack} {p | p.NoBack} ∧
    (∀ n, Set.BijOn (c.graphCovering hc).pathMap (GPath.nbPaths α.graphHat uh n)
      (GPath.nbPaths c.graph (c.Θ hc uh) n))) ∧
  (∃ q : PermQuasiEquiv (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) uh) (PathSet α.graphHat uh)
      (MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range) (c.Θ hc uh)) (PathSet c.graph (c.Θ hc uh)),
    (∀ g, ((q.grp g : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) =
      c.theta ((g : ↥(α.Ghat1 ⊔ α.Ghat2)) : α.Ghat)) ∧
    ∀ p, q.set p = (c.graphCovering hc).pathSetMap uh p) ∧
  (∀ {n : ℕ} (p : GPath α.graphHat n), p 0 = uh →
    p.stabPath.map (c.theta0 hc) = ((c.graphCovering hc).pathMap p).stabPath ∧
    Set.InjOn (c.theta0 hc) ((p.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) : Set ↥(α.Ghat1 ⊔ α.Ghat2)) ∧
    Nonempty (↥(p.stabPath : Subgroup ↥(α.Ghat1 ⊔ α.Ghat2)) ≃*
      ↥(((c.graphCovering hc).pathMap p).stabPath : Subgroup ↥(c.φ1.range ⊔ c.φ2.range)))) ∧
  (∀ n : ℕ, (∀ q₁ q₂ : GPath α.graphHat n, q₁ ∈ GPath.nbPaths α.graphHat uh n →
      q₂ ∈ GPath.nbPaths α.graphHat uh n →
      ∃ g : ↥(α.Ghat1 ⊔ α.Ghat2), g • uh = uh ∧ g • q₁ = q₂) →
    ∀ p₁ p₂ : GPath c.graph n, p₁ ∈ GPath.nbPaths c.graph (c.Θ hc uh) n →
      p₂ ∈ GPath.nbPaths c.graph (c.Θ hc uh) n →
      ∃ g : ↥(c.φ1.range ⊔ c.φ2.range), g • c.Θ hc uh = c.Θ hc uh ∧ g • p₁ = p₂)

@[expose] def F34Conclusion {α : RankTwoAmalgam.{0}} {Y Y' : Type} [Group Y] [Group Y']
    (ι : α.Completion Y) (β : α.Completion Y') (hι : ι.IsFaithful) (hβ : β.IsFaithful)
    (uh : α.Γhat) : Prop :=
  (∃ q : PermQuasiEquiv (MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι uh))
      (PathSet ι.graph (ι.Θ hι uh))
      (MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh))
      (PathSet β.graph (β.Θ hβ uh)),
    q.grp = stabComp ι β hι hβ uh ∧ q.set = psi ι β hι hβ uh) ∧
  (∀ (p : PathSet ι.graph (ι.Θ hι uh)) (g : MulAction.stabilizer ↥(ι.φ1.range ⊔ ι.φ2.range) (ι.Θ hι uh)),
    ((g : ↥(ι.φ1.range ⊔ ι.φ2.range)) ∈ p.2.1.stabPath ↔
      ((stabComp ι β hι hβ uh g : MulAction.stabilizer ↥(β.φ1.range ⊔ β.φ2.range) (β.Θ hβ uh)) :
        ↥(β.φ1.range ⊔ β.φ2.range)) ∈ (psi ι β hι hβ uh p).2.1.stabPath)) ∧
  (∀ n : ℕ, (∀ p₁ p₂ : GPath ι.graph n, p₁ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      p₂ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      ∃ g : ↥(ι.φ1.range ⊔ ι.φ2.range), g • ι.Θ hι uh = ι.Θ hι uh ∧ g • p₁ = p₂) →
    ∀ p₁ p₂ : GPath β.graph n, p₁ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n →
      p₂ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n →
      ∃ g : ↥(β.φ1.range ⊔ β.φ2.range), g • β.Θ hβ uh = β.Θ hβ uh ∧ g • p₁ = p₂)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.RankTwoAmalgam
open CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_3_1 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    (CosetGeom.graph (G₁ ⊔ G₂) G₁ G₂).Connected ∧
    GraphCovering (RankTwoAmalgam.ofSubgroups G₁ G₂).graphHat (incl G₁ G₂).graph
      ((incl G₁ G₂).Θ (incl_faithful G₁ G₂)) ∧
    (∀ uh : (RankTwoAmalgam.ofSubgroups G₁ G₂).Γhat,
      GraphCovering.StabIso (θ := (incl G₁ G₂).Θ (incl_faithful G₁ G₂))
        (θG := ((incl G₁ G₂).coverData (incl_faithful G₁ G₂)).hom0) uh)


@[expose] def F_3_3 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    ∀ uh : (RankTwoAmalgam.ofSubgroups G₁ G₂).Γhat,
      F33Conclusion (incl G₁ G₂) (incl_faithful G₁ G₂) uh


@[expose] def F_3_4 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    ∀ (Ġ : Type) [Group Ġ] (β : (RankTwoAmalgam.ofSubgroups G₁ G₂).Completion Ġ)
      (hβ : β.IsFaithful) (uh : (RankTwoAmalgam.ofSubgroups G₁ G₂).Γhat),
      F34Conclusion (incl G₁ G₂) β (incl_faithful G₁ G₂) hβ uh


@[expose] def F_3_5 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    2 < (nbrs (γ₀ (G₁ ⊔ G₂) G₁ G₂)).encard → 2 < (nbrs (γ₁ (G₁ ⊔ G₂) G₁ G₂)).encard →
    ∀ (u : CosetGeom (G₁ ⊔ G₂) G₁ G₂) (m : ℕ), 1 ≤ m →
      (∀ q q' : GPath (graph (G₁ ⊔ G₂) G₁ G₂) (m + 1),
        q ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1) →
        q' ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1) →
        ∃ g : ↥(G₁ ⊔ G₂), g • u = u ∧ g • q = q') →
      ∀ p : GPath (graph (G₁ ⊔ G₂) G₁ G₂) (m + 1),
        p ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1) →
        GPath.F35Conclusion (graph (G₁ ⊔ G₂) G₁ G₂) ↥(G₁ ⊔ G₂) u m p


@[expose] def F_3_6 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    ∀ m : ℕ, 1 < m → UniqueGeod (graph (G₁ ⊔ G₂) G₁ G₂) m →
      ∀ s t : ↥(G₁ ⊔ G₂), s * s = 1 → t * t = 1 → (s : G) ∈ G₁ → (s : G) ∉ G₁ ⊓ G₂ →
        (t : G) ∈ G₂ → (t : G) ∉ G₁ ⊓ G₂ →
        ∀ n : ℕ, 0 < n → n ≤ m → (((s * t) ^ n : ↥(G₁ ⊔ G₂)) : G) ∈ G₁ ⊓ G₂ →
          n = m ∧
          IsPolygon (graph (G₁ ⊔ G₂) G₁ G₂)
            (MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
              MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂)) (2 * m) ∧
          (∀ w ∈ Subgroup.closure {s, t},
            (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
              MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂), w • v = v) ↔
              w ∈ Subgroup.zpowers ((s * t) ^ m)) ∧
          (Subgroup.zpowers ((s * t) ^ m)).relIndex (Subgroup.closure {s, t}) = 2 * m


@[expose] def F_3_7 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ : Subgroup G), HypF_3 G₁ G₂ →
    ∀ m : ℕ, 4 ≤ m → Even m → UniqueGeod (graph (G₁ ⊔ G₂) G₁ G₂) m →
      ∀ c : CosetGeom (G₁ ⊔ G₂) G₁ G₂,
        (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₀ (G₁ ⊔ G₂) G₁ G₂) c → c ≠ γ₁ (G₁ ⊔ G₂) G₁ G₂ →
        ∀ s t : ↥(G₁ ⊔ G₂), s * s = 1 → t * t = 1 → (s : G) ∈ stab c → (s : G) ∉ G₁ ⊓ stab c →
          (t : G) ∈ G₂ → (t : G) ∉ G₁ ⊓ G₂ →
          ∀ n : ℕ, 0 < n → n ≤ m / 2 → (((s * t) ^ n : ↥(G₁ ⊔ G₂)) : G) ∈ G₁ ⊓ G₂ ⊓ stab c →
            n = m / 2 ∧
            IsPolygon (graph (G₁ ⊔ G₂) G₁ G₂)
              (MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
                MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂) ∪
                MulAction.orbit (Subgroup.closure {s, t}) c) (2 * m) ∧
            (∀ w ∈ Subgroup.closure {s, t},
              (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
                MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂) ∪
                MulAction.orbit (Subgroup.closure {s, t}) c, w • v = v) ↔
                w ∈ Subgroup.zpowers ((s * t) ^ n)) ∧
            (Subgroup.zpowers ((s * t) ^ n)).relIndex (Subgroup.closure {s, t}) = 2 * n


end CFSG.ASVolI
