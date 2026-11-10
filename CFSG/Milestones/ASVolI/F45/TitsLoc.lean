module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLocThm
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam.Completion

section Data

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

structure burnsideF45_TitsData (c : α.Completion Y) : Prop where
  faithful : c.IsFaithful
  poly : IsGenPolygon c.graph 8
  pt : ∃ b₀, PtLoc c.G0 c.graph c.xv b₀ c.lv
  aff : ∃ lab, AffLab c.G0 c.graph c.xv lab
  ln : ∃ b₇ b₁ b₂, LnLoc c.G0 c.graph c.lv b₇ b₁ b₂
  cardx : Nat.card (stv c c.xv) = 10240
  cardl : Nat.card (stv c c.lv) = 6144


theorem burnsideF45_relIndex_stv (c : α.Completion Y) (H : Subgroup c.G0) (w : c.Γ) :
    (stv c w).relIndex H = (MulAction.orbit H w).ncard := by
  have h : (stv c w).subgroupOf H = MulAction.stabilizer H w := by
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  rw [Subgroup.relIndex, h, MulAction.index_stabilizer]

@[expose] def burnsideF45_edge {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    GPath Γ 1 :=
  (GPath.triv u).snoc w h

theorem burnsideF45_edge_zero {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h 0 = u := rfl

theorem burnsideF45_edge_one {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h 1 = w := GPath.snoc_last _ _ _

theorem burnsideF45_edge_mem {V : Type*} {Γ : SimpleGraph V} {u w : V} (h : Γ.Adj u w) :
    burnsideF45_edge h ∈ GPath.nbPaths Γ u 1 :=
  ⟨rfl, fun i hi => absurd hi (by omega)⟩


theorem burnsideF45_adj_first {V : Type*} {Γ : SimpleGraph V} {a : V} {n : ℕ}
    (hn : 1 ≤ n) {q : GPath Γ n} (hq : q ∈ GPath.nbPaths Γ a n) : Γ.Adj a (q 1) := by
  have := q.adj 0 (by omega)
  rwa [hq.1] at this


theorem burnsideF45_eq_one_of_card_two {G V : Type*} [Group G] [MulAction G V] {K : Subgroup G}
    (hK : Nat.card K = 2) {t g : G} (ht : t ∈ K) (hg : g ∈ K) {w : V} (htw : t • w ≠ w)
    (hgw : g • w = w) : g = 1 := by
  rw [Nat.card_eq_two_iff' (1 : K)] at hK
  obtain ⟨y, -, huniq⟩ := hK
  by_contra hg1
  have e1 : (⟨g, hg⟩ : K) = y := huniq _ (fun h => hg1 (congrArg Subtype.val h))
  have e2 : (⟨t, ht⟩ : K) = y := huniq _ (fun h => htw (by
    have : t = 1 := congrArg Subtype.val h
    rw [this, one_smul]))
  have : g = t := congrArg Subtype.val (e1.trans e2.symm)
  exact htw (this ▸ hgw)

@[expose] def burnsideF45_dih (e b : ZMod 5) : DihedralGroup 5 :=
  if e = 1 then DihedralGroup.r b else DihedralGroup.sr (-b)

theorem burnsideF45_dih_mul : ∀ e₁ e₂ b₁ b₂ : ZMod 5, (e₁ = 1 ∨ e₁ = -1) → (e₂ = 1 ∨ e₂ = -1) →
    burnsideF45_dih e₁ b₁ * burnsideF45_dih e₂ b₂ = burnsideF45_dih (e₁ * e₂) (e₁ * b₂ + b₁) := by
  decide

theorem burnsideF45_dih_inj : ∀ e₁ e₂ b₁ b₂ : ZMod 5, (e₁ = 1 ∨ e₁ = -1) → (e₂ = 1 ∨ e₂ = -1) →
    burnsideF45_dih e₁ b₁ = burnsideF45_dih e₂ b₂ → e₁ = e₂ ∧ b₁ = b₂ := by
  decide

theorem burnsideF45_aff_iter : ∀ e b : ZMod 5, (fun i => e * i + b)^[10] 0 = 0 →
    (fun i => e * i + b)^[10] 1 = 1 → e = 1 ∨ e = -1 := by
  decide

end Data

namespace burnsideF45_TitsData

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}
  (T : burnsideF45_TitsData c)

include T

theorem card_nbrs_xv : Nat.card (CosetGeom.nbrs c.xv) = 5 := by
  obtain ⟨lab, A⟩ := T.aff
  have e : Nat.card (ZMod 5) = Nat.card (CosetGeom.nbrs c.xv) :=
    Nat.card_congr (Equiv.ofBijective (fun i : ZMod 5 => (⟨lab i, A.adj i⟩ : CosetGeom.nbrs c.xv))
      ⟨fun i j hij => A.inj (congrArg Subtype.val hij), fun ⟨u, hu⟩ => by
        obtain ⟨i, hi⟩ := A.surj u hu
        exact ⟨i, Subtype.ext hi⟩⟩)
  rw [← e]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_nbrs_lv : Nat.card (CosetGeom.nbrs c.lv) = 3 := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  rw [Nat.card_coe_set_eq]
  exact L.card

theorem qOne_eq : α.qOne = 4 := by
  have h := card_nbrs T.faithful c.xv
  rw [T.card_nbrs_xv] at h
  have h' : α.qv false = α.qOne := rfl
  change 5 = α.qv false + 1 at h
  omega

theorem qTwo_eq : α.qTwo = 2 := by
  have h := card_nbrs T.faithful c.lv
  rw [T.card_nbrs_lv] at h
  have h' : α.qv true = α.qTwo := rfl
  change 3 = α.qv true + 1 at h
  omega

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  exists_nbr_ne T.faithful (by rw [T.qOne_eq]; norm_num) (by rw [T.qTwo_eq])

theorem transX : c.PathTrans c.xv 8 := by
  obtain ⟨b₀, P⟩ := T.pt
  exact fun q q' hq hq' => P.pathTrans T.poly hq hq'

theorem transL : c.PathTrans c.lv 7 := by
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  exact fun q q' hq hq' => L.pathTrans7 T.poly hq hq'


end burnsideF45_TitsData

end CFSG.ASVolI
