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
