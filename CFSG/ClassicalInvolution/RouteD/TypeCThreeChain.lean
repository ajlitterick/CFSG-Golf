module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLayers
public import CFSG.ClassicalInvolution.RouteD.TypeCChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv suppGroup coords pairPlanes
  pairPlaneSubgroup form IsAdaptedShortIn SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (diagTorus2 LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem exists_symplecticBlockStandardPairW (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z)
    {i₀ j₀ : Fin 3} (hij : i₀ ≠ j₀) {T : Subgroup G} (hT : IsShortNodeAt Fr i₀ j₀ T) {l : Fin 3}
    (hl1 : l ≠ i₀) (hl2 : l ≠ j₀) :
    ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (Fr.Kf j₀) T := by
  obtain ⟨LF⟩ := exists_localFrameIW S Fr l
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl1)
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl2)
  have hab : a ≠ b := fun h => hij (by rw [h])
  obtain ⟨s, hs, rfl⟩ := (LF.isAdaptedShortIn_iff S hab hT.1).mp hT.2
  obtain ⟨W, hW⟩ := Models.SymplecticPairs.exists_symplecticBlockStandardPair_short_comp
    (K := GaloisField p f) hab (LF.layerHom S hab) (LF.layerHom_injective S hab) hs
  have hKb : ((longBlock (GaloisField p f) 2 b).range.subgroupOf
      (suppGroup (coords a ∪ coords b) : Subgroup (StatedSp 2 (GaloisField p f)))).map
        (LF.layerHom S hab) = Fr.Kf (l.succAbove b) := by
    refine LF.injOn_locImg_Mf S hab (LF.map_layerHom_le S hab _)
      (Kf_le_Mf Fr (l.succAbove b) (Or.inr rfl)) ?_
    rw [LF.locImg_map_layerHom S hab, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Models.SymplecticPairs.longBlock_range_le_suppGroup_right hab),
      LF.adapted b]
  rw [hKb] at hW
  exact ⟨W, hW⟩

theorem routeD_typeC_two_of_shortNodes (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (Fr : Frame p f 2 Ω K z)
    (hA2 : ∃ T₀ T₁ : Subgroup G, IsShortNodeAt Fr 0 1 T₀ ∧ IsShortNodeAt Fr 1 2 T₁ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W T₀ T₁) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = 2 + 1 := by
  obtain ⟨T₀, T₁, hT₀, hT₁, hW⟩ := hA2
  refine routeD_typeC_of_chain S.odd S.five S.two_le S.inClass S.mem S.single hconn S.cls S.shape
    S.p1_z ![T₀, T₁, Fr.Kf 2] (Fr.mem 2) ?_ ?_ ?_
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | skip
    exact commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) a (hT₀.1 ha) b hb
  · intro i j hij hj
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; decide) | (exfalso; revert hj; decide) | skip
    exact hW
  · intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hi; decide) | (exfalso; revert hj; decide) | skip
    exact exists_symplecticBlockStandardPairW S Fr (i₀ := 1) (j₀ := 2) (by decide) hT₁ (l := 0)
      (by decide) (by decide)

end CFSG.ClassicalInvolution.RouteD
