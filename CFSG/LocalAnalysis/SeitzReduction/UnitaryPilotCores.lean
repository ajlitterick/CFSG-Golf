module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTorusBasic

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.LinearPilot (rootTorusParam)

section Tori

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

omit [Field K] in
theorem subset_compl_pair_iff {a b : Fin n} {I : Finset (Fin n)} :
    I ⊆ {a, b}ᶜ ↔ a ∉ I ∧ b ∉ I := by
  constructor
  · intro hI
    exact ⟨fun ha => by simpa using hI ha, fun hb => by simpa using hI hb⟩
  · rintro ⟨ha, hb⟩ i hi
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => ha (h' ▸ hi), fun h' => hb (h' ▸ hi)⟩

omit [Field K] in
theorem two_le_card_compl_of_subset_compl_pair {a b : Fin n} (hab : a ≠ b)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) : 2 ≤ Iᶜ.card := by
  have hsub : ({a, b} : Finset (Fin n)) ⊆ Iᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxI
    have := hI hxI
    rw [Finset.mem_compl] at this
    exact this hx
  calc 2 = ({a, b} : Finset (Fin n)).card := (Finset.card_pair hab).symm
    _ ≤ Iᶜ.card := Finset.card_le_card hsub

theorem unitaryRootTorus_le_unitaryBlockTorus_of_subset {a b : Fin n} (hab : a ≠ b)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) : unitaryRootTorus h hab ≤ unitaryBlockTorus h I :=
  unitaryRootTorus_le_unitaryBlockTorus h hab (subset_compl_pair_iff.1 hI).1
    (subset_compl_pair_iff.1 hI).2


end Tori

section Pieces

variable {G : Type*} [Group G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} {n : ℕ} (e : L ≃* unitaryPSU h n)

@[expose] noncomputable def pieceCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (unitaryBlockTorus h I))

theorem pieceCore_def (I : Finset (Fin n)) :
    pieceCore e I = centralizerPerfectCore (modelToG e (unitaryBlockTorus h I)) :=
  rfl

@[expose] noncomputable def neighbourCore {a b : Fin n} (hab : a ≠ b) : Subgroup G :=
  centralizerPerfectCore (modelToG e (unitaryRootTorus h hab))

theorem neighbourCore_def {a b : Fin n} (hab : a ≠ b) :
    neighbourCore e hab = centralizerPerfectCore (modelToG e (unitaryRootTorus h hab)) :=
  rfl


theorem modelToG_unitaryRootTorus_le {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (hI : I ⊆ {a, b}ᶜ) :
    modelToG e (unitaryRootTorus h hab) ≤ modelToG e (unitaryBlockTorus h I) :=
  modelToG_mono e (unitaryRootTorus_le_unitaryBlockTorus_of_subset h hab hI)

theorem pieceCore_le_neighbourCore {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (hI : I ⊆ {a, b}ᶜ) : pieceCore e I ≤ neighbourCore e hab :=
  centralizerPerfectCore_anti (modelToG_unitaryRootTorus_le e hab hI)

theorem modelToG_le_pieceCore {I : Finset (Fin n)} {A : Subgroup (unitaryPSU h n)}
    (hA : A ≤ centralizer (unitaryBlockTorus h I : Set (unitaryPSU h n))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ pieceCore e I :=
  modelToG_le_centralizerPerfectCore e hA hperf

theorem modelToG_le_neighbourCore {a b : Fin n} (hab : a ≠ b) {A : Subgroup (unitaryPSU h n)}
    (hA : A ≤ centralizer (unitaryRootTorus h hab : Set (unitaryPSU h n))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ neighbourCore e hab :=
  modelToG_le_centralizerPerfectCore e hA hperf

theorem modelToG_blockSU_le_pieceCore (I : Finset (Fin n))
    (hperf : ⁅blockSU h I, blockSU h I⁆ = blockSU h I) :
    modelToG e (blockSU h I) ≤ pieceCore e I :=
  modelToG_le_pieceCore e (blockSU_le_centralizer_unitaryBlockTorus h I) hperf

end Pieces

section PiecesPerfect

variable {G : Type*} [Group G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} {n : ℕ} (e : L ≃* unitaryPSU h n)


theorem modelToG_blockSU_compl_le_neighbourCore (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n))) ≤ neighbourCore e hab :=
  modelToG_le_neighbourCore e hab (blockSU_compl_le_centralizer_unitaryRootTorus h hab)
    (Subgroup.isPerfect_iff.1 (isQuasisimple_blockSU_compl_pair h hn hab).1)

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (I : Finset (Fin n)) : t ∈ normalizer (pieceCore e I : Set G) :=
  mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _


theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G)) {a b : Fin n}
    (hab : a ≠ b) : t ∈ normalizer (neighbourCore e hab : Set G) :=
  mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem symm_mem_normalizer_neighbourCore {a b : Fin n} (hab : a ≠ b) {x : unitaryPSU h n}
    (hx : x ∈ normalizer (unitaryRootTorus h hab : Set (unitaryPSU h n))) :
    ((e.symm x : L) : G) ∈ normalizer (neighbourCore e hab : Set G) :=
  symm_mem_normalizer_centralizerPerfectCore_modelToG e hx

section Finite

variable [Finite G]

theorem pieceCore_eq_perfectCore_inf {X : Subgroup G} {I : Finset (Fin n)}
    (hX : X ≤ modelToG e (unitaryBlockTorus h I)) :
    pieceCore e I = perfectCore (centralizerPerfectCore X ⊓
      centralizer (modelToG e (unitaryBlockTorus h I) : Set G)) :=
  centralizerPerfectCore_modelToG_eq_perfectCore_inf e hX

theorem pieceCore_eq {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) :
    pieceCore e I = perfectCore (neighbourCore e hab ⊓
      centralizer (modelToG e (unitaryBlockTorus h I) : Set G)) :=
  pieceCore_eq_perfectCore_inf e (modelToG_unitaryRootTorus_le e hab hI)


theorem pieceCore_eq_map_conj {I J : Finset (Fin n)} {x : unitaryPSU h n}
    (hx : (unitaryBlockTorus h I).map (MulAut.conj x).toMonoidHom = unitaryBlockTorus h J) :
    pieceCore e J = (pieceCore e I).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [pieceCore_def, pieceCore_def, ← hx, centralizerPerfectCore_modelToG_map_conj]

theorem neighbourCore_eq_map_conj {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    {x : unitaryPSU h n}
    (hx : (unitaryRootTorus h hab).map (MulAut.conj x).toMonoidHom = unitaryRootTorus h hcd) :
    neighbourCore e hcd =
      (neighbourCore e hab).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [neighbourCore_def, neighbourCore_def, ← hx, centralizerPerfectCore_modelToG_map_conj]

end Finite

end PiecesPerfect

end CFSG.SeitzReduction.UnitaryPilot
