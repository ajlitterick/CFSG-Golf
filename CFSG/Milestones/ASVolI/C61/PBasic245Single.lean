module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.Milestones.ASVolI.C61.CS

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

namespace C56
open CFSG.QuasithinUnique.C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem isShort (hcs : burnsideC56_CS G T M H S L) : IsShort2 L := hcs.block.1.1

theorem le_H (hcs : burnsideC56_CS G T M H S L) : L ≤ H := hcs.block.1.2.1


theorem H_eq (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) : H = L ⊔ S := by
  rw [hcs.eq_join, hj]

theorem H_le_normalizer (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    H ≤ normalizer (L : Set G) := by
  rw [H_eq hcs hj]
  exact sup_le Subgroup.le_normalizer (S_le_normalizer hj)


theorem pCoreOf_le_S (hcs : burnsideC56_CS G T M H S L) : pCoreOf 2 H ≤ S :=
  hcs.sylow.pCoreOf_le

theorem blockQ_le_pCoreOf (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    blockQ L ≤ pCoreOf 2 H :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans (le_H hcs))
    (fun _ hg => C1.mem_normalizer_blockQ (H_le_normalizer hcs hj hg)) (C1.blockQ_isPGroup L)

theorem blockU_le_pCoreOf (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ (isShort hcs)).trans (blockQ_le_pCoreOf hcs hj)

theorem noCommonNormal (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (hne : S ≠ M₀) : C5.NoCommonNormal S H M₀ := by
  intro X hXS hXne hHX hM₀X
  have h244 := hcs.l244 X hXne hXS hHX
  apply hne
  refine le_antisymm hSM fun m hm => ?_
  have : m ∈ T ⊓ normalizer (X : Set G) := ⟨hMT hm, hM₀X hm⟩
  rw [h244] at this
  exact this

theorem blockQ_le_pCoreOf_conjJoin (hcs : burnsideC56_CS G T M H S L) :
    blockQ L ≤ pCoreOf 2 (conjJoin S L) := by
  have hLK : L ≤ conjJoin S L := le_conjJoin L (one_mem _)
  refine C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hLK) ?_ (C1.blockQ_isPGroup L)
  rcases hcs.blocks with hj | ⟨t, ht, hne, hK, hcomm⟩
  · rw [hj]
    exact C1.le_normalizer_blockQ L
  · rw [hK]
    refine sup_le (C1.le_normalizer_blockQ L) ?_
    have hc : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact C5.le_normalizer_of_commute fun u hu a ha =>
      (Subgroup.mem_centralizer_iff.mp (hc hu) a (C1.blockQ_le L ha)).symm

theorem pCoreOf_conjJoin_le (hcs : burnsideC56_CS G T M H S L) :
    pCoreOf 2 (conjJoin S L) ≤ pCoreOf 2 H := by
  have hKH : conjJoin S L ≤ H := by
    rw [hcs.eq_join]
    exact le_sup_left
  have hHK : H ≤ normalizer (conjJoin S L : Set G) := by
    rw [hcs.eq_join]
    exact sup_le Subgroup.le_normalizer (S_le_normalizer_conjJoin L)
  refine C1.le_pCoreOf_of_normalized ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hKH)
    (fun g hg => ?_) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjJoin S L) (hHK hg)

theorem blockU_le_pCoreOf_general (hcs : burnsideC56_CS G T M H S L) :
    blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ (isShort hcs)).trans
    ((blockQ_le_pCoreOf_conjJoin hcs).trans (pCoreOf_conjJoin_le hcs))


theorem not_conj_le_of_exists (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G}
    (h2 : S.relIndex M₀ = 2) (hex : ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H) {x : G}
    (hx : x ∈ M₀) (hxS : x ∉ S) : ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  obtain ⟨y, hy, hyU⟩ := hex
  have hyS : y ∉ S := by
    intro hyS
    apply hyU
    have hUP := blockU_le_pCoreOf_general hcs
    have hPn : y ∈ normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hcs.sylow.le hyS)
    have := C5.conjSubgroup_mono hUP y
    rwa [C5.conjSubgroup_eq_self hPn] at this
  have hs : y⁻¹ * x ∈ S := inv_mul_mem_of_relIndex_two h2 hy hyS hx hxS
  intro hxP
  apply hyU
  have hPn : (y⁻¹ * x)⁻¹ ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
      (hcs.sylow.le (inv_mem hs))
  have h1 := C5.conjSubgroup_mono hxP (y⁻¹ * x)⁻¹
  rw [conjR_eq, conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self hPn] at h1
  have e : x * (y⁻¹ * x)⁻¹ = y := by group
  rw [e] at h1
  exact h1

theorem H_le_normalizer_conjJoin (hcs : burnsideC56_CS G T M H S L) :
    H ≤ normalizer (conjJoin S L : Set G) := by
  rw [hcs.eq_join]
  exact sup_le Subgroup.le_normalizer (S_le_normalizer_conjJoin L)

theorem bb1 (hcs : burnsideC56_CS G T M H S L) :
    ∀ p ∈ pCoreOf 2 H, ∀ l ∈ L, p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  intro p hp l hl
  rcases hcs.blocks with hj | ⟨t, -, -, hK, hcomm⟩
  · exact C1.commutator_mem_blockU_of_mem_blockQ (isShort hcs)
      (fun l hl => C1.commutator_mem_blockQ_of_mem_pCoreOf (le_H hcs)
        (H_le_normalizer hcs hj) hp hl) l hl
  · have hLc : L ≤ centralizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj t).toMonoidHom, a * b = b * a :=
      fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hLc ha) b hb).symm
    refine C1.commutator_mem_blockU_double (isShort hcs) hc (le_H hcs) ?_ hp hl
    rw [← hK]
    exact H_le_normalizer_conjJoin hcs

theorem c55 (hcs : burnsideC56_CS G T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (hne : S ≠ M₀) :
    ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  have hL := isShort hcs
  set U := blockU L with hU
  set P := pCoreOf 2 H with hP
  set X : Subgroup G := ⨆ y : M₀, conjR U (y : G) with hX
  have hXP : X ≤ P := iSup_le fun y => hcon y y.2
  have hUX : U ≤ X := by
    have h1 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) ≤ X :=
      le_iSup (fun y : M₀ => conjR U (y : G)) ⟨1, one_mem _⟩
    have h2 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) = U := conjSubgroup_one U
    rwa [h2] at h1
  have hXne : X ≠ ⊥ := fun h => blockU_ne_bot hL (le_bot_iff.mp (h ▸ hUX))
  have hXS : X ≤ S := hXP.trans (pCoreOf_le_S hcs)
  have hM₀X : M₀ ≤ normalizer (X : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup X m ≤ X := by
      have : conjSubgroup X m = ⨆ y : M₀, conjSubgroup (conjR U (y : G)) m := by
        simp only [conjSubgroup, hX]
        exact Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun y => ?_
      have : conjSubgroup (conjR U (y : G)) m = conjR U ((y : G) * m) :=
        conjSubgroup_conjSubgroup U (y : G) m
      rw [this]
      exact le_iSup (fun y : M₀ => conjR U (y : G)) ⟨(y : G) * m, mul_mem y.2 hm⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  have key : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X := by
    intro l hl x hx
    refine Subgroup.iSup_induction (fun y : M₀ => conjR U (y : G))
      (C := fun x => l * x * l⁻¹ ∈ X) hx ?_ ?_ ?_
    · intro y x hxy
      have hxP : x ∈ P := hcon y y.2 hxy
      have hc : l * x * l⁻¹ * x⁻¹ ∈ U := by
        have h1 := bb1 hcs x hxP l hl
        have e : l * x * l⁻¹ * x⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h1
      have hxX : x ∈ X := le_iSup (fun y : M₀ => conjR U (y : G)) y hxy
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact mul_mem (hUX hc) hxX
    · simp
    · intro a b ha hb
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  have hLX : L ≤ normalizer (X : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key l hl x hx
    · intro h
      have := key l⁻¹ (inv_mem hl) _ h
      simpa [mul_assoc] using this
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hcs.eq_join]
    refine sup_le (iSup_le fun s => ?_) (hSM.trans hM₀X)
    rintro g ⟨l, hl, rfl⟩
    have hs : (s : G) ∈ normalizer (X : Set G) := hM₀X (hSM s.2)
    have e : (MulAut.conj (s : G)).toMonoidHom l = (s : G) * l * (s : G)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (mul_mem hs (hLX hl)) (inv_mem hs)
  exact noCommonNormal hcs hSM hMT hne X hXS hXne hHX hM₀X

theorem not_conj_le_of_mem_diff (hcs : burnsideC56_CS G T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {x : G}
    (hx : x ∈ M₀) (hxS : x ∉ S) : ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  have hne : S ≠ M₀ := by
    intro h
    apply hxS
    rw [h]
    exact hx
  exact not_conj_le_of_exists hcs h2 (c55 hcs hSM hMT hne) hx hxS


end C56

end CFSG.QuasithinUnique.burnsideC56_P
