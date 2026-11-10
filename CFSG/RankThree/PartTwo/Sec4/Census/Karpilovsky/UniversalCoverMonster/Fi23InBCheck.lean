module

public import Certificates.Certificate291200
public import CFSG.Sporadic.Bridge.Fi23Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.Sporadic.GLQ CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Fi23GPL.Native

section Inst


abbrev SM : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2)) :=
  NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2

abbrev mA : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1

abbrev mB : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2

theorem fi23InB_check : mA * mA = 1 ∧ mB * mB * mB = 1 ∧
    ∀ x y : NativeSporadic.B, ((x : SM) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = mA →
      ((y : SM) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = mB →
      Fi23ImgFacts (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2) :=
  Certificates.certificate291200

theorem mA_sq : mA ^ 2 = 1 := by
  rw [pow_two]
  exact fi23InB_check.1

theorem mB_cube : mB ^ 3 = 1 := by
  rw [pow_three']
  exact fi23InB_check.2.1

theorem mA_mem : mA ∈ SM := Submonoid.subset_closure (Set.mem_insert _ _)

theorem mB_mem : mB ∈ SM := Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def gA : SMˣ := unitOf SM mA_mem two_ne_zero mA_sq

@[expose] noncomputable def gB : SMˣ := unitOf SM mB_mem three_ne_zero mB_cube


theorem φ_gA : valHom SM gA = mA := valHom_unitOf SM _ _ _

theorem φ_gB : valHom SM gB = mB := valHom_unitOf SM _ _ _


@[expose] noncomputable def Rg : ℕ → SMˣ := runProg (initRegs gA gB) slp


@[expose] noncomputable def img (k : ℕ) : SMˣ := signedWord (Rg 1) (Rg 2) imgWords[k]!


theorem img_facts : Fi23ImgFacts (Rg 1) (Rg 2) := fi23InB_check.2.2 gA gB φ_gA φ_gB

theorem img_sq {k : ℕ} (hk : k < 10) : img k ^ 2 = 1 := img_facts.1 k hk

theorem img_inv {k : ℕ} (hk : k < 10) : (img k)⁻¹ = img k :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact img_sq hk)


theorem relators_eval : ∀ v ∈ rels, wordProd img v = 1 := img_facts.2.1

theorem img_zero_ne_one : img 0 ≠ 1 := img_facts.2.2

theorem relators_eval' :
    ∀ v ∈ TauCeti.SporadicName.Fi23.presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  have hv' : v ∈ TauCeti.Sporadic.fi23Presentation.relatorLetters := hv
  rw [Fi23.relatorLetters_eq] at hv'
  exact relators_eval v hv'

@[expose] noncomputable def toB :
    TauCeti.SporadicName.Fi23.presentation.Group →* SMˣ :=
  presHom TauCeti.SporadicName.Fi23.presentation img relators_eval'

theorem exists_injective_of_simple {G H K : Type} [Group G] [Group H] [Group K] [IsSimpleGroup G]
    (e : G ≃* H) (φ : H →* K) (x : H) (hx : φ x ≠ 1) : ∃ f : G →* K, Function.Injective f := by
  refine ⟨φ.comp e.toMonoidHom, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.comp e.toMonoidHom).ker with
    h | h
  · exact h
  · exfalso
    have : e.symm x ∈ (φ.comp e.toMonoidHom).ker := by rw [h]; trivial
    simp at this
    exact hx this

theorem exists_injective_fi23_carrier_B :
    ∃ f : NativeSporadic.Carrier .Fi23 →* NativeSporadic.Carrier .B, Function.Injective f := by
  obtain ⟨e⟩ := Fi23.nonempty_mulEquiv
  have : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hx : toB (presGen TauCeti.SporadicName.Fi23.presentation 0) ≠ 1 := by
    rw [toB, presHom_presGen _ _ _ (by rw [show TauCeti.SporadicName.Fi23.presentation =
      TauCeti.Sporadic.fi23Presentation from rfl, Fi23.generatorCount_eq]; omega)]
    exact img_zero_ne_one
  exact exists_injective_of_simple (G := NativeSporadic.Carrier .Fi23) (K := NativeSporadic.Carrier .B) e toB _ hx

end Inst

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
