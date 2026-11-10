module

public import CFSG.Milestones.ASVolI.K1
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.Quasithin.Background.C124YLA6Grp
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C1PackSolvP
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase

public section

namespace CFSG.ASVolI

open CFSG.Open

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] {s : ℕ}

@[expose] def burnsideK312_sg (F : Type) [Field F] [CharP F 2] (s : ℕ) : F →+* F :=
  iterateFrobenius F 2 s

theorem burnsideK312_sg_apply (x : F) : burnsideK312_sg F s x = x ^ 2 ^ s := by
  show iterateFrobenius F 2 s x = _
  rw [iterateFrobenius_def]


@[expose] def burnsideK312_K (F : Type) [Field F] [CharP F 2] (s : ℕ) : Subfield F :=
  RingHom.eqLocusField (burnsideK312_sg F s) (RingHom.id F)

theorem burnsideK312_mem_K {x : F} : x ∈ burnsideK312_K F s ↔ x ^ 2 ^ s = x := by
  show burnsideK312_sg F s x = (RingHom.id F) x ↔ _
  rw [burnsideK312_sg_apply]
  rfl

theorem burnsideK312_card_K (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) :
    Nat.card ↥(burnsideK312_K F s) = 2 ^ s := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * s) := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [← CFSG.Quasithin.B45L2.card_frob_fixed hs hF']
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => burnsideK312_mem_K)

theorem burnsideK312_exists_notFixed (hs : 1 ≤ s) (hF : Nat.card F = 2 ^ (2 * s)) :
    ∃ ω : F, ω ^ 2 ^ s ≠ ω := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card ↥(burnsideK312_K F s) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun x => burnsideK312_mem_K.2 (hcon x))
  rw [burnsideK312_card_K hs hF, hF] at h1
  have : 2 ^ s < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega


end Field

section Coord

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2]


end Coord

section TConj

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {s : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]


end TConj

section Syl

open scoped MatrixGroups Matrix
open CFSG.Quasithin.B45L2 (rootSub card_rootSub rootSub_sq rootSub_comm)

variable {E : Type} [Field E] [Finite E] [CharP E 2]

theorem burnsideK312_card_rootSub : Nat.card (rootSub (⊤ : AddSubgroup E)) = Nat.card E := by
  rw [card_rootSub]
  exact Nat.card_congr (AddSubgroup.topEquiv (G := E)).toEquiv

theorem burnsideK312_even_card : Even (Nat.card E) := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)

theorem burnsideK312_card_SL2 :
    Nat.card SL(2, E) = Nat.card E * (Nat.card E ^ 2 - 1) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have h := Matrix.card_SL_field (𝔽 := E) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h, Nat.card_eq_fintype_card (α := E)]
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have e1 : Fintype.card E ^ 2 - Fintype.card E = Fintype.card E * (Fintype.card E - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1]
  ring

theorem burnsideK312_isPGroup_rootSub : IsPGroup 2 (rootSub (⊤ : AddSubgroup E)) := fun g =>
  ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using rootSub_sq (⊤ : AddSubgroup E) g.1 g.2)⟩

theorem burnsideK312_sylow_conj {Y : Subgroup SL(2, E)} (hY : IsPGroup 2 Y) :
    ∃ x : SL(2, E), Y ≤ (rootSub (⊤ : AddSubgroup E)).map (MulAut.conj x).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := rootSub (⊤ : AddSubgroup E) with hP
  have hPc : Nat.card P = Nat.card E := burnsideK312_card_rootSub
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hidx : P.index = Nat.card E ^ 2 - 1 := by
    have h := Subgroup.index_mul_card P
    rw [hPc, burnsideK312_card_SL2] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))
  have hodd : ¬ 2 ∣ P.index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := burnsideK312_even_card (E := E)
    have h2 : 2 ≤ Nat.card E := by
      have : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hk1 : 1 ≤ k := by omega
    have e : Nat.card E ^ 2 = 4 * (k * k) := by rw [hk]; ring
    have hkk : 1 ≤ k * k := Nat.mul_pos hk1 hk1
    rw [e]
    omega
  let Pu : Sylow 2 SL(2, E) := burnsideK312_isPGroup_rootSub.toSylow hodd
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, E) Pu Q
  refine ⟨g, hYQ.trans ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact le_rfl


end Syl


section Extract

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end Extract


section Cl

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end Cl


section Geo

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end Geo


section RU

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end RU


section RU2

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end RU2


section RU3

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end RU3


section W

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end W


section RO

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin


end RO


section AS1

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique


end AS1


section AS2

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique


end AS2


section AS3

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique


end AS3


section S1

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique


end S1


section AS4

open scoped Matrix MatrixGroups
open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique

section


end

end AS4

end CFSG.ASVolI
