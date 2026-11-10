module

public import CFSG.LieType.AlgebraicGroups.TorusPointSubgroups
public import CFSG.LieType.Chevalley.DiagonalCharTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralEmbed
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralClauses
public import CFSG.Permutation.FiveTransitive.KernelImageGeneration
public import CFSG.LocalAnalysis.StandardType.GGE6MaximalCentralizerTorsion

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]

section E6
open CFSG.StandardType.E6NonToralThree CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem connected_centralizer_le_torus_of_regular
    (hchar : ringChar k ≠ 3)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 k)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 k ⟨e, hEM he⟩ ∈
      CFSG.StandardType.TableBExc.E6Three.modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 k ⟨e, hEM he⟩ ≠
      CFSG.StandardType.TableBExc.E6Three.gE6 i) :
    closedIdentityComponent (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) ≤
      torusGroup .E6 k := by
  let Z := adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  let T := torusGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))
  have hEZ : E ≤ Z := by
    intro e he
    refine ⟨monomialSubgroup_le_adjointGroup' (hEM he), ?_⟩
    change e ∈ centralizer (E : Set (ModGL .E6 k))
    rw [mem_centralizer_iff]
    intro x hx
    exact hE.comm hx he
  have hZT : ∀ z ∈ Z, ∃ e ∈ E, ∃ t ∈ T, z = e * t := by
    intro z hz
    obtain ⟨e, he, t, ht, hc, hzt⟩ :=
      exists_mul_torus_of_commute hchar hEM hE hcard hET hAS hAg hz.1
        (fun x hx => (mem_centralizer_iff.mp hz.2 x hx).symm)
    refine ⟨e, he, t, ⟨ht, ?_⟩, hzt⟩
    change t ∈ centralizer (E : Set (ModGL .E6 k))
    rw [mem_centralizer_iff]
    intro x hx
    exact (hc x hx).symm
  have : (T.subgroupOf Z).FiniteIndex := finiteIndex_subgroupOf_of_finite_left_factor hEZ hZT
  have hT := isPointClosed_inf (isPointClosed_torusGroup (τ := Tag.E6) (k := k))
    (isPointClosed_centralizer (E : Set (ModGL .E6 k)))
  exact (closedIdentityComponent_le_of_isPointClosed_finiteIndex hT).trans inf_le_left

theorem cube_mem_original_centralizer_identityComponent
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 k}
    (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) :
    x ^ 3 ∈ closedIdentityComponent
      (adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg,hEM,hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 k))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hET : ¬ E' ≤ torusGroup .E6 k := by
    intro h
    exact hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg E).mp
      ⟨1,one_mem _,fun e he => by simpa using h he⟩)
  let f := (MulAut.conj g).toMonoidHom
  have hx' : f x ∈ adjointGroup .E6 k ⊓ centralizer (E' : Set (ModGL .E6 k)) := by
    rw [← map_adjoint_centralizer_conj E hg]
    exact mem_map_of_mem f hx
  have hc := cube_mem_closedIdentityComponent_of_mem_centralizer
    (by rw [ringChar.eq k 2]; decide) hEM hE' hcard' hET
      (fun e he => (hreg e he).1) (fun e he i => (hreg e he).2 i) hx'
  rw [← map_pow, ← map_adjoint_centralizer_conj E hg, closedIdentityComponent_map_conj] at hc
  obtain ⟨y,hy,hye⟩ := Subgroup.mem_map.mp hc
  have heq : y = x ^ 3 := (MulAut.conj g).injective hye
  exact heq ▸ hy


theorem connected_centralizer_conj_le_torus
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) :
    ∃ g ∈ adjointGroup .E6 L,
      closedIdentityComponent (adjointGroup .E6 L ⊓ centralizer
        (E.map (MulAut.conj g).toMonoidHom : Set (ModGL .E6 L))) ≤ torusGroup .E6 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgG, hEM, hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 L))) hE
  let E' := E.map (MulAut.conj g).toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hnt' : ¬ CFSG.StandardType.SCFourCover.E6AdToral E' := fun h =>
    hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hgG E).mp h)
  have hET : ¬ E' ≤ torusGroup .E6 L := by
    intro h
    apply hnt'
    refine ⟨1, one_mem _, fun e he => ?_⟩
    simpa using h he
  have : Finite E' := Finite.of_surjective _ ((MulAut.conj g).toMonoidHom.subgroupMap_surjective E)
  refine ⟨g, hgG, connected_centralizer_le_torus_of_regular
    (by rw [ringChar.eq L 2]; decide : ringChar L ≠ 3) hEM hE' hcard' hET (fun e he => (hreg e he).1)
      (fun e he i => (hreg e he).2 i)⟩

theorem eq_one_of_mem_original_centralizer_of_pow_two_pow_eq_one
    [CharP k 2]
    (halg : letI := ZMod.algebra k 2; Algebra.IsAlgebraic (ZMod 2) k)
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 k}
    (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))
    {m : ℕ} (hxm : x ^ (2 ^ m) = 1) : x = 1 := by
  have hx3 := cube_mem_original_centralizer_identityComponent halg hEG hE hcard hnt hx
  obtain ⟨g,hg,hST⟩ := connected_centralizer_conj_le_torus halg hEG hE hcard hnt
  let f := (MulAut.conj g).toMonoidHom
  have hx3T : f (x ^ 3) ∈ torusGroup .E6 k := by
    apply hST
    rw [← map_adjoint_centralizer_conj E hg, closedIdentityComponent_map_conj]
    exact mem_map_of_mem f hx3
  have hx32 : f (x ^ 3) ^ (2 ^ m) = 1 := by
    rw [← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hxm, one_pow, map_one]
  have hx31 : f (x ^ 3) = 1 :=
    eq_one_of_mem_diagonalGroup_of_pow_two_pow_eq_one
      (torusGroup_le_diagonalGroup hx3T) hx32
  have hx3one : x ^ 3 = 1 := (MulAut.conj g).injective (hx31.trans (map_one f).symm)
  exact (pow_eq_one_iff_of_coprime ((by decide : Nat.Coprime 3 2).pow_right m)).mp ⟨hx3one,hxm⟩


open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three


end E6
end CFSG.LieType.AlgebraicGroups
