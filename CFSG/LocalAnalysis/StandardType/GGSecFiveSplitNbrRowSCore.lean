module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCover
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenTag modelUniv_eq
  lieModel_unique_even)

theorem ggSplitLie_of_lieModel
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    (hp : p.Prime) (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hpf : p ∣ 2 ^ f - 1) [Finite (ggU t n f).K]
    (hsplit : 2 ≤ f → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU t n f).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : (ggU t n f).K →* E, ∀ g, π (s g) = g)
    (hK : commutator ↥K = ⊤) (hX : LieModel (↥K ⧸ Subgroup.center ↥K) t n 2 f) :
    GGSplitLie p K := by
  have hadm := hX.admissible
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by have := hadm.2.1; omega
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpf))
  have hev : EvenTag t := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hiso : ∀ M : LieUniversal, M = ggU t n f →
      LieModel (M.K ⧸ Subgroup.center M.K) t n 2 f →
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := by
    rintro M rfl hY
    exact lieModel_unique_even hev hX hY
  obtain ⟨φ, hφ, hker⟩ := ggExists_universal_cover_of_marking hK
    (hiso _ (modelUniv_eq hev n 2 f Nat.prime_two)
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 f Nat.prime_two hev.isFundTag
        hadm).2)
    fun E _ _ π hπ hc => (hsplit hf E π hπ hc).imp fun s hs => MonoidHom.ext hs
  refine ⟨t, n, f, K.subtype.comp φ, hadm,
    fun x hx => hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hx))), ?_, ht, hpf⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end CFSG.StandardType

end
