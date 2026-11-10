module

public import CFSG.Goldschmidt.Steps.StrongEmb
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.Monster.B.GSide

open CFSG.BenderSuzuki

variable {G : Type*} [Group G]

theorem isConj_of_mem_of_isStronglyEmbeddedOrder [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) {t u : G} (ht : orderOf t = 2) (hu : orderOf u = 2)
    (htM : t ∈ M) (huM : u ∈ M) : IsConj t u := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra h
    push Not at h
    exact hM.1 (eq_top_iff.2 fun g _ => h g)
  have hgu : g * u * g⁻¹ ∉ M := fun h => by
    have h' := CFSG.Goldschmidt.mem_of_involution_conj_mem hM hu huM (g := g⁻¹)
      (by rwa [inv_inv])
    exact hg (by simpa using M.inv_mem h')
  have hgu2 : orderOf (g * u * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  exact (CFSG.Goldschmidt.isConj_of_mem_of_not_mem hM ht hgu2 htM hgu).trans
    (isConj_iff.2 ⟨g⁻¹, by group⟩)

theorem exists_conj_eq_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) {t u : G} (ht : orderOf t = 2) (htM : t ∈ M) (huM : u ∈ M)
    (htu : IsConj t u) : ∃ m ∈ M, m * t * m⁻¹ = u := by
  obtain ⟨c, hc⟩ := isConj_iff.1 htu
  refine ⟨c, ?_, hc⟩
  have h := CFSG.Goldschmidt.mem_of_involution_conj_mem hM ht htM (g := c⁻¹)
    (by rw [inv_inv, hc]; exact huM)
  simpa using M.inv_mem h

theorem isStronglyEmbeddedOrder_fusion [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) :
    (∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M) ∧
    (∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → orderOf u = 2 → IsConj t u) ∧
    (∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → IsConj t u → ∃ m ∈ M, m * t * m⁻¹ = u) :=
  ⟨fun _ htM ht => CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hM ht htM,
    fun _ htM _ huM ht hu => isConj_of_mem_of_isStronglyEmbeddedOrder hM ht hu htM huM,
    fun _ htM _ huM ht htu => exists_conj_eq_of_isStronglyEmbeddedOrder hM ht htM huM htu⟩


theorem mem_of_conj_mem_of_centralizer_le {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {g a : G} (ha : a ∈ D₀)
    (hga : g * a * g⁻¹ ∈ D₀) : g ∈ M := by
  obtain ⟨m, hmM, hm⟩ := hD₀ a ha _ hga
  have hcent : m⁻¹ * g ∈ Subgroup.centralizer {a} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * g * a = m⁻¹ * (g * a * g⁻¹) * g := by group
      _ = m⁻¹ * (m * a * m⁻¹) * g := by rw [hm]
      _ = a * (m⁻¹ * g) := by group
  simpa using M.mul_mem hmM (hC₀ a ha hcent)

theorem normalizer_le_of_conj_class {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {D : Set G}
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀) {X : Subgroup G} (hXM : X ≤ M) (hXD : ∃ a ∈ X, a ∈ D₀) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  intro n hn
  obtain ⟨a, haX, haD₀⟩ := hXD
  have hnaX : n * a * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn a).1 haX
  exact mem_of_conj_mem_of_centralizer_le hD₀ hC₀ haD₀
    (hDM _ (hDconj a (hD₀D haD₀) n) (hXM hnaX))


end CFSG.Monster.B.GSide
