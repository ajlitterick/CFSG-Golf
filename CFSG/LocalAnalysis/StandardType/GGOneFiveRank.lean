module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped Pointwise


variable {G : Type} [Group G]

theorem isElemAbelian_map_conj {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map h _

variable [Finite G]

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ q ∈ Q, q ∈ Subgroup.normalizer (P : Set G) ∧ q ∉ P := by
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hPQ.not_ge fun q hq => (Subgroup.subgroupOf_eq_top.mp h) hq
  obtain ⟨q, hqN, hqP⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨q, q.2, ?_, hqP⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have := (Subgroup.mem_normalizer_iff.mp hqN ⟨k, hPQ.le hk⟩).mp hk
    exact this
  · intro hk
    have hkQ : k ∈ Q := by
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem q.2) (hPQ.le hk)) q.2
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hqN ⟨k, hkQ⟩).mpr hk

theorem isMaxPSubgroup_of_normalizer_le {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → P ≤ Q → Q = P)
    (hN : Subgroup.normalizer (P : Set G) ≤ M) :
    ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q → Q = P := by
  intro Q hQ hPQ
  by_contra hne
  obtain ⟨q, hqQ, hqN, hqP⟩ :=
    exists_mem_normalizer_not_mem hQ (lt_of_le_of_ne hPQ (Ne.symm hne))
  have hR : Q ⊓ Subgroup.normalizer (P : Set G) = P :=
    hmax _ (inf_le_right.trans hN) (hQ.to_le inf_le_left) (le_inf hPQ Subgroup.le_normalizer)
  exact hqP (hR ▸ ⟨hqQ, hqN⟩)


end CFSG.StandardType
