module

public import CFSG.Open.OrderForm
import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

instance normal_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (NormalSubgroup : Subgroup Ambient)
    [NormalSubgroup.Normal] (equivalence : Ambient ≃* Target) :
    (NormalSubgroup.map equivalence.toMonoidHom).Normal :=
  Subgroup.Normal.map inferInstance equivalence.toMonoidHom equivalence.surjective

theorem nonabelian_of_mulEquiv {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (equivalence : Source ≃* Target)
    (hnonab : ∃ first second : Source, first * second ≠ second * first) :
    ∃ first second : Target, first * second ≠ second * first := by
  obtain ⟨first, second, hne⟩ := hnonab
  refine ⟨equivalence first, equivalence second, ?_⟩
  intro heq
  apply hne
  apply equivalence.injective
  simpa using heq


end CFSG.LargeEvenClassification.Helpers
