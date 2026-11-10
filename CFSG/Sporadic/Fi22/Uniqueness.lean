module

public import CFSG.Fischer.Uniq.F22Uniq
public import CFSG.Fischer.OpenTranslation
public import CFSG.Sporadic.Fi22.Fischer

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fischer_uniqueness_zero
    (hPF : PolarFacts) (X : Type) [Group X] (E : Set X)
    (_hP : Pair X E) (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
    (hT : HasType 0 X E) : ∃ iso : X ≃* Carrier 0, iso '' E = D22 := by
  obtain ⟨hZ0, hS0, hT0, -, -⟩ := existence_carrier
  exact F22.exists_mulEquiv hPF (hT : F22 X E) hT0 hZ hZ0 hS hS0


end CFSG.Sporadic.Fi22
