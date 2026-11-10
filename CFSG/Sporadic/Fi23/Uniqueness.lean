module

public import CFSG.Fischer.Uniq.F23Uniq
public import CFSG.Fischer.OpenTranslationHigh
public import CFSG.Sporadic.Fi23.Fischer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fischer_uniqueness_one
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (X : Type) [Group X] (E : Set X) (_hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hT : HasType 1 X E) :
    ∃ iso : X ≃* Carrier 1, iso '' E = D23c := by
  obtain ⟨hZ0, hS0, hT0, -, -⟩ := existence_carrier
  exact F23.exists_mulEquiv hPF hHF hFF (hT : F23 X E) hT0 hZ hZ0 hS hS0


end CFSG.Sporadic.Fi23
