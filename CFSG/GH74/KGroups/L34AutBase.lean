
module

public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.L34Base
public import CFSG.GH74.KGroups.L34AutInputs
public meta import CFSG.GH74.KGroups.L34AutInputs

@[expose] public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

section Consequences


end Consequences

end CFSG.GH74.KGroups.L34
