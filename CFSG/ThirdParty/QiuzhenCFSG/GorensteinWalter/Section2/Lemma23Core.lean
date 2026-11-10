module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970 -- the [1]-statements 1.6/1.7 (sorrys until the Bender1970_* modules land; then re-exported proved)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample -- minimalCounterexample_isSimple
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23IIHelpers -- oddCore_inversion_of_disjoint

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2 lemma 2.3 applications below the wrapper

The paper's Lemma 2.3 is cited wholesale from Bender [1, §1.6/7] ("On groups
with abelian Sylow 2-subgroups", Math. Z. 117 (1970), 164–176;
`books/bender-abelian-sylow2.pdf`).  This module sits BELOW
`GorensteinWalter.Section2.Basic` and holds the provable applications of the
[1]-statements that the per-theorem modules (`Lemma24`, `Lemma25`, `Lemma27`,
`Lemma28`, `Theorem26`, `Theorem210`) need — it was extracted from the
old `Section2/Lemma23.lean` (which imports `Basic`, making its helpers
unreachable from the per-theorem modules without a landing cycle).

Content:

* `lemma_2_3_ii_inverts_of_core_disjoint` — a legacy odd-core inversion
  utility (`oddCore_inversion_of_disjoint`), retained for callers that
  genuinely use `O_{2ᶜ}(M)`;
* `lemma_2_3_equalityAlternative_of_Fstar_contained` — the equality
  alternative of Lemma 2.3(iii) from [1, 1.6];
* `lemma_2_3_ii_coreDisjoint_prime_of_Fstar_le` — the first conjunct of
  Lemma 2.3(ii) for primes outside `π(F(Ĥ))` from [1, 1.7(i)], given
  `F*(Ĥ) ≤ M`;
* `lemma_2_3_ii_coreDisjoint_prime_of_controlCore` — the same from the
  control-core bridge.

These odd-core statements are not the paper's Lemma 2.3(ii).  The corrected
owner `Section2/Lemma23II.lean` formalizes
`F_{πᶜ}(M) = O_{πᶜ}(F(M))` for `π = π(F(Ĥ))` and proves it directly
from Bender 1.7(i).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## Legacy odd-core inversion utility

Given the first conjunct (`F₂'(M) ∩ Ĥ = 1`), the inversion conclusion follows
from Fact 1.5(ii): `D := O₂'(M)` is a `2'`-group acted on by the involution
`t` (`D ⊴ M` and `t ∈ M`), and its `t`-fixed part is trivial because
`C_D(t) = D ∩ C_G(t) = D ∩ H ≤ D ∩ Ĥ = 1` (the setup gives
`H = C_G(t) ≤ Ĥ`).  Fact 1.5(ii) then decomposes every `x ∈ D` uniquely as
`x = c · i` with `c` fixed by `t` and `i` inverted by `t`; the fixed part is
trivial, so `x` itself is inverted by `t`.
-/


/-! ## Lemma 2.3(iii): the equality alternative via Bender [1, 1.6]

The paper's Lemma 2.3(iii) ("if we also have `M ↝ Ĥ`, then `Ĥ = M` unless
`F*(Ĥ)` and `F*(M)` are p-groups") is [1, 1.6] applied to the maximal pair
`(A, M)`: "Let A and B be different maximal subgroups of a simple group G
such that `F*(A) ⊆ B` and `F*(B) ⊆ A`.  Then `F*(A)` and `F*(B)` are
p-groups (for the same prime p)".  The relation-level bridge from the two
`NormalizerControlledBy` hypotheses is the control-core route of
`GorensteinWalter/Section2/ControlCore.lean` (the direct containment
bridge is false in general — see the module header); the containments are
therefore explicit hypotheses below, making this theorem a stronger
corollary of `lemma_2_3_of_controlCore`.  The `A = M` branch
is discharged first (repo protocol: prune easy branches early).
-/


/-! ## Prime-wise Bender 1.7(i) consequences

For every prime outside `π(F(Ĥ))`, [1, 1.7(i)] — "O_q(B) ∩ A = 1 for
`q ∈ π(F(A))'`" — applies with `A := Ĥ`, `B := M`, and the subnormal
subgroup `S := F*(Ĥ)` of `F*(Ĥ)` (the centralizer condition
`C_{F*(Ĥ)}(S) ≤ S` is then trivially `Z(F*(Ĥ)) ≤ F*(Ĥ)`), giving
`O_q(M) ∩ Ĥ = 1` for every prime `q ∉ π(F(Ĥ))`.  The hypotheses needed:
`G` simple (from `hmin` via `minimalCounterexample_isSimple`), `Ĥ` maximal
(from the setup), and the bridge `F*(Ĥ) ≤ M` (an explicit hypothesis — not
derivable from `NormalizerControlledBy`, see the module header).  The
corrected Lemma 2.3(ii) uses only the primes outside `π(F(Ĥ))`,
because its subgroup is `O_{πᶜ}(F(M))`.
-/


end CFSG.GorensteinWalter
