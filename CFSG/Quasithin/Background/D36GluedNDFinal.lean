module

public import CFSG.Quasithin.Background.D36GluedNDNum
public import CFSG.Quasithin.Background.D36GluedNDL27
public import CFSG.Quasithin.Background.D36GluedNDEven
import CFSG.Quasithin.Background.F918J2
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z7aTypes

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique


@[expose] def D36Inner : Prop :=
  D3L38 → ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W), D36Norm M Mp T L V t →
    ∀ g ∈ T, ∀ m ∈ L, g ∈ stabSub (commSub (orbSup T V) L) →
      (∀ v ∈ orbSup T V, (g * g) v = v) → (∀ v ∈ orbSup T V, (m * m) v = v) →
      (∀ l ∈ L, ∀ v ∈ orbSup T V, (g * l * g⁻¹) v = (m * l * m⁻¹) v) →
      ∀ u ∈ commSub (orbSup T V) L, g u = m u

section Normalized

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}


theorem d36nd_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) {g : MulAut W} (hgT : g ∈ T)
    (hgU : g ∈ stabSub (commSub (orbSup T V) L)) :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hz : g ∈ Mp ⊔ T := Subgroup.mem_sup_right hgT
  rcases d36t_conj_cases hL38 n hz with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    have hgV : g ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V hgT
    have h1 : (commSub (orbSup T V) L).map g.toMonoidHom =
        commSub (orbSup T V) (conjAutSub g L) := d36t_map_U hgV
    have h2 : (commSub (orbSup T V) L).map g.toMonoidHom = commSub (orbSup T V) L :=
      mem_stabSub_iff_map_eq.mp hgU
    have h3 : commSub (orbSup T V) L = (commSub (orbSup T V) L).map t.toMonoidHom :=
      calc commSub (orbSup T V) L = (commSub (orbSup T V) L).map g.toMonoidHom := h2.symm
        _ = commSub (orbSup T V) (conjAutSub g L) := h1
        _ = commSub (orbSup T V) (conjAutSub t L) := by rw [h]
        _ = (commSub (orbSup T V) L).map t.toMonoidHom := (d36t_Ut_eq n).symm
    have hrank := d36t_rank hL38 n
    rw [← h3, inf_idem] at hrank
    omega


end Normalized


end CFSG.Quasithin
