module
public import CFSG.Quasithin.Background.RonanE42SetS4
public section
namespace CFSG.Quasithin.RonanE42.Gen
open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
variable {G : Type} [Group G] [Finite G]


theorem mQuot_le_pRank_of_le {K Z A : Subgroup G} (hZK : Z ≤ K) (hAZ : A ≤ Z)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    mQuot A (A ⊓ pCoreOf 2 K) ≤
      CFSG.Open.pRank 2 ((Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
  have hAK : A ≤ K := hAZ.trans hZK
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA2 (a : G) a.2)⟩
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set E := (A.subgroupOf K).map π with hE
  have hcard : Nat.card E = 2 ^ mQuot A (A ⊓ pCoreOf 2 K) := by
    have h1 := Subgroup.relIndex_ker (K := A.subgroupOf K) (f := π)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.relIndex_map_map_of_injective (f := K.subtype) (CFSG.pCore 2 ↥K)
      (A.subgroupOf K) K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK] at h2
    rw [hE, ← h1, ← h2]
    show (pCoreOf 2 K).relIndex A = _
    rw [← Subgroup.inf_relIndex_left (H := A) (K := pCoreOf 2 K)]
    exact relIndex_eq_two_pow hAp _
  have hEl : IsElemAbelian 2 E := by
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
    unfold IsElemAbelian
    refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu2 : u ^ 2 = 1 :=
      Subtype.ext (by simpa using hA2 (u : G) (Subgroup.mem_subgroupOf.mp hu))
    rw [← map_pow, hu2, map_one]
  have hEF : E ≤ (Z.subgroupOf K).map π :=
    Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.2 (hAZ (Subgroup.mem_subgroupOf.1 hu))
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
      E ≤ (Z.subgroupOf K).map π ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card (↥K ⧸ CFSG.pCore 2 ↥K), ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  unfold CFSG.Open.pRank
  exact le_csSup hbdd ⟨E, hEF, hEl, hcard⟩


end CFSG.Quasithin.RonanE42.Gen
