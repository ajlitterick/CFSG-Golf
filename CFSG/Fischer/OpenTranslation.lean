module

public import CFSG.Open.FischerExistenceUniquenessMilestoneDefs
public import CFSG.Fischer.HermitianEquiv

public section

namespace CFSG.Fischer

open CFSG.Open CFSG.Blueprint.Fischer Matrix

variable {X : Type} [Group X]

theorem pair_iff (E : Set X) : Pair X E ↔ Finite X ∧ fischerEUIsPair E := by
  unfold Pair fischerEUIsPair
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩


theorem hermitian_one (x y : V) : hermitian 1 x y = fischerEUHerm x y := by
  unfold hermitian fischerEUHerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

theorem SU_one_eq : SU (1 : Matrix (Fin 6) (Fin 6) K) = fischerEUSU := by
  unfold SU fischerEUSU
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, hermitian_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← Matrix.GeneralLinearGroup.val_det_apply, h1]; rfl, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, h1]; rfl), h2⟩

noncomputable def psuOpenEquiv : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* fischerEUPSU :=
  quotientCenterCongr (MulEquiv.subgroupCongr SU_one_eq)

theorem psuOpenEquiv_mk (u : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    psuOpenEquiv (QuotientGroup.mk u) =
      QuotientGroup.mk (MulEquiv.subgroupCongr SU_one_eq u) :=
  quotientCenterCongr_mk _ _

theorem psuOpenEquiv_image :
    psuOpenEquiv '' Transvections 1 = fischerEUTransvections := by
  ext q
  constructor
  · rintro ⟨_, ⟨u, rfl, v, hv0, hviso, hact⟩, rfl⟩
    refine ⟨MulEquiv.subgroupCongr SU_one_eq u, v, hv0, by rw [← hermitian_one]; exact hviso,
      fun x => ?_, psuOpenEquiv_mk u⟩
    rw [← hermitian_one]
    exact hact x
  · rintro ⟨A, v, hv0, hviso, hact, rfl⟩
    refine ⟨QuotientGroup.mk ((MulEquiv.subgroupCongr SU_one_eq).symm A),
      ⟨(MulEquiv.subgroupCongr SU_one_eq).symm A, rfl, v, hv0, by rw [hermitian_one]; exact hviso,
        fun x => ?_⟩, ?_⟩
    · rw [hermitian_one]
      exact hact x
    · rw [psuOpenEquiv_mk, MulEquiv.apply_symm_apply]


end CFSG.Fischer
