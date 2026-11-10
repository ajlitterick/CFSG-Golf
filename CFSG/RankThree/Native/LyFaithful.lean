
module

public import CFSG.RankThree.Native.LyConjugationBase

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native

theorem lyPhi_injective : Function.Injective lyPhi := by
  refine (injective_iff_map_eq_one lyPhi).2 fun g hg => eq_one_of_fix_all fun i => ?_
  have := congrArg (fun p : Equiv.Perm (Fin lyN) => p i) hg
  exact this

theorem lyPhiP_injective : Function.Injective lyPhiP := fun _ _ e =>
  lyPhi_injective (congrArg Subtype.val e)

theorem lyPhiP_bijective : Function.Bijective lyPhiP := ⟨lyPhiP_injective, lyPhiP_surjective⟩

@[expose] def lyPhiEquiv : J ≃* lyP := MulEquiv.ofBijective lyPhiP lyPhiP_bijective


@[expose] def lyEquivP : CFSG.Blueprint.NativeSporadic.Ly ≃* lyP := lyEquivJ.trans lyPhiEquiv


end CFSG.RankThree.Native
