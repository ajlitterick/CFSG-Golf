module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.LocalAnalysis.StandardType.GGK0ProducerAssembly
import CFSG.LocalAnalysis.StandardType.GGK0LangMarkUntw
import CFSG.LocalAnalysis.StandardType.GGK0LangMarkTw
import CFSG.LocalAnalysis.StandardType.GGK0LQAlgClosure

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Assembly CFSG.StandardType

theorem f4Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .F4 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inl rfl))

theorem e6Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E6 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inl rfl)))

theorem twE6Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .twE6 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure k0LangMark_hA_tw

theorem e7Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E7 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inr (Or.inl rfl))))

theorem e8Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E8 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.StandardType.GGK0MarkedKacIface1587
