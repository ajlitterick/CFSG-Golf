module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeBender
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeM11
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem inCatalog_of_fusionIsBenderGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (h : fusionIsBenderGroup X) :
    CFSG.Assembly.InCatalog X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact inCatalog_of_mulEquiv_psl_two_galoisField_two hf e
  · exact inCatalog_of_mulEquiv_psu3 hnonab hf e
  · exact inCatalog_of_mulEquiv_sz ha e


end CFSG.QuasithinUnique
