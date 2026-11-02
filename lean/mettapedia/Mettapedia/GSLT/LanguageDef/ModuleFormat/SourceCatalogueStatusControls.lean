import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueStatus
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIOControls
import Mettapedia.GSLT.Parsing.ClassAwareCatalogueControls

/-! Invalid input is separate from unfinished or differing catalogues. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue.Controls

open Mettapedia.GSLT.Parsing

theorem malformed_forest_is_invalid :
    check SourceSyntaxIO.Controls.spec [] "x" [] [] [] 10 = .invalid := by decide_cbv

def request : Request := ⟨ClassAwareCatalogueValidation.Controls.forest, [97],
  ClassAwareCatalogueValidation.Controls.root,
  [ClassAwareCatalogueValidation.Controls.proof 0, ClassAwareCatalogueValidation.Controls.proof 1]⟩

theorem valid_request_pending : request.run? [] 0 = none := rfl
theorem valid_request_complete : request.run? [] 3 = some true := by decide_cbv
theorem missing_native_output_differs : {request with native := []}.run? [] 3 = some false := by decide_cbv

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue.Controls
