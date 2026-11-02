import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxTextInverse
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCSTToCore

/-! The authored Datalog scalar realization and the generic source-syntax
printer/reader have the same data operations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
def description : ScalarSyntaxCore.Description := ⟨SourceViews.grammar, SourceViews.profile, "dl-scalar:"⟩

theorem description_shape : ScalarSyntaxCore.Shape description :=
  (ScalarSyntaxCore.checkShape_exact description).mp (by decide +kernel)

theorem shared_lexicalRow (sort : String) :
    ScalarSyntaxCore.lexicalRow? description sort = CorePrinter.lexicalRow? sort := by
  unfold ScalarSyntaxCore.lexicalRow? CorePrinter.lexicalRow?
  simp only [description, ScalarCore.lexicalState]
  split <;> simp_all only

theorem shared_leaf (row : ScalarCore.Row) (point : Nat)
    (formed : SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className point) :
    ScalarSyntaxCore.leaf description row point formed = ScalarCore.leaf row point formed := rfl

theorem shared_readLeaf (row : ScalarCore.Row) (pattern : Pattern) :
    ScalarSyntaxCore.readLeaf? description row pattern = ScalarCore.readLeaf? row pattern := rfl

theorem shared_lexical : ScalarSyntaxCore.lexicalPrinter description = CorePrinter.lexical := by
  funext sort
  unfold ScalarSyntaxCore.lexicalPrinter CorePrinter.lexical
  rw [shared_lexicalRow]
  rfl

theorem shared_print (sort : String) (pattern : Pattern) :
    ScalarSyntaxCore.printText? description sort pattern = CorePrinter.printText? sort pattern := by
  unfold ScalarSyntaxCore.printText? ScalarSyntaxCore.printScalars? CorePrinter.printText? CorePrinter.printScalars?
  rw [shared_lexical]
  rfl

theorem shared_lower (sort : String) (tree : PresentationExprSemantics.CST) :
    ScalarSyntaxCore.lowerCST? description sort tree = CSTToCore.lower? sort tree := by
  have lexical : ScalarSyntaxCore.lexicalDecoder description = CSTToCore.lexical := by
    funext sort
    unfold ScalarSyntaxCore.lexicalDecoder CSTToCore.lexical
    rw [shared_lexicalRow]
    rfl
  unfold ScalarSyntaxCore.lowerCST? CSTToCore.lower?
  rw [lexical]
  rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
