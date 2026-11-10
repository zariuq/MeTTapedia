import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPayloads
import Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra

/-! # Binding-tree payloads constructed by the authored grammar

The routes below use physical constructor positions in the existing structural
compiler's output. Their token lists are produced by the generic grammar
algebra. The tree projection is proved equal to the independent binding-tree
codec, so the codec's tags, arities and field order are checked against the
authored rows rather than asserted to match them.

Every binding tree has an actual grammar derivation, at arbitrary finite depth.
This is the printing-to-derivation direction and its structural readback law;
uniqueness among all parses of the printed text is a separate result.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

abbrev Route := ConstructionTree (syntaxAlgebra rules)

def indexRoute : Nat → Route "TcIndex"
  | 0 => .apply (.at ⟨0, by decide +kernel⟩) .nil
  | n + 1 => .apply (.at ⟨1, by decide +kernel⟩) (.cons (indexRoute n) .nil)

def headRoute : Head → Route "TcHead"
  | .symbol n => .apply (.at ⟨2, by decide +kernel⟩) (.cons (indexRoute n) .nil)
  | .name n => .apply (.at ⟨3, by decide +kernel⟩) (.cons (indexRoute n) .nil)
  | .hole n => .apply (.at ⟨4, by decide +kernel⟩) (.cons (indexRoute n) .nil)
  | .quotedRule n => .apply (.at ⟨5, by decide +kernel⟩) (.cons (indexRoute n) .nil)

mutual
  def termRoute : Term → Route "TcTerm"
    | .idx index => .apply (.at ⟨6, by decide +kernel⟩) (.cons (indexRoute index) .nil)
    | .node head fields => .apply (.at ⟨7, by decide +kernel⟩)
        (.cons (headRoute head) (.cons (fieldsRoute fields) .nil))

  def fieldsRoute : Fields → Route "TcFields"
    | .nil => .apply (.at ⟨8, by decide +kernel⟩) .nil
    | .cons depth term rest => .apply (.at ⟨9, by decide +kernel⟩)
        (.cons (indexRoute depth) (.cons (termRoute term) (.cons (fieldsRoute rest) .nil)))
end

theorem indexRoute_tree (index : Nat) :
    ((syntaxAlgebra rules).evaluate (indexRoute index)).tree = indexPattern index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change Pattern.apply "TcSucc" [((syntaxAlgebra rules).evaluate (indexRoute index)).tree] =
      Pattern.apply "TcSucc" [indexPattern index]
    rw [ih]

theorem headRoute_tree (head : Head) :
    ((syntaxAlgebra rules).evaluate (headRoute head)).tree = headPattern head := by
  cases head with
  | symbol n =>
    change Pattern.apply "TcSymbol" [((syntaxAlgebra rules).evaluate (indexRoute n)).tree] = _
    rw [indexRoute_tree]
    rfl
  | name n =>
    change Pattern.apply "TcName" [((syntaxAlgebra rules).evaluate (indexRoute n)).tree] = _
    rw [indexRoute_tree]
    rfl
  | hole n =>
    change Pattern.apply "TcHole" [((syntaxAlgebra rules).evaluate (indexRoute n)).tree] = _
    rw [indexRoute_tree]
    rfl
  | quotedRule n =>
    change Pattern.apply "TcQuotedRule" [((syntaxAlgebra rules).evaluate (indexRoute n)).tree] = _
    rw [indexRoute_tree]
    rfl

mutual
  theorem termRoute_tree (term : Term) :
      ((syntaxAlgebra rules).evaluate (termRoute term)).tree = termPattern term := by
    cases term with
    | idx index =>
      change Pattern.apply "TcVar" [((syntaxAlgebra rules).evaluate (indexRoute index)).tree] = _
      rw [indexRoute_tree]
      rfl
    | node head fields =>
      change Pattern.apply "TcNode" [((syntaxAlgebra rules).evaluate (headRoute head)).tree,
        ((syntaxAlgebra rules).evaluate (fieldsRoute fields)).tree] = _
      rw [headRoute_tree, fieldsRoute_tree fields]
      rfl
  termination_by sizeOf term

  theorem fieldsRoute_tree (fields : Fields) :
      ((syntaxAlgebra rules).evaluate (fieldsRoute fields)).tree = fieldsPattern fields := by
    cases fields with
    | nil => rfl
    | cons depth term rest =>
      change Pattern.apply "TcFieldsCons" [((syntaxAlgebra rules).evaluate (indexRoute depth)).tree,
        ((syntaxAlgebra rules).evaluate (termRoute term)).tree,
        ((syntaxAlgebra rules).evaluate (fieldsRoute rest)).tree] = _
      rw [indexRoute_tree, termRoute_tree term, fieldsRoute_tree rest]
      rfl
  termination_by sizeOf fields
end

def printTokens (term : Term) : List String :=
  ((syntaxAlgebra rules).evaluate (termRoute term)).tokens

/-- Every printed payload is licensed by the original authored source rows. -/
theorem printed_derivation (term : Term) :
    GrammarDerives.Derives dataLanguage "TcTerm" (printTokens term) (termPattern term) := by
  have derived := evaluate_source_derives data_compiles (termRoute term)
  simpa only [printTokens, termRoute_tree] using derived

theorem printed_tree_readback (term : Term) :
    readTerm ((syntaxAlgebra rules).evaluate (termRoute term)).tree = some term := by
  rw [termRoute_tree, readTerm_pattern]

theorem printed_checked_readback (signature : Head → List Nat) (depth : Nat)
    (term : {term : Term // Admitted signature depth term}) :
    readAdmitted signature depth ((syntaxAlgebra rules).evaluate (termRoute term.1)).tree =
      some term := by
  rw [termRoute_tree, admitted_roundtrip]

theorem binder_printing : printTokens boundIdentity =
    ["(", "node", "(", "symbol", "z", ")", "(", "field", "(", "s", "z", ")",
      "(", "var", "z", ")", "fields-end", ")", ")"] := by decide +kernel

theorem quoted_handle_printing : printTokens (.node (.quotedRule 0) .nil) =
    ["(", "node", "(", "quoted-rule", "z", ")", "fields-end", ")"] := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads
