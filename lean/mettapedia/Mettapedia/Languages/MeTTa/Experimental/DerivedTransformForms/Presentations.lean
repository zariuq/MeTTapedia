import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport

/-!
# Candidate expression and interaction presentations

Both grammars use the existing authored module format, structural compiler
and lexical profile. Explicit field interpretation follows trivia erasure;
concrete syntax and retained parse trees remain different.
Neither candidate changes a shipped dialect or selects a Prime foundation.

Grammar elaboration and portable recovery do not alone establish lowering or
evaluation correctness. Those are downstream interpretation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Presentations

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

namespace ExpressionSurface
#module_tree "../../../../../../../metta/gslt/module/derived-transform/Expressions.module" as Authored
#module_roundtrip Expressions
def description? := SourceSyntax.description? Expressions.library Expressions.module
#guard Authored.language.isOk
#guard description?.isSome
#guard (description?.bind SourceSyntaxExport.plan?).any (fun plan =>
  (SourceSyntaxExport.missingCategories plan).isEmpty)
end ExpressionSurface

namespace InteractionSurface
#module_tree "../../../../../../../metta/gslt/module/derived-transform/Interactions.module" as Authored
#module_roundtrip Interactions
def description? := SourceSyntax.description? Interactions.library Interactions.module
#guard Authored.language.isOk
#guard description?.isSome
#guard (description?.bind SourceSyntaxExport.plan?).any (fun plan =>
  (SourceSyntaxExport.missingCategories plan).isEmpty)
end InteractionSurface

/- An explicit syntax control preserves two source derivations. It is not
one of the candidate execution presentations or an implicit selection rule. -/
namespace AmbiguityControl
#module_tree "../../../../../../../metta/gslt/module/derived-transform/Ambiguity.module" as Authored
#module_roundtrip Ambiguity
def description? := SourceSyntax.description? Ambiguity.library Ambiguity.module
#guard Authored.language.isOk
#guard description?.isSome
end AmbiguityControl

theorem expression_description_roundtrip :
    (ExpressionSurface.description?.map Portable.renderSyntax).bind Portable.readSyntax? = ExpressionSurface.description? :=
  SourceSyntax.optional_text_roundtrip _

theorem interaction_description_roundtrip :
    (InteractionSurface.description?.map Portable.renderSyntax).bind Portable.readSyntax? = InteractionSurface.description? :=
  SourceSyntax.optional_text_roundtrip _

inductive Surface where
  | expression
  | interaction
  deriving DecidableEq, Repr

def description? : Surface → Option Portable.SyntaxDescription
  | .expression => ExpressionSurface.description?
  | .interaction => InteractionSurface.description?

end Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Presentations
