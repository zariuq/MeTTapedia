import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport

/-! Compositional source syntax for OCaml O0, Maude M0 and textual Core
Erlang. These modules author source forms only. Parsing a form does not admit
its operations, equation theory or compiler-generated primitives for execution.
Packed alternatives are retained until a separate selection policy is applied. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

def closedPack (description : Option Portable.SyntaxDescription) : Bool :=
  (description.bind SourceSyntaxExport.plan?).any fun plan =>
    (SourceSyntaxExport.missingCategories plan).isEmpty

namespace OCaml
#module_tree "../../../../../../metta/gslt/module/gold/OCaml/Syntax.module" as Authored
def description? : Option Portable.SyntaxDescription :=
  SourceSyntax.description? Syntax.library Syntax.module
def selection? : Option (List SourceSyntax.FamilyFilter) :=
  SourceSyntax.selection? Syntax.library Syntax.module
#guard Authored.language.isOk
#guard description?.isSome
#guard selection?.isSome
#guard closedPack description?
#module_roundtrip Syntax
end OCaml

namespace Maude
#module_tree "../../../../../../metta/gslt/module/gold/Maude/Syntax.module" as Authored
def description? : Option Portable.SyntaxDescription :=
  SourceSyntax.description? Syntax.library Syntax.module
def selection? : Option (List SourceSyntax.FamilyFilter) :=
  SourceSyntax.selection? Syntax.library Syntax.module
#guard Authored.language.isOk
#guard description?.isSome
#guard selection?.isSome
#guard closedPack description?
#module_roundtrip Syntax
end Maude

namespace Erlang
#module_tree "../../../../../../metta/gslt/module/gold/Erlang/Syntax.module" as Authored
def description? : Option Portable.SyntaxDescription :=
  SourceSyntax.description? Syntax.library Syntax.module
def selection? : Option (List SourceSyntax.FamilyFilter) :=
  SourceSyntax.selection? Syntax.library Syntax.module
#guard Authored.language.isOk
#guard description?.isSome
#guard selection?.isSome
#guard closedPack description?
#module_roundtrip Syntax
end Erlang

#guard (SourceSyntax.lexicalReplyAt? OCaml.Syntax.library OCaml.Syntax.module
  "MissingProfile" SourceSyntax.profileRequest).isNone
#guard (SourceSyntax.lexicalReplyAt? Maude.Syntax.library Maude.Syntax.module
  "ReturnLexicalProfile" (.apply "WrongRequest" [])).isNone

#guard OCaml.selection?.any (fun filters =>
  !(filters.all (SourceSyntax.FamilyFilter.allows "SrcLowerName" [105, 102] [])))
#guard OCaml.selection?.any (fun filters =>
  filters.all (SourceSyntax.FamilyFilter.allows "SrcLowerName" [105, 102, 120] []))
#guard OCaml.selection?.any (fun filters =>
  !(filters.all (SourceSyntax.FamilyFilter.allows "SrcLowerName" [105, 102] [120])))

#guard ((OCaml.description?.bind SourceSyntaxExport.plan?).map fun plan =>
  let missing := { plan with lexical := { plan.lexical with startSort := "MissingSourceCategory" } }
  (SourceSyntaxExport.missingCategories missing).contains "MissingSourceCategory") == some true

#print axioms SourceSyntax.optional_text_roundtrip

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
