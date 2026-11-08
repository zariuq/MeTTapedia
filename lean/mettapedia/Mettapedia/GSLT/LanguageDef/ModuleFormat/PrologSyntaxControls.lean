import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO
import Mettapedia.Logic.Prolog.ReaderTermRegression

/-! Profile separation and shared .module loading controls. These qualify
the declared sentence grammar; they do not assert full ISO/SWI coverage. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxControls
open Mettapedia.Logic.Prolog ReaderProfile ReaderTermRegression
open scoped ModuleSource.Loader

-- Lexical scalar sorts and structural escape sorts have distinct roles.
#guard (ScalarSyntaxCore.admit? (SourceSyntaxIO.description (PrologSyntax.description iso))).isSome
#guard (ScalarSyntaxCore.admit? (SourceSyntaxIO.description (PrologSyntax.description swi))).isSome
#guard (ScalarSyntaxCore.admit? (SourceSyntaxIO.description CHRPrologSyntax.description)).isSome

namespace ISOCase
#module_tree "../../../../../../metta/gslt/module/prolog/ISOSyntax.module" as Loaded
#guard PrologSyntaxModule.profile? Loaded.library Loaded.module = some iso
#guard (SourceSyntax.description? Loaded.library Loaded.module).map (·.grammar.terms) =
  some (PrologSyntax.grammar iso).terms
#guard (SourceSyntax.description? Loaded.library Loaded.module).map (·.profile) = some (PrologSyntax.lexical iso)
#guard SourceSyntax.selection? Loaded.library Loaded.module = some (PrologSyntax.selection iso)
end ISOCase

namespace SWICase
#module_tree "../../../../../../metta/gslt/module/prolog/SWISyntax.module" as Loaded
#guard PrologSyntaxModule.profile? Loaded.library Loaded.module = some swi
#guard (SourceSyntax.description? Loaded.library Loaded.module).map (·.grammar.terms) =
  some (PrologSyntax.grammar swi).terms
#guard (SourceSyntax.description? Loaded.library Loaded.module).map (·.profile) = some (PrologSyntax.lexical swi)
#guard SourceSyntax.selection? Loaded.library Loaded.module = some (PrologSyntax.selection swi)
end SWICase

def read (profile : Profile) (source : String) : Option Shape :=
  (ReaderTerm.readOneWith profile profile.operators source).toOption.map (fun result => shape result.term)

#guard read iso "f()." == none
#guard read swi "f()." == some (.compound "f" [])
#guard read iso "a '+' b." == some (.compound "+" [.atom "a", .atom "b"])
#guard read swi "a '+' b." == none
#guard read swi "\"ab\"." == some (.string "ab")
#guard read iso "\"ab\"." == read iso "[97,98]."
#guard read iso "`ab`." == none
#guard read swi "`ab`." == read swi "[97,98]."
#guard read iso "12_345." == none
#guard read swi "12_345." == some (.integer 12345)
#guard read iso "edge(X,X,_,_)." == read swi "edge(X,X,_,_)."
#guard read iso "a *-> b." == none
#guard (read swi "a *-> b.").isSome
#guard read swi "[]." == some .nil
#guard read swi "'[]'." == some (.atom "[]")
#guard read iso "[]." == read iso "'[]'."
#guard read iso "[a]." == read iso "'.'(a,[])."
#guard read swi "[a]." != read swi "'.'(a,[])."

#guard read swi "'\\x3bb\\'." == some (.atom "λ")
#guard read swi "'\\141'." == some (.atom "a")
#guard read swi "'\\u03bc'." == some (.atom "μ")
#guard read swi "0'\\x41\\." == some (.integer 65)
#guard read swi "'\\uD800'." == none
#guard !(PrologSyntax.extensionRows iso).any (fun r => r.label == "pl:escape-unicode-four")
#guard (PrologSyntax.extensionRows swi).any (fun r => r.label == "pl:escape-unicode-four")

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxControls
