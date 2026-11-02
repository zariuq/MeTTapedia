import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourcePatternBinding
import Mettapedia.Languages.OCaml.Evaluation

/-! Nearest source-name lookup reaches the same opaque value through the
actual variable-reference assembler and independent indexed evaluation.
The converse forbids reading a different or outer binding at that index. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering

open Mettapedia.Languages
open Mettapedia.Languages.OCaml

theorem resolveName_reflects (context : Context) (entries : List (String × OCaml.Value)) (name : String)
    (index : Nat) (value : OCaml.Value) (aligned : entries.map Prod.fst = context.names)
    (resolved : resolveName? context name = some index) (found : (entries.map Prod.snd)[index]? = some value) :
    List.NamedEnvironment.Lookup name value entries := by
  apply (List.NamedEnvironment.lookup_iff entries name value).mp
  rw [resolveName_lookup context entries name aligned, resolved]
  exact found

theorem resolveName_evaluates (context : Context) (entries : List (String × OCaml.Value)) (name : String) (value : OCaml.Value)
    (arena : Array Instruction) (constructors : List Constructor)
    (aligned : entries.map Prod.fst = context.names) (looked : List.NamedEnvironment.Lookup name value entries) :
    ∃ index, resolveName? context name = some index ∧
      let installed := (Assembly.variableRef index).run arena
      Evaluates ⟨constructors, installed.2, installed.1⟩ (entries.map Prod.snd) installed.1 (.ok value) := by
  have found := (List.NamedEnvironment.lookup_iff entries name value).mpr looked
  rw [resolveName_lookup context entries name aligned] at found
  cases resolved : resolveName? context name with
  | none => simp [resolved] at found
  | some index =>
    have slot : (entries.map Prod.snd)[index]? = some value := by simpa only [resolved, Option.bind_some] using found
    refine ⟨index, rfl, .variable ?_ slot⟩
    exact Assembly.emit_installed (.variable index) arena

theorem resolveName_none_iff (context : Context) (name : String) :
    resolveName? context name = none ↔ name ∉ context.names := List.idxOf?_eq_none_iff

#print axioms resolveName_reflects
#print axioms resolveName_evaluates
#print axioms resolveName_none_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
