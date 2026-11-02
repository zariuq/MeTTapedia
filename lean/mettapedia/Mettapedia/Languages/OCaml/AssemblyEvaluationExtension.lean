import Mettapedia.Languages.OCaml.AssemblyPreservation
import Mettapedia.Languages.OCaml.EvaluationExtension

/-! Append-only arena growth preserves existing evaluation and closure
application with the same constructor declarations and code identities. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.Assembly

theorem Extension.evaluates {before after : Array Instruction} (extension : Extension before after)
    (constructors : List Constructor) (entry : Code) {environment : Environment} {code : Code} {result : Result}
    (evaluated : Evaluates ⟨constructors, before, entry⟩ environment code result) :
    Evaluates ⟨constructors, after, entry⟩ environment code result :=
  Evaluates.mono (before := ⟨constructors, before, entry⟩) (after := ⟨constructors, after, entry⟩)
    extension.lookup (fun _ member => member) evaluated

theorem Extension.applies {before after : Array Instruction} (extension : Extension before after)
    (constructors : List Constructor) (entry : Code) {function argument : Value} {result : Result}
    (applied : Applies ⟨constructors, before, entry⟩ function argument result) :
    Applies ⟨constructors, after, entry⟩ function argument result :=
  Applies.mono (before := ⟨constructors, before, entry⟩) (after := ⟨constructors, after, entry⟩)
    extension.lookup (fun _ member => member) applied

#print axioms Extension.evaluates
#print axioms Extension.applies

end Mettapedia.Languages.OCaml.Assembly
