import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformList

/-!
# Lawful extensional operations and a typed non-natural operation table

The full extensional host satisfies the local compiler substitution laws.
The counterexample changes only the availability of its already typed
reflexivity operation: closed contexts reject it, nonempty contexts retain
it. All operation typing laws still hold, but substitution cannot preserve
that availability. This distinguishes type preservation from naturality.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation Mettapedia.Logic

theorem UniformList.rawOperations_natural : UniformList.rawOperations.Natural := by
  constructor
  · intro n m sigma
    rfl
  · intro n m sigma type left comparison
    simp [UniformList.rawOperations]
  · intro n m sigma type left first second
    simp [UniformList.rawOperations]
  · intro n m sigma left right forward backward
    simp [UniformList.rawOperations,
      FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp, subst]
  · intro n m sigma comparison
    rfl
  · intro n m sigma result function argument comparison
    simp [UniformList.rawOperations]
  · intro n m sigma result function argument comparison
    simp [UniformList.rawOperations]
  · intro n m sigma domain codomain function other pointwise
    simp [UniformList.rawOperations,
      FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp, subst]

namespace ScopeSensitiveControl

open FormationSensitiveHOLInterface

/-- A negative control, not a recommended compiler host. Its operation terms
remain certified at their actual target proof families. -/
def operations : Operations FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName :=
  { UniformList.operations with
    raw := { UniformList.rawOperations with
      reflexivity := fun {n} => if n = 0 then none else UniformList.rawOperations.reflexivity }
    reflexivity_typed := by
      intro n context type left right out emitted leftTyped rightTyped conversion
      change (if n = 0 then none else UniformList.rawOperations.reflexivity) = some out at emitted
      split at emitted
      · contradiction
      · exact UniformList.operations.reflexivity_typed emitted leftTyped rightTyped conversion }

theorem not_natural : ¬ operations.raw.Natural := by
  intro natural
  have availability := natural.reflexivity (n := 0) (m := 1) Fin.elim0
  simp [operations, UniformList.rawOperations] at availability

/-- A genuine source reflexivity proof, independent of declarations. -/
def source : HOL.ProofSyntax HOL.UniformListInduction.Symbol (Γ := []) []
    (.eq (HOL.Term.lam (τ := HOL.Ty.prop) (.var .vz))
      (HOL.Term.lam (τ := HOL.Ty.prop) (.var .vz))) :=
  .eqRefl (.lam (.var .vz))

theorem rejected_closed :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      operations source (n := 0) Fin.elim0 Fin.elim0 = none := rfl

theorem emitted_open :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      operations source (n := 1) Fin.elim0 Fin.elim0 =
      some FormationSensitiveHOLLeibnizDerived.reflTerm := rfl

/-- The same source proof changes from rejection to acceptance under the
unique empty-context substitution, despite every operation being typed. -/
theorem compile_does_not_commute :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
        operations source (n := 1) Fin.elim0 Fin.elim0 ≠
      (compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
        operations source (n := 0) Fin.elim0 Fin.elim0).map
          (subst (Fin.elim0 : Sub Tower.Head 0 1)) := by
  rw [rejected_closed, emitted_open]
  intro impossible
  cases impossible

end ScopeSensitiveControl

#print axioms UniformList.rawOperations_natural
#print axioms ScopeSensitiveControl.not_natural
#print axioms ScopeSensitiveControl.compile_does_not_commute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
