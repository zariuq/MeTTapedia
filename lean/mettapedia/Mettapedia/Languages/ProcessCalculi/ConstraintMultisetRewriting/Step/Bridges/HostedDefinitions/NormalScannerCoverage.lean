import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerIsolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerGrounding

/-!
# All live scanner alternatives have the actual native constructor's fields

Coverage reads every possible selected equation of the assembled source
program. Literal-head isolation first places it in the scanner table; the
determined encoded input then identifies its exact constructor. The resulting
constraint store, control shape and field dependencies are those of the
actual call branch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCoverage

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev)

theorem matched_kind (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor)
    {n : Nat} (term : Tower.Tm n) (determined : Determines K datum (encodeTm term))
    (live : Solvable (NormalScannerGrounding.matchStore built scope K datum ctor)) :
    ctor = NormalScannerGrounding.kind term := by
  have pattern := NormalScannerGrounding.copied_pattern_determines built scope K datum ctor
    (encodeTm term) determined live
  obtain ⟨X, target, assignment, solved⟩ := live
  have read := pattern.2 target assignment solved
  have lhs := literalHead_instantiate assignment
    (literalHead_instantiate (copyAt (BinderCore.keys built.rules) scope)
      (show literalHead (NormalScanner.pattern built ctor) = some ctor.tag from rfl))
  have rhs : literalHead (Rigid.includeTerm target (encodeTm term)) =
      some (NormalScannerGrounding.kind term).tag := by
    rw [NormalScannerGrounding.encode_instance, NormalScanner.include_nodeAt]
    rfl
  have tags := congrArg literalHead read
  rw [lhs, rhs] at tags
  exact NormalScannerIsolation.constructor_tag_injective (Option.some.inj tags)

theorem live_clause (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K (NormalScanner.scanAt datum) frames pending clause).store)
    {n : Nat} (term : Tower.Tm n) (determined : Determines K datum (encodeTm term)) :
    clause = NormalScanner.equation built D (NormalScannerGrounding.kind term) := by
  obtain ⟨ctor, rfl⟩ := NormalScannerIsolation.live_callBranch_clause built D scope K datum frames pending member live
  have same := matched_kind built scope K datum ctor term determined live
  exact congrArg (NormalScanner.equation built D) same

theorem live_callBranch (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K (NormalScanner.scanAt datum) frames pending clause).store)
    {n : Nat} (term : Tower.Tm n) (determined : Determines K datum (encodeTm term)) :
    let ctor := NormalScannerGrounding.kind term
    let child := callBranch D scope K (NormalScanner.scanAt datum) frames pending clause
    clause = NormalScanner.equation built D ctor ∧
      child = ⟨NormalScannerGrounding.matchStore built scope K datum ctor,
        .eval (NormalScanner.rootTest built
          (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.pattern built ctor))
          ((NormalScanner.childTests built ctor).inst (copyAt (BinderCore.keys built.rules) scope))),
        frames, pending⟩ ∧
      ∀ index ∈ ctor.fields,
        Determines child.store
          (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built index))
          (NormalScannerGrounding.values term index) := by
  have same := live_clause built D scope K datum frames pending member live term determined
  subst clause
  refine ⟨rfl, NormalScannerGrounding.callBranch_shape built D scope K datum _ frames pending, ?_⟩
  intro index used
  exact NormalScannerGrounding.copied_field_determines built scope K datum _
    (NormalScannerGrounding.values term) (encodeTm term) (NormalScannerGrounding.encode_instance term)
    determined live index used

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCoverage

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCoverage.live_callBranch
