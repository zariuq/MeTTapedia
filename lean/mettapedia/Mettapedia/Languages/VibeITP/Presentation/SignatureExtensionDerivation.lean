import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionOperations
import Mettapedia.Languages.VibeITP.Presentation.DerivedTermShape
import Mettapedia.Languages.VibeITP.Spec.Execution

/-!
# Preservation of derivations as a theory grows

Previously derived statements retain their derivations when immutable symbol
data, admitted axioms and admitted definitions are preserved.  The source
theory's hosting invariants supply structural profiles for known statements;
they do not impose a word bound on free-variable arities.  Guarded execution
also preserves the actual observation and its membership in the run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

theorem builtinsFixed_sigExt {source target : Sig} (extension : SigExt source target)
    (builtins : BuiltinsFixed source) : BuiltinsFixed target :=
  fun builtin => extension (.builtin builtin) builtin.info (builtins builtin)

theorem admittedDefinition_parameters_known {theory : Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) (definition : Definition)
    (member : definition ∈ theory.definitions) :
    KnownParameters theory.sig definition.fvars := by
  obtain ⟨_, _, hints, admitted⟩ := hosted.definitionsOk definition member
  exact definitionAdmissible_parameters_known theory.sig definition.fvars hints
    definition.value admitted

theorem executionObservation_termShape {sig : Sig} (builtins : BuiltinsFixed sig)
    (observation : ExecutionObservation) : TermShape sig observation.statement :=
  .app (builtins .executedTo) rfl
    (.cons (.lit _) (.cons (.lit _) (.cons (.lit _) (.cons (.lit _) .nil))))

theorem derivesWithExecution_termShape {theory : Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) {observations : List ExecutionObservation} {statement : Term}
    (derived : DerivesWithExecution theory observations statement) :
    TermShape theory.sig statement := by
  induction derived with
  | «axiom» member =>
      exact wellFormed_termShape theory.sig _ (hosted.axiomsWf _ member).1
  | @definition definition member =>
      exact admittedDefinition_termShape hosted definition member
  | @modusPonens a b _ _ implication _ =>
      obtain ⟨_, _, _, args⟩ := TermShape.app_iff.mp implication
      exact args.of_mem (by simp)
  | @instantiate statement result value F _ valid success statementShape =>
      exact instantiateStatement_termShape theory.sig F value statement result
        (wellFormed_termShape theory.sig value valid) statementShape success
  | litIsNat _ =>
      exact .app (hosted.builtin .litIsNat) rfl (.cons (.lit _) .nil)
  | litLt _ _ =>
      exact .app (hosted.builtin .litLt) rfl (.cons (.lit _) (.cons (.lit _) .nil))
  | litAdd _ _ =>
      exact .app (hosted.builtin .eq) rfl
        (.cons (.app (hosted.builtin .litAdd) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litMul _ _ =>
      exact .app (hosted.builtin .eq) rfl
        (.cons (.app (hosted.builtin .litMul) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litDiv _ _ _ =>
      exact .app (hosted.builtin .eq) rfl
        (.cons (.app (hosted.builtin .litDiv) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litLength _ =>
      exact .app (hosted.builtin .eq) rfl
        (.cons (.app (hosted.builtin .litLength) rfl (.cons (.lit _) .nil))
          (.cons (.lit _) .nil))
  | litGet _ _ =>
      exact .app (hosted.builtin .eq) rfl
        (.cons (.app (hosted.builtin .litGet) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | jit _ _ _ _ => exact executionObservation_termShape hosted.builtin _

theorem derives_with_execution_theory_extension
    {source target : Theory} {allocated : Nat} (hosted : Hosted source allocated)
    (extension : TheoryExt source target) {before after : List ExecutionObservation}
    (included : ∀ observation ∈ before, observation ∈ after) {statement : Term}
    (derived : DerivesWithExecution source before statement) :
    DerivesWithExecution target after statement := by
  induction derived with
  | «axiom» member => exact .axiom (extension.axioms _ member)
  | @definition definition member =>
      rw [← definitionStatement_sigExt extension.sig definition.symbol definition.fvars
        definition.value (admittedDefinition_parameters_known hosted definition member)]
      exact .definition (extension.definitions definition member)
  | modusPonens _ _ implication antecedent => exact .modusPonens implication antecedent
  | @instantiate statement result value F premise valid success transported =>
      exact .instantiate transported (wellFormed_true_sigExt extension.sig valid)
        (instantiateStatement_success_sigExt extension.sig F value statement result
          (wellFormed_termShape source.sig value valid)
          (derivesWithExecution_termShape hosted premise) success)
  | litIsNat bound => exact .litIsNat bound
  | litLt smaller bound => exact .litLt smaller bound
  | litAdd left right => exact .litAdd left right
  | litMul left right => exact .litMul left right
  | litDiv left right nonzero => exact .litDiv left right nonzero
  | litLength valid => exact .litLength valid
  | litGet valid index => exact .litGet valid index
  | jit _ member guarded premise => exact .jit premise (included _ member) guarded

theorem derives_theory_extension {source target : Theory} {allocated : Nat}
    (hosted : Hosted source allocated) (extension : TheoryExt source target)
    {statement : Term} (derived : Spec.Derives source statement) :
    Spec.Derives target statement := by
  apply execution_free_derives_static
  exact derives_with_execution_theory_extension hosted extension (before := []) (after := [])
    (fun _ member => member) (static_derives_with_execution derived [])

end Mettapedia.Languages.VibeITP.Presentation
