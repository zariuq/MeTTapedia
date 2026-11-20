import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorCertificates

/-!
# Administrative source moves preserve normal-evaluator certificates

The public entry, driver choice, scanner entry and held-result returns keep
their actual constraint stores and continuation frames. The public bind
reads back its original done reply before certifying an output. A machine
residual whose determined code has the active head cannot pass that bind.
Call and embedded-scanner preservation are separate components.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPhaseMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalEvaluatorCertificates (Certificate Reaches CorrectOutput publicFrame payload scanBody envelop)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)
  {initial : Tower.Tm 0} {K : List (Constraint (BinderCore.keys built.rules) [] ())}
  {world nextWorld : World (BinderCore.keys built.rules) [] ()}
  {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}

theorem initial_move (initial : Tower.Tm 0)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨[], .eval (NormalProgram.query built initial), [], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases moved with
  | letStart =>
      intro child member live
      rw [Multiset.mem_singleton.mp member] at live ⊢
      refine .evaluating initial
        (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (NormalProgram.code initial)) .refl ⟨live, ?_⟩
      intro X target assignment _
      exact Rigid.instantiate_include assignment _

theorem choosing_move (current : Tower.Tm 0) (scope : Nat)
    (reached : Reaches built initial current)
    (input : Determines K (payload built scope) (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (NormalEvaluatorGrounding.bodyAt built .evaluate (payload built scope)),
        [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases moved with
  | choice =>
      intro child member _
      rcases Multiset.mem_cons.mp member with rfl | later
      · exact .startingScan current scope reached input
      · rw [Multiset.mem_singleton.mp later]
        exact .machine current (NormalProgram.seekAt (payload built scope)) _ reached
          (NormalEvaluatorMachineView.initial built current) (NormalEvaluatorGrounding.determines_seekAt built input)

theorem startingScan_move (current : Tower.Tm 0) (scope : Nat)
    (reached : Reaches built initial current)
    (input : Determines K (payload built scope) (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (scanBody built D scope), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases moved with
  | letStart =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact .scanning current scope
        ⟨K, .eval (.apply (NormalScanner.scanAt (payload built scope))), [], []⟩ reached input
        (.scan (payload built scope) ⟨0, current⟩ [] input .done)

theorem machineValue_move (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (head : closedHead code = some activeTag) (input : Determines K call code)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value call, [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  let result := PublicQuery.result RuntimeSubstitution.rules built.authored
  let site := PublicQuery.site RuntimeSubstitution.rules built.authored
  change Move D (NormalProgram.program built D) supply world
    ⟨K, .value call, [.bindTo site (PublicReadout.pattern result) (.ret result)], []⟩ nextWorld children at moved
  cases moved with
  | letBind =>
      intro child member live
      rw [Multiset.mem_singleton.mp member] at live ⊢
      obtain ⟨X, target, assignment, solved⟩ := live
      obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
      have bound := (models_singleton assignment _).mp added
      dsimp only at bound
      have left := literalHead_instantiate assignment
        (literalHead_instantiate (openAt (BinderCore.keys built.rules) site world.scope)
          (show literalHead (PublicReadout.pattern result) = some doneTag from rfl))
      have original := input.2 target assignment old
      have heads := congrArg literalHead bound
      have right : literalHead (instantiate assignment call) = some activeTag :=
        (congrArg literalHead original).trans ((literalHead_include target code).trans head)
      have same : some doneTag = some activeTag := left.symm.trans (heads.trans right)
      exact False.elim (active_done_distinct (Option.some.inj same.symm))

theorem returningDone_move (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
    (input : Determines K datum (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.ret (NormalProgram.doneAt datum)), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases moved with
  | ret =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact .repliedDone current datum reached normal input

theorem repliedDone_move (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
    (input : Determines K datum (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value (NormalProgram.doneAt datum), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  let result := PublicQuery.result RuntimeSubstitution.rules built.authored
  let site := PublicQuery.site RuntimeSubstitution.rules built.authored
  change Move D (NormalProgram.program built D) supply world
    ⟨K, .value (NormalProgram.doneAt datum), [.bindTo site (PublicReadout.pattern result) (.ret result)], []⟩
    nextWorld children at moved
  cases moved with
  | letBind =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      apply Certificate.returning
      intro value read
      have original := PublicReadout.bind_reads_original K result (NormalProgram.doneAt datum) site world.scope value read
      have reply := ((NormalEvaluatorCertificates.determines_done built input).reads_iff (doneC value)).mp original
      have same : value = encodeTm current :=
        (List.cons.inj (DataEmbedding.nodeC_eq_iff.mp reply).2).1
      exact ⟨current, same, reached, normal⟩

theorem returning_move (datum : Data (BinderCore.keys built.rules) [] ())
    (correct : CorrectOutput built initial K datum)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.ret datum), [], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases moved with
  | ret =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact .finished datum correct

theorem finished_move (datum : Data (BinderCore.keys built.rules) [] ())
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value datum, [], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child :=
  False.elim (Move.value_still moved)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPhaseMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPhaseMoves.machineValue_move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPhaseMoves.repliedDone_move
