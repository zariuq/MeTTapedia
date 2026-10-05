import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaDataBindings
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaExpressionScope

/-!
# The observation of a MeTTa chain substitution

The independent minimal machine replaces the chain variable structurally.
Its observation is exactly a valuation update, including symbolic replacement
values. Closed guest data is unchanged by that target substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open MeTTaData
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)

theorem substituteName_solution (atom : Atom) (name : String) (replacement : Atom)
    (valuation : String → Metta.Atom) :
    applyClassSolution valuation (toLeaTTaAtom (substituteName name replacement atom)) =
      applyClassSolution
        (Function.update valuation name (applyClassSolution valuation (toLeaTTaAtom replacement)))
        (toLeaTTaAtom atom) := by
  cases atom with
  | symbol | grounded => simp only [substituteName, toLeaTTaAtom, applyClassSolution]
  | var other =>
      by_cases same : other = name
      · subst other
        simp only [substituteName, if_true, toLeaTTaAtom, applyClassSolution,
          Function.update_self]
      · simp only [substituteName, same, if_false, toLeaTTaAtom, applyClassSolution,
          Function.update_of_ne same]
  | expression items =>
      simp only [substituteName, toLeaTTaAtom, applyClassSolution,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map, Metta.Atom.expr.injEq]
      apply List.map_congr_left
      intro item member
      exact substituteName_solution item name replacement valuation
termination_by sizeOf atom

theorem substituteName_data {atom : Atom} (data : DataAtom atom)
    (name : String) (replacement : Atom) :
    substituteName name replacement atom = atom := by
  induction data with
  | symbol | grounded => simp only [substituteName]
  | expression children ih =>
      simp only [substituteName, Atom.expression.injEq]
      calc
        _ = List.map id _ := List.map_congr_left (fun item member => ih item member)
        _ = _ := List.map_id _

/-- Even a guest variable spelled like a chain binder remains inert data. -/
theorem chain_cannot_capture_guest_variable (name : String) (replacement : Atom) :
    substituteName name replacement (MeTTaData.encode (.var name)) =
      MeTTaData.encode (.var name) :=
  substituteName_data (encode_data (.var name)) name replacement

/-- An actual target variable is replaced; quotation is what protects the guest. -/
theorem chain_replaces_target_variable (name : String) (replacement : Atom) :
    substituteName name replacement (.var name) = replacement := by
  simp only [substituteName, if_true]

@[simp] theorem substituteName_call (name : String) (replacement : Atom)
    (head : String) (arguments : List Atom) :
    substituteName name replacement (call head arguments) =
      call head (arguments.map (substituteName name replacement)) := by
  simp only [call, substituteName, List.map_cons]

@[simp] theorem substituteName_sequence (name : String) (replacement : Atom)
    (arguments : List Atom) :
    substituteName name replacement (sequenceAtom arguments) =
      sequenceAtom (arguments.map (substituteName name replacement)) := by
  induction arguments with
  | nil => simp [sequenceAtom, substituteName]
  | cons head rest ih => simp [sequenceAtom, ih]

@[simp] theorem substituteName_encoded (name : String) (replacement : Atom) (term : Term) :
    substituteName name replacement (MeTTaData.encode term) = MeTTaData.encode term :=
  substituteName_data (encode_data term) name replacement

/-- Substitution changes supplied operands, never dispatch identity or the
distinction between an authored function, primitive and data constructor. -/
theorem substituteName_invoke (name : String) (replacement : Atom)
    (program : Program) (fuel : Atom) (head : String) (arguments : List Atom) :
    substituteName name replacement (invoke program fuel head arguments) =
      invoke program (substituteName name replacement fuel) head
        (arguments.map (substituteName name replacement)) := by
  unfold invoke
  split
  · simp
  · split <;> simp [value, substituteName]

private theorem earlier_name_untouched (replacement : Atom) (index next : Nat)
    (before : index < next) :
    substituteName (freshName index) replacement (.var (freshName next)) =
      .var (freshName next) := by
  have different : freshName next ≠ freshName index := by
    intro same
    have equalIndex := freshName_injective same
    omega
  simp only [substituteName, different, if_false]

/-- The generated temporary is later than the name being filled in. This
transport law includes the allocation state, rather than only the printed
control expression. -/
theorem substituteName_bindResult (replacement source name body : Atom)
    (index first : Nat) (before : index < first) :
    (substituteName (freshName index) replacement (bindResult source name body first).1,
      (bindResult source name body first).2) =
      bindResult (substituteName (freshName index) replacement source)
        (substituteName (freshName index) replacement name)
        (substituteName (freshName index) replacement body) first := by
  change (substituteName (freshName index) replacement
    (call "chain" [call "function" [source], .var (freshName first),
      resultBranches (.var (freshName first)) name body]), first + 1) = _
  simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
    substituteName_call, List.map_cons, List.map_nil, returned, value,
    earlier_name_untouched replacement index first before, substituteName]
  rfl

/-- Filling an older operand leaves both the return convention and newly
allocated control names unchanged. The invocation retains its call head. -/
theorem substituteName_returnInvocation (replacement : Atom) (head : String)
    (arguments : List Atom) (index first : Nat) (before : index < first) :
    (substituteName (freshName index) replacement
        (returnInvocation (call head arguments) first).1,
      (returnInvocation (call head arguments) first).2) =
      returnInvocation (call head (arguments.map (substituteName (freshName index) replacement)))
        first := by
  have next := earlier_name_untouched replacement index (first + 1) (by omega)
  have current := earlier_name_untouched replacement index first before
  by_cases primitive : head = "nik:primitive"
  · subst head
    change (substituteName (freshName index) replacement
      (call "chain" [call "context-space" [], .var (freshName first),
        call "chain" [call "metta" [call "nik:primitive" arguments, .symbol "%Undefined%",
          .var (freshName first)], .var (freshName (first + 1)),
          returned (.var (freshName (first + 1)))]]), first + 2) = _
    simp only [returned, substituteName_call, List.map_cons, List.map_nil, current, next,
      substituteName]
    rfl
  · by_cases tagged : head = "nik:Value"
    · subst head
      cases arguments with
      | nil =>
        change (substituteName (freshName index) replacement
          (call "chain" [call "eval" [call "nik:Value" []], .var (freshName first),
            returned (.var (freshName first))]), first + 1) = _
        simp only [returned, substituteName_call, List.map_cons, List.map_nil, current]
        rfl
      | cons argument rest =>
        cases rest with
        | nil =>
          change (substituteName (freshName index) replacement
            (returned (call "nik:Value" [argument])), first) = _
          simp only [returned, substituteName_call, List.map_cons, List.map_nil]
          rfl
        | cons nextArgument rest =>
          change (substituteName (freshName index) replacement
            (call "chain" [call "eval" [call "nik:Value" (argument :: nextArgument :: rest)],
              .var (freshName first), returned (.var (freshName first))]), first + 1) = _
          simp only [returned, substituteName_call, List.map_cons, List.map_nil, current]
          rfl
    · have shape (items : List Atom) : returnInvocation (call head items) first =
          (call "chain" [call "eval" [call head items], .var (freshName first),
            returned (.var (freshName first))], first + 1) := by
        simp [returnInvocation, call, primitive, tagged, fresh]
        rfl
      rw [shape, shape]
      simp [returned, current]

/-- Transport a fuel guard together with its body and allocation state.
Only names allocated before the guard may be filled in by this law. -/
theorem substituteName_withFuel (replacement fuel : Atom)
    (build transformedBuild : Atom → Emit Atom) (index first : Nat)
    (before : index < first)
    (later : first ≤ (build (.var (freshName first)) (first + 1)).2)
    (body : (substituteName (freshName index) replacement
        (build (.var (freshName first)) (first + 1)).1,
      (build (.var (freshName first)) (first + 1)).2) =
        transformedBuild (.var (freshName first)) (first + 1)) :
    (substituteName (freshName index) replacement (withFuel fuel build first).1,
      (withFuel fuel build first).2) =
      withFuel (substituteName (freshName index) replacement fuel) transformedBuild first := by
  let original := build (.var (freshName first)) (first + 1)
  let transformed := transformedBuild (.var (freshName first)) (first + 1)
  change first ≤ original.2 at later
  change (substituteName (freshName index) replacement original.1, original.2) = transformed at body
  change (substituteName (freshName index) replacement
    (call "chain" [call "eval" [call "==" [fuel, .grounded (.int 0)]],
      .var (freshName original.2),
      call "unify" [.var (freshName original.2), .grounded (.bool true),
        returned (.symbol "nik:Exhausted"),
        call "chain" [call "eval" [call "-" [fuel, .grounded (.int 1)]],
          .var (freshName first), original.1]]]), original.2 + 1) =
    (call "chain" [call "eval" [call "==" [substituteName (freshName index) replacement fuel,
      .grounded (.int 0)]], .var (freshName transformed.2),
      call "unify" [.var (freshName transformed.2), .grounded (.bool true),
        returned (.symbol "nik:Exhausted"),
        call "chain" [call "eval" [call "-" [substituteName (freshName index) replacement fuel,
          .grounded (.int 1)]], .var (freshName first), transformed.1]]], transformed.2 + 1)
  rw [← body]
  simp only [returned, substituteName_call, List.map_cons, List.map_nil,
    earlier_name_untouched replacement index original.2 (by omega),
    earlier_name_untouched replacement index first before, substituteName]

private theorem substitute_names_lookup (names : Names) (name marker : String)
    (replacement : Atom) :
    (names.map (fun entry => (entry.1, substituteName marker replacement entry.2))).find?
        (fun entry => entry.1 == name) =
      (names.find? (fun entry => entry.1 == name)).map
        (fun entry => (entry.1, substituteName marker replacement entry.2)) := by
  induction names with
  | nil => rfl
  | cons entry rest ih =>
    by_cases same : entry.1 == name <;> simp [List.find?, same, ih]

theorem substituteName_returnInvoke (replacement fuel : Atom) (program : Program)
    (head : String) (arguments : List Atom) (index first : Nat) (before : index < first) :
    (substituteName (freshName index) replacement
        (returnInvocation (invoke program fuel head arguments) first).1,
      (returnInvocation (invoke program fuel head arguments) first).2) =
      returnInvocation (invoke program (substituteName (freshName index) replacement fuel)
        head (arguments.map (substituteName (freshName index) replacement))) first := by
  have formed : ∃ symbol operands, invoke program fuel head arguments = call symbol operands := by
    unfold invoke
    split
    · exact ⟨_, _, rfl⟩
    · split <;> exact ⟨_, _, rfl⟩
  rw [← substituteName_invoke]
  obtain ⟨symbol, operands, shape⟩ := formed
  rw [shape, substituteName_call]
  exact substituteName_returnInvocation replacement symbol operands index first before

mutual

/-- Filling a previously allocated variable commutes with compilation of
every source expression. The name table is transformed while the source
program, source term and allocation state remain unchanged. -/
theorem expression_substitution (program : Program) (names : Names) (fuel replacement : Atom)
    (source : Term) (index first : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    (substituteName (freshName index) replacement (expression program names fuel source first).1,
      (expression program names fuel source first).2) =
      expression program
        (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
        (substituteName (freshName index) replacement fuel) source first := by
  have allocation := (expression_scope program names fuel source first namesBound fuelBound).1
  unfold expression at allocation ⊢
  apply substituteName_withFuel replacement fuel _ _ index first before
  · change first < _ + 1 at allocation
    simpa only [freshName] using Nat.le_of_lt_succ allocation
  · have remainingBound : UsesBefore (first + 1) (.var (freshName first)) := by simp
    have namesNext : ∀ entry ∈ names, UsesBefore (first + 1) entry.2 :=
      fun entry member => (namesBound entry member).mono (Nat.le_succ first)
    have remainingSame := earlier_name_untouched replacement index first before
    split
    case h_1 =>
      rename_i name
      rw [substitute_names_lookup]
      cases found : names.find? (fun entry => entry.1 == name) with
      | none =>
        change (substituteName (freshName index) replacement (returned (.symbol "nik:Failure")),
          first + 1) = (returned (.symbol "nik:Failure"), first + 1)
        simp [returned, substituteName]
      | some entry =>
        rcases entry with ⟨label, target⟩
        change (substituteName (freshName index) replacement (returned (value target)), first + 1) =
          (returned (value (substituteName (freshName index) replacement target)), first + 1)
        simp [returned, value]
    case h_2 | h_3 | h_4 | h_8 =>
      change (substituteName (freshName index) replacement (returned (value (encode _))),
        first + 1) = _
      simp only [returned, value, substituteName_call, List.map_cons, List.map_nil,
        substituteName_encoded]
      rfl
    case h_7 | h_9 =>
      change (substituteName (freshName index) replacement (returned (.symbol "nik:Failure")),
        first + 1) = _
      simp only [returned, substituteName_call, List.map_cons, List.map_nil, substituteName]
      rfl
    case h_5 | h_11 =>
      conv_rhs => rw [← remainingSame]
      apply expressions_substitution program names (.var (freshName first)) replacement _ _ _
        index (first + 1) (by omega) namesNext remainingBound
      · intro next _ arguments argumentsBound
        refine ⟨le_rfl, ?_⟩
        change UsesBefore next (returned (value (call _ [sequenceAtom arguments])))
        simpa [returned, value] using usesBefore_sequence next arguments argumentsBound
      · intro next _ arguments _
        change (substituteName (freshName index) replacement
          (returned (value (call _ [sequenceAtom arguments]))), next) = _
        simp only [returned, value, substituteName_call, List.map_cons, List.map_nil,
          substituteName_sequence]
        rfl
    case h_10 =>
      rename_i head terms _ _ _ _
      have scope : ∀ next, first + 1 ≤ next → ∀ arguments,
          (∀ atom ∈ arguments, UsesBefore next atom) →
          next ≤ (returnInvocation (invoke program (.var (freshName first)) head arguments) next).2 ∧
            UsesBefore (returnInvocation (invoke program (.var (freshName first)) head arguments) next).2
              (returnInvocation (invoke program (.var (freshName first)) head arguments) next).1 := by
        intro next later arguments argumentsBound
        apply returnInvocation_scope
        exact invoke_scope program _ _ arguments next (remainingBound.mono later) argumentsBound
      have transported := expressions_substitution program names (.var (freshName first))
        replacement terms
        (fun arguments => returnInvocation (invoke program (.var (freshName first)) head arguments))
        (fun arguments => returnInvocation (invoke program (.var (freshName first)) head arguments))
        index (first + 1) (by omega) namesNext remainingBound scope (by
          intro next later arguments _
          simpa only [remainingSame] using
            substituteName_returnInvoke replacement (.var (freshName first)) program head arguments
              index next (by omega))
      simpa only [remainingSame] using transported
    case h_6 =>
      rename_i name bound body
      let assigned := expression program names (.var (freshName first)) bound (first + 2)
      have assignedBound := expression_scope program names (.var (freshName first)) bound
        (first + 2) (fun entry member => (namesBound entry member).mono (by omega))
        ((usesBefore_freshName (first + 2) first).mpr (by omega))
      change first + 2 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at assignedBound
      let target := Atom.var (freshName (first + 1))
      let bodyCode := expression program ((name, target) :: names)
        (.var (freshName first)) body assigned.2
      have bodyNames : ∀ entry ∈ (name, target) :: names, UsesBefore assigned.2 entry.2 := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact (usesBefore_freshName assigned.2 (first + 1)).mpr (by omega)
        · exact (namesBound entry member).mono (by omega)
      have bodyFuel := (usesBefore_freshName assigned.2 first).mpr (by omega)
      have bodyBound := expression_scope program ((name, target) :: names)
        (.var (freshName first)) body assigned.2 bodyNames bodyFuel
      change assigned.2 < bodyCode.2 ∧ UsesBefore bodyCode.2 bodyCode.1 at bodyBound
      have assignedSame := expression_substitution program names (.var (freshName first))
        replacement bound index (first + 2) (by omega)
        (fun entry member => (namesBound entry member).mono (by omega))
        ((usesBefore_freshName (first + 2) first).mpr (by omega))
      have bodySame := expression_substitution program ((name, target) :: names)
        (.var (freshName first)) replacement body index assigned.2 (by omega) bodyNames bodyFuel
      have targetSame : substituteName (freshName index) replacement target = target :=
        earlier_name_untouched replacement index (first + 1) (by omega)
      simp only [remainingSame] at assignedSame bodySame
      simp only [List.map_cons, targetSame] at bodySame
      change (substituteName (freshName index) replacement
          (bindResult assigned.1 target bodyCode.1 bodyCode.2).1,
        (bindResult assigned.1 target bodyCode.1 bodyCode.2).2) =
        (let assigned' := expression program
          (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
          (.var (freshName first)) bound (first + 2)
         let body' := expression program
          ((name, target) :: names.map
            (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
          (.var (freshName first)) body assigned'.2
         bindResult assigned'.1 target body'.1 body'.2)
      rw [← assignedSame]
      dsimp only
      rw [← bodySame]
      simpa only [targetSame] using
        substituteName_bindResult replacement assigned.1 target bodyCode.1 index bodyCode.2 (by omega)
termination_by sizeOf source

/-- The same law through left-to-right argument evaluation, with a supplied
continuation that respects substitution and the emitter's allocation bound. -/
theorem expressions_substitution (program : Program) (names : Names) (fuel replacement : Atom)
    (sources : List Term) (continuation transformedContinuation : List Atom → Emit Atom)
    (index first : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel)
    (continuationBound : ∀ next, first ≤ next → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore next atom) →
      next ≤ (continuation arguments next).2 ∧
        UsesBefore (continuation arguments next).2 (continuation arguments next).1)
    (continuationSame : ∀ next, first ≤ next → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore next atom) →
      (substituteName (freshName index) replacement (continuation arguments next).1,
        (continuation arguments next).2) =
        transformedContinuation (arguments.map (substituteName (freshName index) replacement)) next) :
    (substituteName (freshName index) replacement
        (expressions program names fuel sources continuation first).1,
      (expressions program names fuel sources continuation first).2) =
      expressions program
        (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
        (substituteName (freshName index) replacement fuel) sources transformedContinuation first := by
  cases sources with
  | nil => simpa only [expressions, List.map_nil] using continuationSame first le_rfl [] (by simp)
  | cons head rest =>
      let headCode := expression program names fuel head (first + 1)
      have headBound := expression_scope program names fuel head (first + 1)
        (fun entry member => (namesBound entry member).mono (Nat.le_succ first))
        (fuelBound.mono (Nat.le_succ first))
      change first + 1 < headCode.2 ∧ UsesBefore headCode.2 headCode.1 at headBound
      let tailCode := expressions program names fuel rest
        (fun values => continuation (.var (freshName first) :: values)) headCode.2
      have tailScope : ∀ next, headCode.2 ≤ next → ∀ arguments,
          (∀ atom ∈ arguments, UsesBefore next atom) →
          next ≤ (continuation (.var (freshName first) :: arguments) next).2 ∧
            UsesBefore (continuation (.var (freshName first) :: arguments) next).2
              (continuation (.var (freshName first) :: arguments) next).1 := by
        intro next later arguments argumentsBound
        apply continuationBound next (by omega)
        simpa using And.intro ((usesBefore_freshName next first).mpr (by omega)) argumentsBound
      have tailBound := expressions_scope program names fuel rest
        (fun values => continuation (.var (freshName first) :: values)) headCode.2
        (fun entry member => (namesBound entry member).mono (by omega))
        (fuelBound.mono (by omega)) tailScope
      change headCode.2 ≤ tailCode.2 ∧ UsesBefore tailCode.2 tailCode.1 at tailBound
      have headSame := expression_substitution program names fuel replacement head index (first + 1)
        (by omega) (fun entry member => (namesBound entry member).mono (Nat.le_succ first))
        (fuelBound.mono (Nat.le_succ first))
      have tailSame := expressions_substitution program names fuel replacement rest
        (fun values => continuation (.var (freshName first) :: values))
        (fun values => transformedContinuation (.var (freshName first) :: values))
        index headCode.2 (by omega)
        (fun entry member => (namesBound entry member).mono (by omega))
        (fuelBound.mono (by omega)) tailScope (by
          intro next later arguments argumentsBound
          simpa only [List.map_cons, earlier_name_untouched replacement index first before] using
            continuationSame next (by omega) (.var (freshName first) :: arguments)
              (by simpa using (And.intro
                ((usesBefore_freshName next first).mpr (by omega)) argumentsBound)))
      rw [expressions, expressions]
      change (substituteName (freshName index) replacement
          (bindResult headCode.1 (.var (freshName first)) tailCode.1 tailCode.2).1,
        (bindResult headCode.1 (.var (freshName first)) tailCode.1 tailCode.2).2) =
        (let head' := expression program
          (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
          (substituteName (freshName index) replacement fuel) head (first + 1)
         let tail' := expressions program
          (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
          (substituteName (freshName index) replacement fuel) rest
          (fun values => transformedContinuation (.var (freshName first) :: values)) head'.2
         bindResult head'.1 (.var (freshName first)) tail'.1 tail'.2)
      rw [← headSame]
      dsimp only
      rw [← tailSame]
      simpa only [earlier_name_untouched replacement index first before] using
        substituteName_bindResult replacement headCode.1 (.var (freshName first)) tailCode.1
          index tailCode.2 (by omega)
termination_by sizeOf sources

end

/-- The structural substitution used in the compiler law is exactly the
independent interpreter's substitution after atom translation. -/
theorem substituteName_runtime (atom : Atom) (name : String) (replacement : Atom) :
    toLeaTTaAtom (substituteName name replacement atom) =
      Metta.Subst.apply [(name, toLeaTTaAtom replacement)] (toLeaTTaAtom atom) := by
  cases atom with
  | symbol | grounded => simp only [substituteName, toLeaTTaAtom, Metta.Subst.apply]
  | var other =>
    by_cases same : other = name <;>
      simp [substituteName, toLeaTTaAtom, Metta.Subst.apply, Metta.Subst.lookup, same]
  | expression items =>
    simp only [substituteName, toLeaTTaAtom, Metta.Subst.apply,
      solutionTheory_toLeaTTaAtoms_eq_map, List.map_map, Metta.Atom.expr.injEq]
    apply List.map_congr_left
    intro item member
    exact substituteName_runtime item name replacement
termination_by sizeOf atom

/-- A real interpreter substitution of an older generated operand produces
the code compiled with that operand already materialized. This includes
recursive source expressions and shadowing `let` bindings. -/
theorem expression_runtime_substitution (program : Program) (names : Names)
    (fuel replacement : Atom) (source : Term) (index first : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    Metta.Subst.apply [(freshName index, toLeaTTaAtom replacement)]
        (toLeaTTaAtom (expression program names fuel source first).1) =
      toLeaTTaAtom (expression program
        (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
        (substituteName (freshName index) replacement fuel) source first).1 := by
  rw [← substituteName_runtime]
  exact congrArg (fun emitted => toLeaTTaAtom emitted.1)
    (expression_substitution program names fuel replacement source index first before namesBound fuelBound)

open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

private theorem rename_single_substitution (atom replacement : Metta.Atom) (name : String)
    (rename : String → String) (injective : Function.Injective rename) :
    renBy rename (Metta.Subst.apply [(name, replacement)] atom) =
      Metta.Subst.apply [(rename name, renBy rename replacement)] (renBy rename atom) := by
  induction atom with
  | sym | gnd => simp only [renBy, Metta.Subst.apply]
  | var other =>
    by_cases same : other = name
    · simp [same, Metta.Subst.apply, Metta.Subst.lookup]
    · have different : rename other ≠ rename name := fun equal => same (injective equal)
      simp [Metta.Subst.apply, Metta.Subst.lookup, same, different]
  | expr items ih =>
    simp only [renBy, Metta.Subst.apply, List.map_map, Metta.Atom.expr.injEq]
    exact List.map_congr_left (fun item member => ih item member)

/-- Runtime freshening and operand materialization commute with the whole
expression compiler. Closed payloads are not renamed; generated binders are.
This is the substitution performed when a computed argument enters its
freshened continuation. -/
theorem renamed_expression_runtime_substitution (program : Program) (names : Names)
    (fuel replacement : Atom) (source : Term) (index first : Nat)
    (rename : String → String) (injective : Function.Injective rename)
    (closed : (toLeaTTaAtom replacement).vars = []) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    Metta.Subst.apply [(rename (freshName index), toLeaTTaAtom replacement)]
        (renBy rename (toLeaTTaAtom (expression program names fuel source first).1)) =
      renBy rename (toLeaTTaAtom (expression program
        (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
        (substituteName (freshName index) replacement fuel) source first).1) := by
  have transport := rename_single_substitution
    (toLeaTTaAtom (expression program names fuel source first).1)
    (toLeaTTaAtom replacement) (freshName index) rename injective
  rw [renBy_eq_self_of_vars_nil rename _ closed] at transport
  rw [← transport, expression_runtime_substitution program names fuel replacement source index
    first before namesBound fuelBound]

theorem substitute_scope (atom replacement : Atom) (name : String) (bound : Nat)
    (bounded : UsesBefore bound atom) (replacementBound : UsesBefore bound replacement) :
    UsesBefore bound (substituteName name replacement atom) := by
  cases atom with
  | symbol | grounded => simpa only [substituteName] using bounded
  | var other =>
    by_cases same : other = name
    · simpa [substituteName, same] using replacementBound
    · simpa [substituteName, same] using bounded
  | expression items =>
    intro candidate occurrence
    simp only [substituteName] at occurrence
    cases occurrence with
    | expression member childOccurs =>
      obtain ⟨child, childHere, rfl⟩ := List.mem_map.mp member
      exact substitute_scope child replacement name bound
        (fun candidate occurs => bounded candidate (.expression childHere occurs))
        replacementBound candidate childOccurs
termination_by sizeOf atom

/-- Fill the finite set of allocated input variables. This is a structural
substitution used in the compiler proof; it does not execute guest code. -/
def fillInputs : List (Nat × Atom) → Atom → Atom
  | [], atom => atom
  | (index, replacement) :: rest, atom =>
      fillInputs rest (substituteName (freshName index) replacement atom)

private theorem fillInputs_scope (inputs : List (Nat × Atom)) (atom : Atom) (bound : Nat)
    (bounded : UsesBefore bound atom)
    (inputBound : ∀ entry ∈ inputs, UsesBefore bound entry.2) :
    UsesBefore bound (fillInputs inputs atom) := by
  induction inputs generalizing atom with
  | nil => exact bounded
  | cons entry rest ih =>
    exact ih _ (substitute_scope atom entry.2 (freshName entry.1) bound bounded
      (inputBound entry (by simp))) (fun entry member => inputBound entry (by simp [member]))

/-- Materializing all supplied inputs commutes with compilation, including
the compiler's allocation state. Local binders lie above the input interval. -/
theorem expression_fillInputs (program : Program) (names : Names) (fuel : Atom)
    (source : Term) (inputs : List (Nat × Atom)) (first : Nat)
    (inputBefore : ∀ entry ∈ inputs, entry.1 < first)
    (inputBound : ∀ entry ∈ inputs, UsesBefore first entry.2)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    (fillInputs inputs (expression program names fuel source first).1,
      (expression program names fuel source first).2) =
      expression program (names.map (fun entry => (entry.1, fillInputs inputs entry.2)))
        (fillInputs inputs fuel) source first := by
  induction inputs generalizing names fuel with
  | nil => simp [fillInputs]
  | cons entry rest ih =>
    have one := expression_substitution program names fuel entry.2 source entry.1 first
      (inputBefore entry (by simp)) namesBound fuelBound
    let updated := names.map (fun row =>
      (row.1, substituteName (freshName entry.1) entry.2 row.2))
    have updatedBound : ∀ row ∈ updated, UsesBefore first row.2 := by
      intro row member
      obtain ⟨old, oldHere, rfl⟩ := List.mem_map.mp member
      exact substitute_scope old.2 entry.2 (freshName entry.1) first
        (namesBound old oldHere) (inputBound entry (by simp))
    have next := ih updated (substituteName (freshName entry.1) entry.2 fuel)
      (fun row member => inputBefore row (by simp [member]))
      (fun row member => inputBound row (by simp [member])) updatedBound
      (substitute_scope fuel entry.2 (freshName entry.1) first fuelBound
        (inputBound entry (by simp)))
    have transported := congrArg (fun emitted : Atom × Nat =>
      (fillInputs rest emitted.1, emitted.2)) one
    exact transported.trans (by simpa only [updated, List.map_map, Function.comp_def,
      fillInputs] using next)

private theorem subst_cons_closed (name : String) (replacement : Metta.Atom)
    (rest : Metta.Subst) (atom : Metta.Atom) (closed : replacement.vars = []) :
    Metta.Subst.apply ((name, replacement) :: rest) atom =
      Metta.Subst.apply rest (Metta.Subst.apply [(name, replacement)] atom) := by
  induction atom with
  | sym | gnd => simp only [Metta.Subst.apply]
  | var other =>
    by_cases same : other = name
    · simp [same, Metta.Subst.apply, Metta.Subst.lookup,
        Metta.Subst.apply_of_closed rest replacement closed]
    · simp [Metta.Subst.apply, Metta.Subst.lookup, same]
  | expr items ih =>
    simp only [Metta.Subst.apply, List.map_map, Metta.Atom.expr.injEq]
    exact List.map_congr_left (fun item member => ih item member)

/-- Simultaneous runtime substitution agrees with filling closed inputs,
even when input keys repeat. The first occurrence supplies the value. -/
theorem fillInputs_runtime (inputs : List (Nat × Atom)) (atom : Atom)
    (rename : String → String) (injective : Function.Injective rename)
    (closed : ∀ entry ∈ inputs, (toLeaTTaAtom entry.2).vars = []) :
    Metta.Subst.apply (inputs.map (fun entry =>
        (rename (freshName entry.1), toLeaTTaAtom entry.2)))
        (renBy rename (toLeaTTaAtom atom)) =
      renBy rename (toLeaTTaAtom (fillInputs inputs atom)) := by
  induction inputs generalizing atom with
  | nil => simpa only [List.map_nil, fillInputs] using
      Metta.Subst.apply_nil (renBy rename (toLeaTTaAtom atom))
  | cons entry rest ih =>
    rw [List.map_cons, subst_cons_closed _ _ _ _ (closed entry (by simp))]
    have transport := rename_single_substitution (toLeaTTaAtom atom)
      (toLeaTTaAtom entry.2) (freshName entry.1) rename injective
    rw [renBy_eq_self_of_vars_nil rename _ (closed entry (by simp))] at transport
    rw [← transport, ← substituteName_runtime]
    exact ih _ (fun row member => closed row (by simp [member]))

/-- The entire emitted expression can be materialized in one runtime
substitution. The supplied data remain closed while all local control
variables retain the enclosing rule's freshening. -/
theorem expression_runtime_inputs (program : Program) (names : Names) (fuel : Atom)
    (source : Term) (inputs : List (Nat × Atom)) (first : Nat)
    (rename : String → String) (injective : Function.Injective rename)
    (inputBefore : ∀ entry ∈ inputs, entry.1 < first)
    (inputBound : ∀ entry ∈ inputs, UsesBefore first entry.2)
    (closed : ∀ entry ∈ inputs, (toLeaTTaAtom entry.2).vars = [])
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel) :
    Metta.Subst.apply (inputs.map (fun entry =>
        (rename (freshName entry.1), toLeaTTaAtom entry.2)))
        (renBy rename (toLeaTTaAtom (expression program names fuel source first).1)) =
      renBy rename (toLeaTTaAtom (expression program
        (names.map (fun entry => (entry.1, fillInputs inputs entry.2)))
        (fillInputs inputs fuel) source first).1) := by
  rw [fillInputs_runtime inputs _ rename injective closed]
  exact congrArg (fun emitted : Atom × Nat => renBy rename (toLeaTTaAtom emitted.1))
    (expression_fillInputs program names fuel source inputs first inputBefore inputBound
      namesBound fuelBound)

theorem instantiate_eq_subst_on_variables (bindings : Metta.Bindings)
    (substitution : Metta.Subst) (atom : Metta.Atom)
    (observations : ∀ name ∈ atom.vars,
      Metta.instantiate bindings (.var name) = substitution.apply (.var name)) :
    Metta.instantiate bindings atom = substitution.apply atom := by
  induction atom with
  | sym | gnd => simp only [Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Subst.apply]
  | var name => exact observations name (by simp [Metta.Atom.vars])
  | expr items ih =>
    simp only [Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Subst.apply,
      Metta.Atom.expr.injEq]
    apply List.map_congr_left
    intro child member
    apply ih child member
    intro name occurrence
    apply observations name
    simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
    exact ⟨child.vars, ⟨child, member, rfl⟩, occurrence⟩

/-- Actual equality-class materialization agrees with compiling the supplied
inputs. The hypotheses concern only the finite allocated variable interval;
they do not assume an execution or a result for the compiled computation. -/
theorem expression_binding_materialization (program : Program) (names : Names) (fuel : Atom)
    (source : Term) (inputs : List (Nat × Atom)) (first : Nat)
    (rename : String → String) (injective : Function.Injective rename)
    (bindings : Metta.Bindings)
    (inputBefore : ∀ entry ∈ inputs, entry.1 < first)
    (inputBound : ∀ entry ∈ inputs, UsesBefore first entry.2)
    (closed : ∀ entry ∈ inputs, (toLeaTTaAtom entry.2).vars = [])
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel)
    (observations : ∀ index, index < (expression program names fuel source first).2 →
      Metta.instantiate bindings (.var (rename (freshName index))) =
        Metta.Subst.apply (inputs.map (fun entry =>
          (rename (freshName entry.1), toLeaTTaAtom entry.2)))
          (.var (rename (freshName index)))) :
    Metta.instantiate bindings
        (renBy rename (toLeaTTaAtom (expression program names fuel source first).1)) =
      renBy rename (toLeaTTaAtom (expression program
        (names.map (fun entry => (entry.1, fillInputs inputs entry.2)))
        (fillInputs inputs fuel) source first).1) := by
  rw [instantiate_eq_subst_on_variables bindings
    (inputs.map (fun entry => (rename (freshName entry.1), toLeaTTaAtom entry.2))) _ ?_]
  · exact expression_runtime_inputs program names fuel source inputs first rename injective
      inputBefore inputBound closed namesBound fuelBound
  · intro name occurrence
    rw [renBy_vars] at occurrence
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp occurrence
    obtain ⟨index, before, rfl⟩ :=
      (expression_scope program names fuel source first namesBound fuelBound).2 original
        (atomOccurs_of_mem_translated_vars member)
    exact observations index before

theorem symbol_substitution_fixed_excludes (atom : Atom) (name : String)
    (fixed : substituteName name (.symbol "") atom = atom) :
    ¬ AtomOccurs atom name := by
  cases atom with
  | symbol | grounded => intro occurrence; cases occurrence
  | var other =>
    intro occurrence
    cases occurrence
    simp [substituteName] at fixed
  | expression items =>
    intro occurrence
    cases occurrence with
    | expression member occurs =>
      have same : items.map (substituteName name (.symbol "")) = items.map id := by
        simpa only [substituteName, Atom.expression.injEq, List.map_id] using fixed
      have pointwise := List.map_inj_left.mp same
      exact symbol_substitution_fixed_excludes _ name (pointwise _ member) occurs
termination_by sizeOf atom

private theorem substituteName_absent (atom replacement : Atom) (name : String)
    (absent : ¬ AtomOccurs atom name) : substituteName name replacement atom = atom := by
  cases atom with
  | symbol | grounded => simp only [substituteName]
  | var other =>
    have different : other ≠ name := by rintro rfl; exact absent (.var _)
    simp only [substituteName, different, if_false]
  | expression items =>
    simp only [substituteName, Atom.expression.injEq]
    calc
      _ = items.map id := List.map_congr_left (fun child member =>
        substituteName_absent child replacement name (fun occurs =>
          absent (.expression member occurs)))
      _ = items := List.map_id _
termination_by sizeOf atom

/-- An unused older input cannot be introduced by compiling an expression.
Other source inputs may still be symbolic, as in a pending let continuation. -/
theorem expression_excludes_unused_input (program : Program) (names : Names)
    (fuel : Atom) (source : Term) (index first : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first fuel)
    (namesUnused : ∀ entry ∈ names, ¬ AtomOccurs entry.2 (freshName index))
    (fuelUnused : ¬ AtomOccurs fuel (freshName index)) :
    ¬ AtomOccurs (expression program names fuel source first).1 (freshName index) := by
  have substituted := congrArg Prod.fst (expression_substitution program names fuel (.symbol "")
    source index first before namesBound fuelBound)
  have namesSame : names.map (fun entry =>
      (entry.1, substituteName (freshName index) (.symbol "") entry.2)) = names := by
    calc
      _ = names.map id := List.map_congr_left (by
        intro entry member
        simp only [id_eq, substituteName_absent _ _ _ (namesUnused entry member)])
      _ = names := List.map_id _
  simp only [namesSame, substituteName_absent _ _ _ fuelUnused] at substituted
  exact symbol_substitution_fixed_excludes _ _ substituted

/-- Once source inputs are data, a body has no variable allocated before its
own interval. This follows from the whole-compiler substitution law. -/
theorem expression_excludes_earlier_data (program : Program) (names : Names)
    (fuel : Atom) (source : Term) (index first : Nat) (before : index < first)
    (namesData : ∀ entry ∈ names, DataAtom entry.2) (fuelData : DataAtom fuel) :
    ¬ AtomOccurs (expression program names fuel source first).1 (freshName index) := by
  have bounded (atom : Atom) (data : DataAtom atom) : UsesBefore first atom := by
    intro name occurs
    exact False.elim (data_has_no_variables data name occurs)
  exact expression_excludes_unused_input program names fuel source index first before
    (fun entry member => bounded _ (namesData entry member)) (bounded fuel fuelData)
    (fun entry member => data_has_no_variables (namesData entry member) _)
    (data_has_no_variables fuelData _)

/-- Materialized expression variables belong to its own finite allocation
interval; an earlier argument binder and later sibling binders are excluded. -/
theorem expression_data_name_bounds (program : Program) (names : Names)
    (fuel : Atom) (source : Term) (first : Nat)
    (namesData : ∀ entry ∈ names, DataAtom entry.2) (fuelData : DataAtom fuel) :
    ∀ name, AtomOccurs (expression program names fuel source first).1 name →
      ∃ index, first ≤ index ∧ index < (expression program names fuel source first).2 ∧
        name = freshName index := by
  have bounded (atom : Atom) (data : DataAtom atom) : UsesBefore first atom := by
    intro name occurs
    exact False.elim (data_has_no_variables data name occurs)
  have scope := (expression_scope program names fuel source first
    (fun entry member => bounded _ (namesData entry member)) (bounded fuel fuelData)).2
  intro name occurs
  obtain ⟨index, upper, same⟩ := scope name occurs
  refine ⟨index, ?_, upper, same⟩
  by_contra lower
  have before : index < first := by omega
  exact expression_excludes_earlier_data program names fuel source index first before
    namesData fuelData (same ▸ occurs)

/-- Runtime freshening preserves the allocation interval in the emitted
syntax. The guest's variable spellings remain inside encoded data. -/
theorem renamed_expression_data_name_bounds (program : Program) (names : Names)
    (fuel : Atom) (source : Term) (first : Nat) (rename : String → String)
    (namesData : ∀ entry ∈ names, DataAtom entry.2) (fuelData : DataAtom fuel) :
    ∀ name ∈ (renBy rename (toLeaTTaAtom (expression program names fuel source first).1)).vars,
      ∃ index, first ≤ index ∧ index < (expression program names fuel source first).2 ∧
        name = rename (freshName index) := by
  intro name member
  rw [renBy_vars] at member
  obtain ⟨original, occurs, same⟩ := List.mem_map.mp member
  obtain ⟨index, lower, upper, spelling⟩ := expression_data_name_bounds program names fuel source
    first namesData fuelData original (atomOccurs_of_mem_translated_vars occurs)
  exact ⟨index, lower, upper, by rw [← same, spelling]⟩

/-- A caller operand is filled in without changing any later local binder,
even when the source body contains its own calls and shadowing declarations. -/
theorem supplied_operand_compiles (program : Program) (source : Term) (fuel : Nat)
    (payload : Term) :
    (substituteName (freshName 0) (encode payload)
        (expression program [("x", .var (freshName 0))] (.grounded (.int fuel)) source 1).1,
      (expression program [("x", .var (freshName 0))] (.grounded (.int fuel)) source 1).2) =
      expression program [("x", encode payload)] (.grounded (.int fuel)) source 1 := by
  simpa [substituteName] using expression_substitution program [("x", .var (freshName 0))]
    (.grounded (.int fuel)) (encode payload) source 0 1 (by omega)
    (by intro entry member; rcases List.mem_singleton.mp member with rfl; simp)
    (usesBefore_grounded 1 _)

/-- Filling in a local control binder is not operand materialization. This
counterexample rejects the compiler law when its strict allocation boundary
is removed, even though the source has no free variables. -/
theorem local_control_capture_changes_code :
    substituteName (freshName 0) (.symbol "captured")
        (expression [] [] (.grounded (.int 1)) (.sym "kept") 0).1 ≠
      (expression [] [] (.grounded (.int 1)) (.sym "kept") 0).1 := by
  simp only [expression]
  let body := returned (value (encode (.sym "kept")))
  change substituteName (freshName 0) (.symbol "captured")
    (call "chain" [call "eval" [call "==" [.grounded (.int 1), .grounded (.int 0)]],
      .var (freshName 1),
      call "unify" [.var (freshName 1), .grounded (.bool true), returned (.symbol "nik:Exhausted"),
        call "chain" [call "eval" [call "-" [.grounded (.int 1), .grounded (.int 1)]],
          .var (freshName 0), body]]]) ≠ _
  change _ ≠ call "chain" [call "eval" [call "==" [.grounded (.int 1), .grounded (.int 0)]],
    .var (freshName 1),
    call "unify" [.var (freshName 1), .grounded (.bool true), returned (.symbol "nik:Exhausted"),
      call "chain" [call "eval" [call "-" [.grounded (.int 1), .grounded (.int 1)]],
        .var (freshName 0), body]]]
  simp [substituteName, call, freshName]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
