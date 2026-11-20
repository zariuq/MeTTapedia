import Mettapedia.Languages.MeTTa.ContextualTransform.HEReturnAndSpaces
import Mettapedia.Languages.MeTTa.ContextualTransform.HEArgumentContexts
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Languages.MeTTa.HE.EquationFrontierExtension
import Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
import Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame
import Mettapedia.Languages.MeTTa.HE.DeliveredArgumentPackets

/-!
# Stateful source controls with named stores

This explicit model host implements list-valued stores, first-occurrence take,
append, inspection and a failing destination. It supplies primitive outcomes
to the independent HE source judgments; it receives no evaluator continuation.
The controls distinguish source sequencing from rollback and space labels from
their host representations. They are not conformance proofs for CeTTa natives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful
open HEStatefulContexts HEReturnAndSpaces

abbrev World := Bool → List Atom

def failure (destination : Atom) : Atom :=
  .expression [.symbol "Error", destination, .symbol "BadDestination"]

/-- An independent primitive service, with ordered physical occurrences. -/
def execute (label : Bool) (world : World) (command argument : Atom) : List Atom × World :=
  if command = .symbol "put" then
    ([.expression []], Function.update world label (world label ++ [argument]))
  else if command = .symbol "take" then
    if argument ∈ world label then
      ([argument], Function.update world label ((world label).erase argument))
    else ([], world)
  else if command = .symbol "silent-put" then
    ([], Function.update world label (world label ++ [argument]))
  else if command = .symbol "read" then (world label, world)
  else ([failure argument], world)

def services : WorldServices Bool World where
  contextPayload label := .int (if label then 1 else 0)
  nativeCall label before name command argument frame results after :=
    name = .symbol "model-store" ∧
      results = (execute label before command argument).1.map
        (fun value => (Entry.Value.ofAtom value, frame)) ∧
      after = (execute label before command argument).2

def environment : WorldEnvironment Bool World where
  view world label := ⟨world label⟩
  services := services
  dispatch := { executable := fun _ => False, outcome := fun _ _ _ => False }
  lookup := rawLookup

def command (name : String) (argument : Atom) : Entry.Value :=
  native (.symbol "model-store") (.symbol name) (Entry.Value.ofAtom argument)

theorem command_exact (label : Bool) (before : World) (name : String) (argument : Atom)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller (command name argument)
        frame results after (policy := policy) ↔
      results = (execute label before (.symbol name) argument).1.map
        (fun value => (Entry.Value.ofAtom value, frame)) ∧
      after = (execute label before (.symbol name) argument).2 := by
  rw [command, native_exact]
  simp [environment, services, Entry.Value.erase]

/-- Changing one named store leaves the other store intact. -/
theorem execute_other_space (label other : Bool) (different : other ≠ label)
    (world : World) (name argument : Atom) :
    (execute label world name argument).2 other = world other := by
  unfold execute
  split_ifs <;> simp [Function.update_of_ne different]

theorem handles_distinct : Function.Injective services.contextPayload := by
  intro first second same
  cases first <;> cases second <;> simp_all [services]

private theorem substitute_command (policy : Policy) (binder : String) (value : Entry.Value)
    (name argument : String) :
    substituteBinder policy binder value (command name (.symbol argument)) =
      command name (.symbol argument) := by
  cases rebuild : policy.rebuilding <;>
    simp [command, native, substituteBinder, Entry.Value.ofAtom,
      Entry.Value.substitute, Entry.Value.rebuildStatus, rebuild]

def takeThenFail (item destination : String) : Entry.Value :=
  chain (command "take" (.symbol item)) "claimed" (command "bad" (.symbol destination))

/-- A later destination error does not undo a successful earlier take. Both
directions exclude a success count, a missing error, or a restored source row. -/
theorem take_then_fail_exact (label : Bool) (before : World) (item destination : String)
    (present : Atom.symbol item ∈ before label)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller (takeThenFail item destination)
        frame results after (policy := policy) ↔
      results = [(Entry.Value.ofAtom (failure (.symbol destination)), frame)] ∧
      after = Function.update before label ((before label).erase (.symbol item)) := by
  rw [takeThenFail, chain_exact]
  constructor
  · rintro ⟨middle, selected, taken, continued⟩
    have takenExact := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp taken
    simp [execute, present] at takenExact
    rcases takenExact with ⟨rfl, rfl⟩
    have one := BoundaryBatchRel.single_iff.mp continued
    cases one with
    | chain resumed =>
        rw [substitute_command] at resumed
        have result := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp resumed
        simpa [execute] using result
  · rintro ⟨rfl, rfl⟩
    refine ⟨Function.update before label ((before label).erase (.symbol item)),
      [(Entry.Value.ofAtom (.symbol item), frame)], ?_, ?_⟩
    · apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
      simp [execute, present]
    · apply BoundaryBatchRel.single_iff.mpr
      apply Stateful.BoundaryRel.chain
      rw [substitute_command]
      apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
      simp [execute]

/-- An effectful operand that emits no answers suppresses the continuation,
but its store update survives. This holds for every continuation template. -/
theorem answerless_effect_exact (label : Bool) (before : World) (item : Atom)
    (binder : String) (template : Entry.Value)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller
        (chain (command "silent-put" item) binder template)
        frame results after (policy := policy) ↔
      results = [] ∧ after = Function.update before label (before label ++ [item]) := by
  rw [chain_exact]
  constructor
  · rintro ⟨middle, selected, produced, continued⟩
    have producedExact := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp produced
    simp [execute] at producedExact
    rcases producedExact with ⟨rfl, rfl⟩
    cases continued
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨_, [], ?_, .nil⟩
    apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
    simp [execute]

/-- Completed outcomes cannot claim that the source was rolled back. -/
theorem answerless_is_not_rollback (label : Bool) (before : World) (item : Atom)
    (template : Entry.Value) (policy : Policy) :
    ¬MinimalRel environment label before [] [] none
      (chain (command "silent-put" item) "unused" template)
      Frame.empty [] before (policy := policy) := by
  intro run
  have same := ((answerless_effect_exact _ _ _ _ _ _ _ _ _ _ _ _).mp run).2
  have atLabel := congrFun same label
  have lengths := congrArg List.length atLabel
  simp at lengths

def aliasedEnvironment : WorldEnvironment Bool World :=
  { environment with services := { services with contextPayload := fun _ => .int 0 } }

def twoStores : World := fun label => if label then [.symbol "right"] else [.symbol "left"]

private theorem aliased_read (child : Bool) (policy : Policy) :
    MinimalRel aliasedEnvironment false twoStores [] [] none
      (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
      ((twoStores child).map (fun value => (Entry.Value.ofAtom value, Frame.empty)))
      twoStores (policy := policy) := by
  apply in_space_exact.mpr
  refine ⟨child, rfl, ?_⟩
  apply Stateful.InvocationRel.embedded
  · simp [Minimal.HostCall, command, native, Entry.Value.erase, aliasedEnvironment, environment]
  · simp [command, native, Entry.Value.erase, Minimal.embeddedInstruction]
  · rw [Frame.read_empty]
    apply native_exact.mpr
    simp [aliasedEnvironment, services, execute, Entry.Value.erase]

/-- Equal host handles do not distinguish worlds: identical source syntax
admits both stores' answers. Injectivity is a real premise of named-space
identification, not something syntax alone provides. -/
theorem aliased_handles_have_distinct_answers (policy : Policy) :
    MinimalRel aliasedEnvironment false twoStores [] [] none
        (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
        [(.symbol "left", Frame.empty)] twoStores (policy := policy) ∧
    MinimalRel aliasedEnvironment false twoStores [] [] none
        (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
        [(.symbol "right", Frame.empty)] twoStores (policy := policy) ∧
      (Entry.Value.symbol "left" ≠ Entry.Value.symbol "right") := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [twoStores, Entry.Value.ofAtom] using aliased_read false policy
  · simpa [twoStores, Entry.Value.ofAtom] using aliased_read true policy
  · intro same
    have erased := congrArg Entry.Value.erase same
    simp [Entry.Value.erase] at erased

namespace Quotation

open Spec.Eval.Steps
open Spec.Match.Merge Spec.Bindings.ScopeObservation Spec.Type.RuntimeRefinement
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory HEReturnAndSpaces
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)

def quote (value : Atom) : Atom := .expression [.symbol "quote", value]
def unquote (value : Atom) : Atom := .expression [.symbol "unquote", quote value]

private def form (release : Bool) : Atom → Atom := if release then unquote else quote
private def rhs (release : Bool) (key : String := "atom") : Atom :=
  if release then .var key else Atom.notReducible
private def row (release : Bool) : Atom := .expression [.symbol "=", form release (.var "atom"), rhs release]

private def signature (release : Bool) : Atom :=
  let demand := if release then Atom.undefinedType else Atom.atomType
  .expression [.symbol ":", .symbol (if release then "unquote" else "quote"),
    .expression [.symbol "->", demand, demand]]

/-- The two authored equations and their declarations in the HE library. A test input to the
existing world host, not an evaluator for quotation. -/
def libraryWorld : World := fun _ => [signature false, row false, signature true, row true]

private def assignment (value : Atom) (key : String := "atom") : Bindings := Bindings.empty.assign key value

private def opened (release : Bool) (value : Atom) (key : String := "atom")
    (before : Bindings := Bindings.empty) : EquationWork :=
  ⟨if release then 3 else 1, form release (.var "atom"), rhs release,
    form release (.var key), rhs release key, before.assign key value⟩

private theorem visible_none {release : Bool} {live : List Atom} {value : Atom}
    (closed : ∀ name, ¬ AtomOccurs value name)
    (saved : ∀ atom ∈ live, ∀ name, ¬ AtomOccurs atom name)
    (name : String) :
    ¬ QueryVisibleName live (form release value) Bindings.empty name := by
  have absent : name ∉ TypeSubst.typeVars value :=
    fun member => closed name ((atomOccurs_iff_mem_typeVars value name).mpr member)
  have formClosed : ¬ AtomOccurs (form release value) name := by
    rw [atomOccurs_iff_mem_typeVars]
    cases release <;> simpa [form, quote, unquote, TypeSubst.typeVars, TypeSubst.typeVarsList] using absent
  simp only [QueryVisibleName, formClosed, Bindings.empty, List.not_mem_nil, false_and,
    exists_const, or_false, false_or]
  rintro ⟨atom, member, occurs⟩
  exact saved atom member name occurs

private theorem fresh_rule (ruleRelease : Bool) (live : List Atom) (query : Atom)
    (before : Bindings) (key : String)
    (fresh : ¬ QueryVisibleName live query before key) :
    AlphaVariantRel live query before
      (form ruleRelease (.var "atom")) (rhs ruleRelease)
      (form ruleRelease (.var key)) (rhs ruleRelease key) := by
  let rename := Equiv.swap "atom" key
  refine ⟨rename, rename.injective, ?_, ?_, ?_⟩
  · have alpha := EquationFreshening.rename_alpha rename (form ruleRelease (.var "atom"))
    cases ruleRelease <;> simpa [form, quote, unquote, renameTypeVars, rename] using alpha
  · have alpha := EquationFreshening.rename_alpha rename (rhs ruleRelease)
    cases ruleRelease <;> simpa [rhs, Atom.notReducible, renameTypeVars, rename] using alpha
  · intro name member
    have same : name = "atom" := by
      have membership := member.elim
        (fun it => List.mem_append_left (TypeSubst.typeVars (rhs ruleRelease)) (atomOccurs_mem_typeVars it))
        (fun it => List.mem_append_right (TypeSubst.typeVars (form ruleRelease (.var "atom")))
          (atomOccurs_mem_typeVars it))
      cases ruleRelease <;>
        simpa [form, quote, unquote, rhs, Atom.notReducible, TypeSubst.typeVars, TypeSubst.typeVarsList]
          using membership
    simpa [same, rename] using fresh

private theorem merge_assignment (value : Atom) (key : String) :
    MergeRel equalityGroundedSemantic Bindings.empty (assignment value key) (assignment value key) :=
  .mk (.refl _) (.value (.fresh rfl) .nil)

private theorem empty_merge :
    MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (.refl _) .nil

private theorem unary_match (head : String) {value pattern body : Atom} {key : String}
    (child : MatchRel equalityGroundedSemantic value pattern (assignment body key))
    (loopFree : SemanticLoopFree (assignment body key)) :
    MatchRel equalityGroundedSemantic (.expression [.symbol head, value])
      (.expression [.symbol head, pattern]) (assignment body key) :=
  .expression (.cons (.symSym head semanticLoopFree_empty) empty_merge
    (.cons child (merge_assignment body key) .nil)) loopFree

private theorem matches_rule (release : Bool) (value : Atom) (key : String)
    (nonvar : isVariableB value = false) (absent : ¬AtomOccurs value key) :
    MatchRel equalityGroundedSemantic (form release value)
      (form release (.var key)) (assignment value key) := by
  have loopFree : SemanticLoopFree (assignment value key) := semanticLoopFree_single_assignment absent
  have quoted := unary_match "quote" (.nonVarVar nonvar loopFree) loopFree
  cases release
  · exact quoted
  · exact unary_match "unquote" quoted loopFree

private theorem merge_logical (value : Atom) (frame : Frame) (key : String)
    (fresh : key ∉ specBindingVars frame.bindings) (absent : key ∉ TypeSubst.typeVars value) :
    LogicalMergeRel (assignment value key) frame.bindings (frame.bindings.assign key value) := by
  have unbound : frame.bindings.lookup key = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    have distinct : key ≠ entry.1 := fun same => fresh (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨entry, member, by simp [same]⟩))
    simpa using distinct
  have appended : frame.bindings.assign key value =
      ⟨frame.bindings.assignments ++ [(key, value)], frame.bindings.equalities⟩ := by
    simp [Bindings.assign, Bindings.isBound, unbound]
  refine ⟨BindingSourceAgreement.of_recordPerm ?_,
    (frame.certified.fresh_assignment key value fresh absent).satisfiable⟩
  rw [appended]
  exact ⟨List.perm_append_comm, .refl _⟩

private theorem hits (release : Bool) (live : List Atom) (value : Atom) (frame : Frame) (key : String)
    (nonvar : isVariableB value = false) (absent : ¬AtomOccurs value key)
    (fresh : ¬QueryVisibleName live (form release value) frame.bindings key)
    (freshFrame : key ∉ specBindingVars frame.bindings) :
    EquationRowResultsRel live (form release value) frame.bindings (if release then 3 else 1)
      (row release) [opened release value key frame.bindings] :=
  .hit _ _ _ _ _ _ _ (fresh_rule release live (form release value) frame.bindings key fresh)
    (matches_rule release value key nonvar absent)
    (merge_logical value frame key freshFrame (fun member => absent ((atomOccurs_iff_mem_typeVars _ _).mpr member)))

private theorem misses (release : Bool) (live : List Atom) (value : Atom) (position : Nat)
    (before : Bindings) (key : String)
    (fresh : ¬QueryVisibleName live (form release value) before key) :
    EquationRowResultsRel live (form release value) before position (row (!release)) [] := by
  apply EquationRowResultsRel.miss position _ _ _ _ (fresh_rule (!release) live (form release value) before key fresh)
  intro pattern body renamed matched output viable
  obtain ⟨rename, _, left, _, _⟩ := renamed
  have shaped := EquationFreshening.alphaRename_eq left
  have matching := viable.1
  rw [shaped] at matching
  cases release
  · have ruled : MatchRel equalityGroundedSemantic (quote value)
        (unquote (.var (rename "atom"))) matched := by
      simpa [form, quote, unquote, renameTypeVars] using matching
    cases ruled with
    | expression children _ =>
        cases children with
        | cons first _ _ => exact symbol_mismatch_not_match (by decide) _ first
  · have ruled : MatchRel equalityGroundedSemantic (unquote value)
        (quote (.var (rename "atom"))) matched := by
      simpa [form, quote, unquote, renameTypeVars] using matching
    cases ruled with
    | expression children _ =>
        cases children with
        | cons first _ _ => exact symbol_mismatch_not_match (by decide) _ first

private theorem declaration_irrelevant (release : Bool) (left right : Atom) :
    signature release ≠ .expression [.symbol "=", left, right] := by
  cases release <;> simp [signature]

/-- The prepared call selects exactly the physical authored row, including the matched
payload binding. The other quotation operation is not an alternative. -/
private theorem scoped_frontier (release : Bool) (label : Bool) (live : List Atom) (value : Atom)
    (frame : Frame) (key : String)
    (nonvar : isVariableB value = false) (absent : ¬AtomOccurs value key)
    (fresh : ¬QueryVisibleName live (form release value) frame.bindings key)
    (freshFrame : key ∉ specBindingVars frame.bindings) :
    EquationFrontierRel (environment.view libraryWorld label) live (form release value)
      frame.bindings [opened release value key frame.bindings] := by
  let work := opened release value key frame.bindings
  have hit := hits release live value frame key nonvar absent fresh freshFrame
  have miss := fun position => misses release live value position frame.bindings key fresh
  cases release
  · apply EquationFrontierRel.completed (blocks := [[], [work], [], []])
    exact .cons (.irrelevant 0 _ (declaration_irrelevant false))
      (.cons hit (.cons (.irrelevant 2 _ (declaration_irrelevant true)) (.cons (miss 3) .nil)))
  · apply EquationFrontierRel.completed (blocks := [[], [], [], [work]])
    exact .cons (.irrelevant 0 _ (declaration_irrelevant false))
      (.cons (miss 1) (.cons (.irrelevant 2 _ (declaration_irrelevant true)) (.cons hit .nil)))

private theorem frontier (release : Bool) (label : Bool) (live : List Atom) (value : Atom)
    (nonvar : isVariableB value = false) (closed : ∀ name, ¬AtomOccurs value name)
    (saved : ∀ atom ∈ live, ∀ name, ¬AtomOccurs atom name) :
    EquationFrontierRel (environment.view libraryWorld label) live (form release value)
      Bindings.empty [opened release value] :=
  scoped_frontier release label live value Frame.empty "atom" nonvar (closed "atom")
    (visible_none closed saved "atom") (by simp [Frame.empty, specBindingVars, Bindings.empty])

private def matchedFrame (value : Atom) (fresh : "atom" ∉ TypeSubst.typeVars value) : Frame :=
  ⟨assignment value, [("atom", Entry.Value.ofAtom value)], by
    simpa [assignment, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup,
      Entry.Value.eraseEnvironment, Entry.Value.erase_ofAtom]
      using ReadoutCertificate.of_fold (single_assignment_presentation "atom" value fresh)⟩

private theorem resolve_empty : Entry.Value.resolve [] = Entry.Value.var := by
  funext name
  rfl

private theorem open_concrete_call (release : Bool) (value : Atom)
    (nonvar : isVariableB value = false) (fresh : "atom" ∉ TypeSubst.typeVars value) :
    Entry.Value.UnifyRel Policy.unmarked.rebuilding Frame.empty.environment
      (Entry.Value.ofAtom (form release value)) (Entry.Value.ofAtom (opened release value).pattern)
      (matchedFrame value fresh).environment := by
  have bound : Entry.Value.UnifyRel Policy.unmarked.rebuilding Frame.empty.environment
      (Entry.Value.ofAtom value) (.var "atom") (matchedFrame value fresh).environment := by
    have nonvariable : ∀ name, (Frame.empty.read .unmarked (Entry.Value.ofAtom value)).erase ≠ .var name := by
      intro name eq
      rw [Frame.read_empty, Entry.Value.erase_ofAtom] at eq
      simp [eq, isVariableB] at nonvar
    simpa [matchedFrame, assignFresh, Frame.empty, Entry.Value.bind, resolve_empty,
      Entry.Value.substitute_identity] using
      assignFresh_unifies .unmarked Frame.empty "atom" (Entry.Value.ofAtom value)
        (by simp [Frame.empty, specBindingVars, Bindings.empty])
        (by simpa only [Entry.Value.erase_ofAtom] using fresh) nonvariable
  cases release
  · simpa [form, opened, quote, Entry.Value.ofAtom] using
      unary_unifies .unmarked Frame.empty "quote" bound
  · simpa [form, opened, quote, unquote, Entry.Value.ofAtom] using
      unary_unifies .unmarked Frame.empty "unquote" (unary_unifies .unmarked Frame.empty "quote" bound)

private theorem read_body (release : Bool) (value : Atom) (fresh : "atom" ∉ TypeSubst.typeVars value) :
    (matchedFrame value fresh).read .unmarked (Entry.Value.ofAtom (opened release value).body) =
      Entry.Value.ofAtom (if release then value else Atom.notReducible) := by
  cases release <;>
    simp [opened, rhs, matchedFrame, Frame.read, Atom.notReducible, Entry.Value.ofAtom,
      Entry.Value.substitute, Entry.Value.resolve]

private theorem non_dispatch (release : Bool) (value : Atom) :
    NonGroundedCallRel environment.dispatch (form release value) := by
  cases release <;>
    simp [environment, NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction, form, quote, unquote]

private theorem not_error (release : Bool) (value : Atom) :
    ¬IsErrorRel (form release value) := by
  cases release <;> simp [IsErrorRel, form, quote, unquote]

private theorem prepared_call (release : Bool) (label : Bool) (value expected : Atom)
    (nonvar : isVariableB value = false) (closed : ∀ name, ¬AtomOccurs value name)
    (expectedClosed : ∀ name, ¬AtomOccurs expected name)
    (fresh : "atom" ∉ TypeSubst.typeVars value)
    {results : List Result} {after : World}
    (ordinary : ¬FunctionPending .unmarked
      (Entry.Value.ofAtom (if release then value else Atom.notReducible)))
    (returned : BoundaryRel environment label libraryWorld [] [] none
      (.returned (Entry.Value.ofAtom (form release value)) expected)
      (Entry.Value.ofAtom (if release then value else Atom.notReducible))
      (matchedFrame value fresh) results after) :
    CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (form release value)) expected
      Frame.empty results after := by
  apply Stateful.CallRel.equations (works := [opened release value])
  · simpa only [Entry.Value.erase_ofAtom] using not_error release value
  · simpa only [Entry.Value.erase_ofAtom] using non_dispatch release value
  · rw [Entry.Value.erase_ofAtom]
    exact frontier release label [expected] value nonvar closed (by simpa using expectedClosed)
  · simp
  · have produced : BoundaryRel environment label libraryWorld [expected] []
        (some (form release value)) .producer
        ((matchedFrame value fresh).read .unmarked (Entry.Value.ofAtom (opened release value).body))
        (matchedFrame value fresh)
        [(Entry.Value.ofAtom (if release then value else Atom.notReducible), matchedFrame value fresh)]
        libraryWorld := by
      rw [read_body]
      exact .producerRaw ordinary
    simpa only [List.append_nil] using
      (Stateful.EquationBodiesRel.cons (work := opened release value)
        (original := Entry.Value.ofAtom (form release value))
        (expected := expected) (live := []) (scope := []) (frame := Frame.empty)
        (rfl : (matchedFrame value fresh).bindings = (opened release value).bindings)
        (open_concrete_call release value nonvar fresh)
        (by simpa only [Entry.Value.erase_ofAtom] using produced)
        (Stateful.BoundaryBatchRel.single_iff.mpr returned) Stateful.EquationBodiesRel.nil)

private theorem marker_not_function :
    ¬FunctionPending .unmarked (Entry.Value.ofAtom Atom.notReducible) := by
  simp [FunctionPending, Minimal.IsFunction, Atom.notReducible, Entry.Value.ofAtom, Entry.Value.erase]

/-- The prepared call to the authored `quote` rule returns the wrapper and does not touch
the world. A bound payload remains available in the reached source frame. -/
theorem prepared_quote (label : Bool) (value : Atom) (nonvar : isVariableB value = false)
    (closed : ∀ name, ¬AtomOccurs value name) :
    ∃ output : Frame, output.bindings = Bindings.empty.assign "atom" value ∧
      CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (quote value)) Atom.atomType
        Frame.empty [(Entry.Value.ofAtom (quote value), output)] libraryWorld := by
  have selected := frontier false label [Atom.atomType] value nonvar closed (by
    intro atom member
    simp only [List.mem_singleton] at member
    subst atom
    intro _ impossible
    cases impossible)
  apply marker_equation_call (work := opened false value)
  · simpa [Entry.Value.erase_ofAtom, form] using not_error false value
  · simpa [Entry.Value.erase_ofAtom, form] using non_dispatch false value
  · simpa [Entry.Value.erase_ofAtom, form, Frame.empty] using selected
  · rfl

/-- For a recovered ordinary body, unquote uses the real evaluator, with the reached
frame and the caller's evaluation demand. In particular the result may be effectful. -/
theorem prepared_unquote (label : Bool) (value : Atom) (nonvar : isVariableB value = false)
    (closed : ∀ name, ¬AtomOccurs value name) (fresh : "atom" ∉ TypeSubst.typeVars value)
    (noFunction : ¬FunctionPending .unmarked (Entry.Value.ofAtom value))
    (ordinary : value ≠ Atom.notReducible) (clean : ¬IsEmptyOrErrorRel value)
    {results : List Result} {after : World}
    (evaluates : AtomRel environment label libraryWorld [] [] (Entry.Value.ofAtom value) Atom.undefinedType
      (matchedFrame value fresh) results after) :
    CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (unquote value))
      Atom.undefinedType Frame.empty results after := by
  apply prepared_call true label value Atom.undefinedType nonvar closed
    (by intro _ impossible; cases impossible) fresh noFunction
  exact (returned_code_exact (by simpa [Entry.Value.erase_ofAtom] using ordinary)
    (by simpa [Entry.Value.erase_ofAtom] using clean)).mpr evaluates

/-- Negative control: in HE the authored unquote is not a pure inverse of quote. Unquoting
the ordinary symbol `NotReducible` asks the caller to return the original unquote call. -/
theorem unquote_marker (label : Bool) :
    ∃ output : Frame, output.bindings = Bindings.empty.assign "atom" Atom.notReducible ∧
      CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (unquote Atom.notReducible))
        Atom.undefinedType Frame.empty [(Entry.Value.ofAtom (unquote Atom.notReducible), output)] libraryWorld := by
  refine ⟨matchedFrame Atom.notReducible (by decide), rfl, ?_⟩
  exact prepared_call true label Atom.notReducible Atom.undefinedType rfl
    (by intro _ impossible; cases impossible) (by intro _ impossible; cases impossible)
    (by decide) marker_not_function
    ((returned_not_reducible_exact (by simp [Entry.Value.erase_ofAtom])).mpr ⟨rfl, rfl⟩)

/-- Error-shaped and empty payloads take the stop case, not the marker case. Unlike
`NotReducible`, such a payload is returned itself rather than restoring the wrapper. -/
theorem unquote_stopped (label : Bool) (value : Atom)
    (nonvar : isVariableB value = false) (closed : ∀ name, ¬AtomOccurs value name)
    (noFunction : ¬FunctionPending .unmarked (Entry.Value.ofAtom value))
    (stopped : IsEmptyOrErrorRel value) :
    ∃ output : Frame, output.bindings = Bindings.empty.assign "atom" value ∧
      CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (unquote value))
        Atom.undefinedType Frame.empty [(Entry.Value.ofAtom value, output)] libraryWorld := by
  have fresh : "atom" ∉ TypeSubst.typeVars value := fun member =>
    closed _ ((atomOccurs_iff_mem_typeVars _ _).mpr member)
  refine ⟨matchedFrame value fresh, rfl, ?_⟩
  exact prepared_call true label value Atom.undefinedType nonvar closed
    (by intro _ impossible; cases impossible) fresh noFunction
    (.returned (.stopped (by simpa [Entry.Value.erase_ofAtom] using stopped)))

def evalUnquoteMarker : Entry.Value :=
  .expression .active [.symbol "eval", Entry.Value.ofAtom (unquote Atom.notReducible)]

private theorem eval_marker_minimal (label : Bool) (live : List Atom)
    (saved : ∀ atom ∈ live, ∀ name, ¬AtomOccurs atom name) :
    MinimalRel environment label libraryWorld live [] none evalUnquoteMarker Frame.empty
      [(.symbol "NotReducible", matchedFrame Atom.notReducible (by decide))] libraryWorld := by
  unfold evalUnquoteMarker
  apply Stateful.MinimalRel.eval
  simp only [Frame.read_empty]
  let work := opened true Atom.notReducible
  apply Stateful.InvocationRel.equations (works := [work])
  · simpa [Entry.Value.erase_ofAtom, form] using non_dispatch true Atom.notReducible
  · rw [Entry.Value.erase_ofAtom]
    exact frontier true label live Atom.notReducible rfl (by intro _ impossible; cases impossible) saved
  · simp
  · have produced : BoundaryRel environment label libraryWorld live []
        (some (unquote Atom.notReducible)) .producer
        ((matchedFrame Atom.notReducible (by decide)).read .unmarked (Entry.Value.ofAtom work.body))
        (matchedFrame Atom.notReducible (by decide))
        [(.symbol "NotReducible", matchedFrame Atom.notReducible (by decide))] libraryWorld := by
      rw [read_body true Atom.notReducible]
      simpa [Atom.notReducible, Entry.Value.ofAtom] using
        (Stateful.BoundaryRel.producerRaw (environment := environment) (label := label)
          (world0 := libraryWorld) (live := live) (scope := [])
          (caller := some (unquote Atom.notReducible))
          (frame := matchedFrame Atom.notReducible (by decide)) marker_not_function)
    simpa only [List.append_nil] using
      (Stateful.InvocationEquationsRel.cons (work := work)
        (original := Entry.Value.ofAtom (unquote Atom.notReducible))
        (live := live) (scope := []) (frame := Frame.empty)
        (rfl : (matchedFrame Atom.notReducible (by decide)).bindings = work.bindings)
        (open_concrete_call true Atom.notReducible rfl (by decide))
        (by simpa only [Entry.Value.erase_ofAtom] using produced) Stateful.InvocationEquationsRel.nil)

/-- Explicit invocation can recover the literal marker. The full call then interprets it at
its caller boundary, returning the outer `eval` expression rather than the inner call. -/
theorem eval_unquote_marker (label : Bool) :
    ∃ output : Frame,
      MinimalRel environment label libraryWorld [] [] none evalUnquoteMarker Frame.empty
        [(.symbol "NotReducible", output)] libraryWorld ∧
      CallRel environment label libraryWorld [] [] evalUnquoteMarker Atom.undefinedType Frame.empty
        [(evalUnquoteMarker, output)] libraryWorld := by
  refine ⟨matchedFrame Atom.notReducible (by decide), eval_marker_minimal label [] (by simp), ?_⟩
  have noHost : ¬Minimal.HostCall environment.dispatch evalUnquoteMarker.erase := by
    simp [environment, evalUnquoteMarker, Entry.Value.erase, Entry.Value.erase_ofAtom, Minimal.HostCall]
  have instruction : Minimal.embeddedInstruction evalUnquoteMarker.erase = true := by
    simp [evalUnquoteMarker, Entry.Value.erase, Entry.Value.erase_ofAtom, Minimal.embeddedInstruction]
  have invoked : InvocationRel environment label libraryWorld [Atom.undefinedType] [] none
      evalUnquoteMarker Frame.empty [(.symbol "NotReducible", matchedFrame Atom.notReducible (by decide))]
      libraryWorld :=
    .embedded noHost instruction (eval_marker_minimal label [Atom.undefinedType]
      (by simpa using (show ∀ name, ¬AtomOccurs Atom.undefinedType name from
        fun _ impossible => by cases impossible)))
  exact .embedded (by simp [evalUnquoteMarker, Entry.Value.erase, Entry.Value.erase_ofAtom, IsErrorRel])
    noHost instruction invoked (Stateful.BoundaryBatchRel.single_iff.mpr
      (.returned (.notReducible (by simp [Atom.notReducible, Entry.Value.erase]))))

/-- A runnable payload with a concrete interpretation from the existing world host. -/
def contextQuery : Atom := .expression [.symbol "context-space"]

theorem contextQuery_closed (name : String) : ¬AtomOccurs contextQuery name := by
  intro occurs
  cases occurs with
  | expression member child =>
      simp only [List.mem_singleton] at member
      subst member
      cases child

private theorem scalar_cast {env : WorldEnvironment Bool World} {world : World}
    (label : Bool) (live : List Atom) (frame : Frame)
    (value : Entry.Value) (expected tag : Atom)
    (read : frame.read .unmarked value = value)
    (entry : Entry.Rel Policy.unmarked.reentry value.status value.erase expected .cast)
    (stored : StorageTypesRel (env.view world label) value.erase [tag])
    (matched : TypeMatchRel expected tag frame.bindings frame.bindings)
    (scope : List String := []) (lookupIsRaw : env.lookup = rawLookup := by rfl) :
    AtomRel env label world live scope value expected frame [(value, frame)]
      world := by
  apply Stateful.AtomRel.cast (raw := [(value.erase,frame.bindings)])
  · simpa only [read] using entry
  · simp only [read]
    rw [lookupIsRaw]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) stored rfl (by simp)
      (frame.preserved_type_match .unmarked matched)
  · exact .cons ⟨rfl, .same frame, by simp [read]⟩ .nil

private theorem untyped_library_symbol (label : Bool) (name : String)
    (notQuote : name ≠ "quote") (notUnquote : name ≠ "unquote") :
    StorageTypesRel (environment.view libraryWorld label) (.symbol name) [Atom.undefinedType] := by
  apply StorageTypesRel.symbolUndefined
  refine .skip ?_ (.skip ?_ (.skip ?_ (.skip ?_ .nil))) <;>
    intro type <;> simp [signature, row, Ne.symm notQuote, Ne.symm notUnquote]

private theorem untyped_context_head (label : Bool) :
    StorageTypesRel (environment.view libraryWorld label) (.symbol "context-space") [Atom.undefinedType] :=
  untyped_library_symbol label "context-space" (by decide) (by decide)

private theorem evaluate_context (label : Bool) (frame : Frame) :
    AtomRel environment label libraryWorld [] [] (Entry.Value.ofAtom contextQuery) Atom.undefinedType
      frame [(.grounded (services.contextPayload label), frame)] libraryWorld := by
  let code : Entry.Value := .expression .active [.symbol "context-space"]
  let handle : Entry.Value := .grounded (services.contextPayload label)
  have codeRead : frame.read .unmarked (Entry.Value.ofAtom contextQuery) = code := by
    simp [contextQuery, Entry.Value.ofAtom, Frame.read, Entry.Value.substitute,
      Entry.Value.rebuildStatus, Policy.unmarked, code]
  have headed : ∀ live, AtomRel environment label libraryWorld live [] (.symbol "context-space")
        Atom.undefinedType frame [(.symbol "context-space", frame)] libraryWorld := by
    intro live
    have entry : Entry.Rel Policy.unmarked.reentry .active (.symbol "context-space")
        Atom.undefinedType .cast :=
      .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol _)
        (by decide) (Or.inl ⟨_, rfl⟩) (by intro impossible; cases impossible)
    exact scalar_cast label live frame (.symbol "context-space") Atom.undefinedType Atom.undefinedType
      (by simp [Frame.read, Entry.Value.substitute]) (by simpa [Entry.Value.erase, Entry.Value.status] using entry)
      (by simpa only [Entry.Value.erase] using untyped_context_head label)
      (.undefinedLeft _ _)
  have grounded : AtomRel environment label libraryWorld [] [] handle Atom.undefinedType frame
      [(handle, frame)] libraryWorld := by
    apply scalar_cast label [] frame handle Atom.undefinedType (.symbol "Number")
      (by simp [handle, Frame.read, Entry.Value.substitute])
    · have entry : Entry.Rel Policy.unmarked.reentry .active (.grounded (services.contextPayload label))
          Atom.undefinedType .cast :=
        .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.grounded _)
          (by decide) (Or.inr (Or.inl ⟨_, rfl⟩)) (by intro impossible; cases impossible)
      simpa [handle, Entry.Value.erase, Entry.Value.status] using entry
    · simpa [handle, services, Entry.Value.erase] using
        (StorageTypesRel.groundedKnown (space := environment.view libraryWorld label)
          (.int (if label then 1 else 0)) (by decide))
    · exact .undefinedLeft _ _
  have called : CallRel environment label libraryWorld [] [] code Atom.undefinedType frame [(handle, frame)]
      libraryWorld := by
    have noHost : ¬Minimal.HostCall environment.dispatch code.erase := by
      simp [Minimal.HostCall, environment]
    have instruction : Minimal.embeddedInstruction code.erase = true := by
      simp [code, Entry.Value.erase, Minimal.embeddedInstruction]
    exact .embedded (by simp [code, Entry.Value.erase, IsErrorRel]) noHost instruction
      (.embedded noHost instruction .contextSpace)
      (Stateful.BoundaryBatchRel.single_iff.mpr (.returned
        (.evaluate (by simp [Entry.Value.erase, Atom.notReducible])
          (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) grounded)))
  have priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ([ (handle, frame) ].map (readResult .unmarked)) [(handle, frame)] := by
    have chosen := SuccessPriorityRel.successes
      (isError := fun result : Result => isErrorAtom result.1.erase)
      (raw := [(handle, frame)]) ⟨(handle, frame), by simp, by simp [handle, Entry.Value.erase, isErrorAtom]⟩
    simpa [readResult, Frame.read, handle, Entry.Value.substitute, Entry.Value.erase, isErrorAtom] using chosen
  have entry : Entry.Rel Policy.unmarked.reentry .active (.expression [.symbol "context-space"])
      Atom.undefinedType .interpret :=
    .expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl)
  have tuple : TupleRel environment label libraryWorld [Atom.undefinedType] []
      [.symbol "context-space"] frame [(code, frame)] libraryWorld := by
    simpa [Completed.tupleSingleton, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, code]
      using Stateful.TupleRel.singleton (headed [Atom.undefinedType])
  have run := Stateful.AtomRel.tuple
    (environment := environment) (label := label) (world0 := libraryWorld)
    (live := []) (scope := []) (value := Entry.Value.ofAtom contextQuery) (expected := Atom.undefinedType)
    (frame := frame) (operator := .symbol "context-space") (arguments := [])
    (rows := [(code, frame)]) (raw := [(handle, frame)])
    (by simpa [codeRead, code, Entry.Value.erase, Entry.Value.status] using entry)
    codeRead
    (by simpa [Entry.Value.erase] using (untyped_context_head label).occurrences)
    tuple
    (by simpa only [List.append_nil] using Stateful.CallsRel.cons called Stateful.CallsRel.nil)
    priority
  simpa [publishResult, Entry.Value.publish, handle, Entry.Value.withStatus] using run

/-- Releasing the quoted context query returns its handle. Quoting the same input instead
returns the wrapped expression (see `prepared_quote`), without requesting the handle. -/
theorem unquote_context_space (label : Bool) :
    ∃ output : Frame,
      CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (unquote contextQuery))
        Atom.undefinedType Frame.empty [(.grounded (services.contextPayload label), output)] libraryWorld := by
  refine ⟨matchedFrame contextQuery (by decide), ?_⟩
  exact prepared_unquote label contextQuery rfl contextQuery_closed (by decide)
    (by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase_ofAtom, contextQuery])
    (by simp [contextQuery, Atom.notReducible]) (by simp [contextQuery, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (evaluate_context label _)

/-! ### A caller that already uses the library's binder -/

/-- The caller owns the same spelling as the library's pattern variable. -/
def quoteCaller : Frame := matchedFrame (.symbol "prior") (by decide)

def openQuote : Atom := quote (.expression [.symbol "pair", .var "atom", .var "atom"])
def callerPair : Atom := .expression [.symbol "pair", .symbol "prior", .symbol "prior"]

private theorem read_open_quote :
    quoteCaller.read .unmarked (Entry.Value.ofAtom openQuote) = Entry.Value.ofAtom (quote callerPair) := by
  simp [openQuote, quote, callerPair, quoteCaller, matchedFrame, Frame.read, Entry.Value.ofAtom,
    Entry.Value.substitute, Entry.Value.resolve, Entry.Value.rebuildStatus, Policy.unmarked]

private theorem scoped_quote (label : Bool) (live : List Atom) (frame : Frame) (key : String) (value : Atom)
    (nonvariable : isVariableB value = false) (absent : ¬AtomOccurs value key)
    (fresh : ¬QueryVisibleName (Atom.atomType :: live) (quote value) frame.bindings key)
    (freshFrame : key ∉ specBindingVars frame.bindings) :
    ∃ reached : Frame, reached.bindings = frame.bindings.assign key value ∧
      CallRel environment label libraryWorld live [] (Entry.Value.ofAtom (quote value)) Atom.atomType
        frame [(Entry.Value.ofAtom (quote value), reached)] libraryWorld := by
  have front := scoped_frontier false label (Atom.atomType :: live) value frame key nonvariable absent
    (by simpa [form] using fresh) freshFrame
  apply marker_equation_call (work := opened false value key frame.bindings)
  · simpa [Entry.Value.erase_ofAtom, form] using not_error false value
  · simpa [Entry.Value.erase_ofAtom, form] using non_dispatch false value
  · simpa [Entry.Value.erase_ofAtom, form] using front
  · rfl

private theorem scoped_quote_call (label : Bool) :
    ∃ reached : Frame, reached.bindings = quoteCaller.bindings.assign "quote#local" callerPair ∧
      CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom (quote callerPair)) Atom.atomType
        quoteCaller [(Entry.Value.ofAtom (quote callerPair), reached)] libraryWorld :=
  scoped_quote label [] quoteCaller "quote#local" callerPair rfl
    (by simp [atomOccurs_iff_mem_typeVars, callerPair, TypeSubst.typeVars, TypeSubst.typeVarsList])
    (by simp [QueryVisibleName, atomOccurs_iff_mem_typeVars, quote, callerPair,
      TypeSubst.typeVars, TypeSubst.typeVarsList, quoteCaller, matchedFrame, assignment, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup, Atom.atomType])
    (by simp [specBindingVars, quoteCaller, matchedFrame, assignment, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup, TypeSubst.typeVars])

/-- Keeping the literal library variable would identify it with the caller's existing key.
It is not a legal instance of the source's alpha-variant relation. -/
theorem raw_quote_binder_rejected :
    ¬AlphaVariantRel [Atom.atomType] (quote callerPair) quoteCaller.bindings
      (quote (.var "atom")) Atom.notReducible (quote (.var "atom")) Atom.notReducible := by
  rintro ⟨rename, _, renamed, _, fresh⟩
  have same : rename "atom" = "atom" := by
    simpa [quote, renameTypeVars] using (EquationFreshening.alphaRename_eq renamed).symm
  have visible : QueryVisibleName [Atom.atomType] (quote callerPair) quoteCaller.bindings "atom" := by
    exact Or.inr (Or.inr (Or.inl ⟨.symbol "prior", by
      simp [quoteCaller, matchedFrame, assignment, Bindings.assign, Bindings.isBound,
        Bindings.lookup, Bindings.empty]⟩))
  have occurs : AtomOccurs (quote (.var "atom")) "atom" := by
    rw [atomOccurs_iff_mem_typeVars]
    simp [quote, TypeSubst.typeVars, TypeSubst.typeVarsList]
  exact fresh "atom" (Or.inl occurs) (same.symm ▸ visible)

private def libraryName (release : Bool) : String := if release then "unquote" else "quote"
private def demandName (release : Bool) : String := if release then "%Undefined%" else "Atom"
private def argumentDemand (release : Bool) : Atom := .symbol (demandName release)

private def librarySignature (release : Bool) : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", argumentDemand release, argumentDemand release],
    [argumentDemand release], argumentDemand release, rfl⟩

private abbrev quoteSignature := librarySignature false

private def libraryApply (release : Bool) (argument : Atom) : Atom :=
  .expression [.symbol (libraryName release), argument]

private theorem library_head_type (release label : Bool) :
    StorageTypesRel (environment.view libraryWorld label) (.symbol (libraryName release))
      [(librarySignature release).functionType] := by
  cases release
  · apply StorageTypesRel.symbolKnown ?_ (by simp)
    refine .hit (.skip ?_ (.skip ?_ (.skip ?_ .nil))) <;>
      intro type <;> simp [row, signature, libraryName]
  · apply StorageTypesRel.symbolKnown ?_ (by simp)
    refine .skip ?_ (.skip ?_ (.hit (.skip ?_ .nil))) <;>
      intro type <;> simp [row, signature, libraryName]

private theorem unannotated_application (label : Bool) (head : Atom) (tail : List Atom) :
    StorageTypesRel (environment.view libraryWorld label) (.expression (head :: tail)) [Atom.undefinedType] := by
  apply StorageTypesRel.expressionUndefined
  refine .skip ?_ (.skip ?_ (.skip ?_ (.skip ?_ .nil))) <;>
    intro type <;> simp [row, signature]

private theorem library_selects (release label : Bool) (live : List Atom) (frame : Frame)
    (argument actual : Atom)
    (declared : StorageTypesRel (environment.view libraryWorld label) argument [actual]) :
    InvocationSelectionRel (environment.view libraryWorld label) environment.lookup .unmarked live []
      (libraryApply release argument) (.symbol (libraryName release)) Atom.undefinedType frame
      (.selected (librarySignature release) [frame]) := by
  have matched : TypeMatchRel (argumentDemand release) actual frame.bindings frame.bindings := by
    cases release
    · exact .atomLeft _ _
    · exact .undefinedLeft _ _
  have typed : TypeCheckRel .unmarked (argumentDemand release) frame actual (.inr frame) :=
    .accepted (.unchanged (frame.preserved_type_match .unmarked matched))
  have arguments : ArgumentChecksRel (environment.view libraryWorld label)
      (rawTypeLookupRel (environment.view libraryWorld label)) .unmarked
      (libraryApply release argument) argument (argumentDemand release) 1 [frame] [frame] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := libraryApply release argument) (position := 1)
        declared (.cons typed .nil) .nil)
  have returns : TypeCheckRel .unmarked Atom.undefinedType frame (argumentDemand release) (.inr frame) :=
    .accepted (.unchanged (frame.preserved_type_match .unmarked (.undefinedLeft _ _)))
  have checks : ApplicationChecksRel (environment.view libraryWorld label)
      (rawTypeLookupRel (environment.view libraryWorld label)) .unmarked
      (libraryApply release argument) Atom.undefinedType (librarySignature release) frame [frame] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (selected := librarySignature release) (before := frame)
        (show libraryApply release argument = .expression [.symbol (libraryName release), argument] by rfl)
        (.cons arguments .nil) (.cons returns .nil))
  exact ⟨_, library_head_type release label, .selected checks (by simp)⟩

private theorem library_operator (release label : Bool) (live : List Atom) (scope : List String) (frame : Frame) :
    AtomRel environment label libraryWorld live scope (.symbol (libraryName release))
      (librarySignature release).functionType frame [(.symbol (libraryName release), frame)] libraryWorld := by
  have entry : Entry.Rel Policy.unmarked.reentry .active (.symbol (libraryName release))
      (librarySignature release).functionType .cast :=
    .cast (by cases release <;> simp [libraryName, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol _)
      (by cases release <;> decide) (Or.inl ⟨_, rfl⟩) (by intro impossible; cases impossible)
  apply scalar_cast label live frame (.symbol (libraryName release)) (librarySignature release).functionType
    (librarySignature release).functionType (by simp [Frame.read, Entry.Value.substitute])
    (by simpa only [Entry.Value.status, Entry.Value.erase] using entry)
    (by simpa only [Entry.Value.erase] using library_head_type release label) (scope := scope)
  refine TypeMatchRel.structural (matched := Bindings.empty)
    (by cases release <;> decide) (by cases release <;> decide)
    (by cases release <;> decide) (by cases release <;> decide) ?_ (.mk (.refl _) .nil)
  exact .expression (.cons (.symSym "->" semanticLoopFree_empty) empty_merge
    (.cons (.symSym (demandName release) semanticLoopFree_empty) empty_merge
      (.cons (.symSym (demandName release) semanticLoopFree_empty) empty_merge .nil))) semanticLoopFree_empty

private theorem library_prepares (release label : Bool) (live : List Atom)
    {before reached : Frame} {input output : Entry.Value} {after : World}
    (arguments : ArgumentsRel environment label libraryWorld
      (.symbol (libraryName release) :: live) [] [(input, argumentDemand release)] before
      [(Entry.Value.argumentPacket [output], reached)] after) :
    FunctionRel environment label libraryWorld live [] Atom.undefinedType (librarySignature release)
      (.symbol (libraryName release)) [input] before
      [(.expression .active [.symbol (libraryName release), output], reached)] after := by
  refine HEArgumentContexts.function_of_one_operator (head := .symbol (libraryName release))
    (ready := before) (middle := libraryWorld)
    (packets := [(Entry.Value.argumentPacket [output], reached)]) ?_ ?_ ?_ ?_
  · rfl
  · simpa only [Entry.Value.erase, List.map_cons, List.map_nil, List.cons_append, List.nil_append, libraryApply] using
      library_operator release label ((librarySignature release).functionType :: input.erase :: live)
        (expectedApplicationScope (libraryApply release input.erase) Atom.undefinedType) before
  · cases release <;> simp [libraryName, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · simpa [Entry.Value.erase, librarySignature] using arguments

private theorem quote_prepares (label : Bool) (live : List Atom) (frame : Frame) (argument : Atom)
    (closed : ∀ name, ¬AtomOccurs argument name) :
    FunctionRel environment label libraryWorld live [] Atom.undefinedType quoteSignature
      (.symbol "quote") [Entry.Value.ofAtom argument] frame
      [(Entry.Value.ofAtom (quote argument), frame)] libraryWorld := by
  let value := Entry.Value.ofAtom argument
  have read : frame.read .unmarked value = value :=
    frame.read_variable_free .unmarked value (by simpa only [value, Entry.Value.erase_ofAtom] using closed)
  have args : ArgumentsRel environment label libraryWorld
      (.symbol "quote" :: live) [] [(value, Atom.atomType)] frame
      [(Entry.Value.argumentPacket [value], frame)] libraryWorld :=
    HEArgumentContexts.singleton_atom_exact.mpr
      ⟨rfl, Or.inr ⟨by simp [read, ArgumentStopped], by rw [read]⟩⟩
  simpa [quote, libraryName, Entry.Value.ofAtom, value] using library_prepares false label live
    (by simpa [libraryName, argumentDemand, demandName, Atom.atomType] using args)

private theorem unmarked_publish (original : Atom) (answer : Result) (active : answer.1.status = .active) :
    publishResult .unmarked original answer = answer := by
  obtain ⟨value, frame⟩ := answer
  cases value
  case expression status children =>
    change status = .active at active
    subst status
    simp [publishResult, Entry.Value.publish, Entry.Value.withStatus, Entry.publish,
      Policy.unmarked, Entry.Value.erase]
  all_goals simp [publishResult, Entry.Value.publish, Entry.Value.withStatus]

private theorem library_completes (release label : Bool) (live : List Atom)
    {before middleFrame : Frame} {original operand prepared : Entry.Value} {actual : Atom}
    {middle final : World} {answer : Result}
    (shape : before.read .unmarked original = .expression .active [.symbol (libraryName release), operand])
    (declared : StorageTypesRel (environment.view libraryWorld label) operand.erase [actual])
    (interpreted : FunctionRel environment label libraryWorld
      (invocationReturnType (librarySignature release) :: live) [] Atom.undefinedType
      (librarySignature release) (.symbol (libraryName release)) [operand] before
      [(.expression .active [.symbol (libraryName release), prepared], middleFrame)] middle)
    (called : CallRel environment label middle live [] (.expression .active [.symbol (libraryName release), prepared])
      (invocationReturnType (librarySignature release)) middleFrame [answer] final)
    (read : answer.2.read .unmarked answer.1 = answer.1) (active : answer.1.status = .active) :
    AtomRel environment label libraryWorld live [] original Atom.undefinedType before [answer] final := by
  have entry : Entry.Rel Policy.unmarked.reentry .active (libraryApply release operand.erase)
      Atom.undefinedType .interpret :=
    .expression (head := .symbol (libraryName release)) (tail := [operand.erase])
      (by cases release <;> simp [libraryName, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (by decide) (Or.inr rfl)
  have run := HEArgumentContexts.completed_typed_one (operator := .symbol (libraryName release))
    (operands := [operand])
    (original := original) (policy := .unmarked)
    (by simpa [shape, libraryApply, Entry.Value.erase, Entry.Value.status] using entry) shape
    (by simpa [shape, libraryApply, Entry.Value.erase, environment, ArgumentService.selection]
      using library_selects release label live before operand.erase actual declared)
    interpreted called
  have preserved : readResult .unmarked answer = answer := by
    cases answer
    simp only [readResult, read]
  simpa only [preserved, unmarked_publish _ _ active] using run

/-- This starts with the open source call, not a prepared call. The two uses of the caller
variable read the same binding. The library scope adds a different key for the whole payload,
and the result returns through the actual typed invocation and publication rules. -/
theorem open_quote_retains_frame (label : Bool) :
    ∃ reached : Frame, reached.bindings = quoteCaller.bindings.assign "quote#local" callerPair ∧
      AtomRel environment label libraryWorld [] [] (Entry.Value.ofAtom openQuote) Atom.undefinedType
        quoteCaller [(Entry.Value.ofAtom (quote callerPair), reached)] libraryWorld ∧
      (reached.read .unmarked (.var "atom")).erase = .symbol "prior" ∧
      (reached.read .unmarked (.var "quote#local")).erase = callerPair := by
  obtain ⟨reached, bindings, called⟩ := scoped_quote_call label
  refine ⟨reached, bindings, ?_⟩
  have shape : quoteCaller.read .unmarked (Entry.Value.ofAtom openQuote) =
      .expression .active [.symbol "quote", Entry.Value.ofAtom callerPair] := by
    simpa [quote, Entry.Value.ofAtom] using read_open_quote
  have read (key : String) (value : Atom) (bound : (key, value) ∈ reached.bindings.assignments)
      (closed : ∀ valuation, applyTypeValuation valuation value = value) :
      (reached.read .unmarked (.var key)).erase = value := by
    rw [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase]
    exact reached.certified.forced_read (.var key) value
      (fun valuation satisfied => by
        simpa only [applyTypeValuation] using (satisfied.1 key value bound).trans (closed valuation))
  refine ⟨?_, read "atom" (.symbol "prior") ?_ (by intro valuation; simp [applyTypeValuation]),
    read "quote#local" callerPair ?_ ?_⟩
  · have payloadClosed : ∀ name, ¬AtomOccurs callerPair name := by
      intro name
      simp [callerPair, atomOccurs_iff_mem_typeVars, TypeSubst.typeVars, TypeSubst.typeVarsList]
    apply library_completes false label [] (operand := Entry.Value.ofAtom callerPair)
      (prepared := Entry.Value.ofAtom callerPair) (middleFrame := quoteCaller) (by simpa [libraryName] using shape)
    · simpa only [Entry.Value.erase_ofAtom, callerPair] using
        unannotated_application label (.symbol "pair") [.symbol "prior", .symbol "prior"]
    · simpa [libraryName, librarySignature, argumentDemand, demandName, invocationReturnType, Atom.atomType,
        Atom.expressionType, quote, Entry.Value.ofAtom] using quote_prepares label [Atom.atomType] quoteCaller
          callerPair payloadClosed
    · simpa [libraryName, librarySignature, argumentDemand, demandName, invocationReturnType, Atom.atomType,
        Atom.expressionType, quote, Entry.Value.ofAtom] using called
    · simp [Frame.read, quote, callerPair, Entry.Value.ofAtom, Entry.Value.substitute,
        Entry.Value.rebuildStatus, Policy.unmarked]
    · simp [Entry.Value.ofAtom, quote, Entry.Value.status]
  · rw [bindings]
    decide +kernel
  · rw [bindings]
    decide +kernel
  · intro valuation
    simp [callerPair, applyTypeValuation]

/-- Release starts from the exact annotated readout of the fresh rule variable, then
runs the ordinary return boundary in the reached frame. The caller may already carry
bindings introduced by evaluating the argument. -/
private theorem scoped_release (label : Bool) (live : List Atom) (before : Frame) (key : String) (value : Atom)
    (closed : ∀ name, ¬AtomOccurs value name) (nonvar : isVariableB value = false)
    (fresh : key ∉ specBindingVars before.bindings)
    (localKey : key ∉ TypeSubst.typeVars (Entry.Value.ofAtom value).erase)
    (scopeFresh : ¬QueryVisibleName (Atom.undefinedType :: live) (unquote value) before.bindings key)
    (plain : ¬FunctionPending .unmarked (Entry.Value.ofAtom value))
    (ordinary : value ≠ Atom.notReducible) (clean : ¬IsEmptyOrErrorRel value)
    {answers : List Result} {after : World}
    (run : AtomRel environment label libraryWorld live [] (Entry.Value.ofAtom value) Atom.undefinedType
      (assignFresh .unmarked before key (Entry.Value.ofAtom value) fresh localKey) answers after) :
    CallRel environment label libraryWorld live [] (Entry.Value.ofAtom (unquote value))
      Atom.undefinedType before answers after := by
  let payload := Entry.Value.ofAtom value
  let next := assignFresh .unmarked before key payload fresh localKey
  let work := opened true value key before.bindings
  let call := Entry.Value.ofAtom (unquote value)
  have stable : before.read .unmarked payload = payload := by
    apply before.read_variable_free
    simpa only [payload, Entry.Value.erase_ofAtom] using closed
  have selected : EquationFrontierRel (environment.view libraryWorld label)
      (Atom.undefinedType :: live) call.erase before.bindings [work] := by
    simpa [call, Entry.Value.erase_ofAtom, form, work] using scoped_frontier true label
      (Atom.undefinedType :: live) value before key nonvar (closed key) (by simpa [form] using scopeFresh) fresh
  have binds : Entry.Value.UnifyRel Policy.unmarked.rebuilding before.environment payload (.var key)
      next.environment := by
    apply assignFresh_unifies
    intro name same
    rw [stable] at same
    have bare : value = .var name := by simpa only [payload, Entry.Value.erase_ofAtom] using same
    simp [bare, isVariableB] at nonvar
  have unified : Entry.Value.UnifyRel Policy.unmarked.rebuilding before.environment call
      (Entry.Value.ofAtom work.pattern) next.environment := by
    simpa [call, work, opened, form, unquote, quote, Entry.Value.ofAtom, payload] using
      unary_unifies .unmarked before "unquote" (unary_unifies .unmarked before "quote" binds)
  have read : next.read .unmarked (Entry.Value.ofAtom work.body) = payload := by
    simpa [work, opened, rhs, Entry.Value.ofAtom, stable, next] using
      assignFresh_reads .unmarked before key payload fresh localKey
  have produced : BoundaryRel environment label libraryWorld (Atom.undefinedType :: live) []
      (some call.erase) .producer (next.read .unmarked (Entry.Value.ofAtom work.body)) next
      [(payload, next)] libraryWorld := by
    rw [read]
    exact .producerRaw plain
  have returned : BoundaryRel environment label libraryWorld live [] none (.returned call Atom.undefinedType)
      payload next answers after :=
    (returned_code_exact (by simpa only [payload, Entry.Value.erase_ofAtom] using ordinary)
      (by simpa only [payload, Entry.Value.erase_ofAtom] using clean)).mpr run
  apply Stateful.CallRel.equations (works := [work])
  · simpa [call, Entry.Value.erase_ofAtom, form] using not_error true value
  · simpa [call, Entry.Value.erase_ofAtom, form] using non_dispatch true value
  · exact selected
  · simp
  · have agrees : next.bindings = work.bindings := by
      simp [next, work, opened, assignFresh, payload, Entry.Value.erase_ofAtom]
    simpa only [List.append_nil] using Stateful.EquationBodiesRel.cons agrees unified produced
      (Stateful.BoundaryBatchRel.single_iff.mpr returned) Stateful.EquationBodiesRel.nil

/-- The caller already owns the library's variable spelling and has stored executable
syntax, not its evaluated handle. -/
def releaseCaller : Frame := matchedFrame contextQuery (by decide)
def openRelease : Atom := unquote (.var "atom")

/-- Start with actual open source, including the inner `quote` as an evaluated argument of
`unquote`. The two rule activations have separate fresh keys; only the released body calls
the context operation. -/
theorem open_unquote_executes (label : Bool) :
    ∃ frame : Frame,
      AtomRel environment label libraryWorld [] [] (Entry.Value.ofAtom openRelease) Atom.undefinedType
        releaseCaller [(.grounded (services.contextPayload label), frame)] libraryWorld ∧
      frame.bindings =
        (releaseCaller.bindings.assign "quote#local" contextQuery).assign "release#local" contextQuery ∧
      (frame.read .unmarked (.var "atom")).erase = contextQuery := by
  let operand := Entry.Value.ofAtom (quote contextQuery)
  let live := [Atom.symbol "unquote", Atom.undefinedType]
  obtain ⟨inner, innerBindings, quotedCall⟩ :=
    scoped_quote label live releaseCaller "quote#local" contextQuery rfl (contextQuery_closed _)
      (by simp [QueryVisibleName, atomOccurs_iff_mem_typeVars, live, quote, contextQuery, TypeSubst.typeVars,
        TypeSubst.typeVarsList, releaseCaller, matchedFrame, assignment, Bindings.assign, Bindings.empty,
        Bindings.isBound, Bindings.lookup, Atom.atomType, Atom.undefinedType])
      (by decide)
  have initiallyHeld : releaseCaller.read .unmarked operand = operand := by
    simp [operand, quote, contextQuery, Entry.Value.ofAtom, Frame.read, Entry.Value.substitute,
      Entry.Value.rebuildStatus, Policy.unmarked]
  have quoted : AtomRel environment label libraryWorld live [] operand Atom.undefinedType releaseCaller
      [(operand, inner)] libraryWorld := by
    apply library_completes false label live (operand := Entry.Value.ofAtom contextQuery)
      (prepared := Entry.Value.ofAtom contextQuery) (middleFrame := releaseCaller)
    · rw [initiallyHeld]
      simp [operand, quote, Entry.Value.ofAtom, libraryName]
    · simpa only [Entry.Value.erase_ofAtom, contextQuery] using
        unannotated_application label (.symbol "context-space") []
    · simpa [libraryName, librarySignature, argumentDemand, demandName, invocationReturnType, Atom.atomType,
        Atom.expressionType, quote, Entry.Value.ofAtom] using
        quote_prepares label (Atom.atomType :: live) releaseCaller contextQuery contextQuery_closed
    · simpa [libraryName, librarySignature, argumentDemand, demandName, invocationReturnType, Atom.atomType,
        Atom.expressionType, operand, quote, Entry.Value.ofAtom] using quotedCall
    · simp [operand, quote, contextQuery, Frame.read, Entry.Value.ofAtom, Entry.Value.substitute,
        Entry.Value.rebuildStatus, Policy.unmarked]
    · simp [operand, quote, Entry.Value.ofAtom, Entry.Value.status]
  have remaining : ArgumentBranchesRel environment label libraryWorld live [] operand [] [(operand, inner)]
      [(Entry.Value.argumentPacket [operand], inner)] libraryWorld := by
    simpa only [List.map_cons, List.map_nil, argumentPrepend_packet, List.append_nil] using
      (Stateful.ArgumentBranchesRel.continuing (environment := environment) (label := label)
        (world0 := libraryWorld) (live := live) (scope := []) (original := operand)
        (requests := []) (head := (operand, inner)) (HEArgumentContexts.unchanged_error_is_not_argument_stop _ _)
        Stateful.ArgumentsRel.nil Stateful.ArgumentBranchesRel.nil)
  have arguments : ArgumentsRel environment label libraryWorld live [] [(operand, Atom.undefinedType)]
      releaseCaller [(Entry.Value.argumentPacket [operand], inner)] libraryWorld :=
    .cons (by simpa [argumentScope] using quoted) remaining
  have prepared := library_prepares true label [Atom.undefinedType]
    (by simpa [live, libraryName, argumentDemand, demandName, Atom.undefinedType] using arguments)
  have fresh : "release#local" ∉ specBindingVars inner.bindings := by
    rw [innerBindings]
    decide +kernel
  have localKey : "release#local" ∉ TypeSubst.typeVars (Entry.Value.ofAtom contextQuery).erase := by
    rw [Entry.Value.erase_ofAtom]
    decide
  let next := assignFresh .unmarked inner "release#local" (Entry.Value.ofAtom contextQuery) fresh localKey
  have released := scoped_release label [] inner "release#local" contextQuery contextQuery_closed rfl fresh localKey
    (by rw [innerBindings]
        simp [QueryVisibleName, atomOccurs_iff_mem_typeVars, quote, unquote, contextQuery, TypeSubst.typeVars,
          TypeSubst.typeVarsList, releaseCaller, matchedFrame, assignment, Bindings.assign, Bindings.empty,
          Bindings.isBound, Bindings.lookup, Atom.undefinedType]
        rintro _ _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp [TypeSubst.typeVars, TypeSubst.typeVarsList])
    (by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase_ofAtom, contextQuery])
    (by simp [contextQuery, Atom.notReducible]) (by simp [contextQuery, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (evaluate_context label next)
  have bindings : next.bindings =
      (releaseCaller.bindings.assign "quote#local" contextQuery).assign "release#local" contextQuery := by
    simp [next, assignFresh, Entry.Value.erase_ofAtom, innerBindings]
  refine ⟨next, ?_, bindings, ?_⟩
  · apply library_completes true label [] (operand := operand) (prepared := operand) (middleFrame := inner)
    · simp [openRelease, unquote, quote, contextQuery, releaseCaller, matchedFrame, Frame.read,
        Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.resolve, Entry.Value.rebuildStatus,
        Policy.unmarked, libraryName, operand]
    · simpa only [operand, quote, Entry.Value.erase_ofAtom] using
        unannotated_application label (.symbol "quote") [contextQuery]
    · simpa [invocationReturnType, librarySignature, argumentDemand, demandName, Atom.undefinedType,
        Atom.expressionType] using prepared
    · simpa [libraryName, librarySignature, argumentDemand, demandName, invocationReturnType, Atom.undefinedType,
        Atom.expressionType, operand, unquote, Entry.Value.ofAtom] using released
    · simp [Frame.read, Entry.Value.substitute]
    · simp [Entry.Value.status]
  · rw [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase]
    apply next.certified.forced_read
    intro valuation satisfied
    have retained := satisfied.1 "atom" contextQuery (by rw [bindings]; decide +kernel)
    simpa [applyTypeValuation, contextQuery] using retained

private def NativeWord (world : World) (label : Bool) (name : String) : Prop :=
  name ≠ "Empty" ∧ name ≠ "Error" ∧
    StorageTypesRel (environment.view world label) (.symbol name) [Atom.undefinedType]

private theorem native_word_eval (world : World) (label : Bool) (live : List Atom) (scope : List String)
    (frame : Frame) (name : String) (word : NativeWord world label name) :
    AtomRel environment label world live scope (.symbol name) Atom.undefinedType frame
      [(.symbol name, frame)] world := by
  apply scalar_cast label live frame (.symbol name) Atom.undefinedType Atom.undefinedType
    (by simp [Frame.read, Entry.Value.substitute]) (scope := scope)
  · have entered : Entry.Rel Policy.unmarked.reentry .active (.symbol name) Atom.undefinedType .cast :=
      .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, word.1])
        (.symbol _) (by decide) (Or.inl ⟨_, rfl⟩) (fun impossible => by cases impossible)
    simpa only [Entry.Value.status, Entry.Value.erase] using entered
  · simpa only [Entry.Value.erase] using word.2.2
  · exact .undefinedLeft _ _

/-- The ordinary tuple path assembles checked literal fields. A lone
symbol Error must also be excluded: putting it at the head of a suffix
would create an error packet even though the symbol itself is data. -/
private theorem native_fields_tuple (world : World) (label : Bool) (scope : List String)
    (frame : Frame) (fields : List Entry.Value)
    (ordinary : ∀ value ∈ fields, ¬IsEmptyOrErrorRel value.erase ∧ value.erase ≠ .symbol "Error")
    (literal : ∀ value ∈ fields, ∀ live,
      AtomRel environment label world live scope value Atom.undefinedType frame [(value, frame)] world)
    (live : List Atom) :
    TupleRel environment label world live scope fields frame
      [(.expression .active fields, frame)] world := by
  induction fields generalizing live with
  | nil => exact .nil
  | cons value rest ih =>
      have here := (ordinary value List.mem_cons_self).1
      cases rest with
      | nil =>
          have good := fun bad => here ((Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr bad)
          simpa only [List.map_singleton, Completed.tupleSingleton, if_neg good] using
            Stateful.TupleRel.singleton (literal value List.mem_cons_self live)
      | cons next rest =>
          have remaining : ∀ child ∈ next :: rest, ¬IsEmptyOrErrorRel child.erase ∧ child.erase ≠ .symbol "Error" :=
            fun child member => ordinary child (List.mem_cons_of_mem _ member)
          have first := literal value List.mem_cons_self (.expression ((next :: rest).map Entry.Value.erase) :: live)
          apply Stateful.TupleRel.cons first
          have combined := Stateful.TupleBranchesRel.continuing
            (environment := environment) (label := label) (live := live) (scope := scope)
            (world0 := world) (world1 := world)
            (head := (value, frame)) here
            (ih remaining (fun child found => literal child (List.mem_cons_of_mem _ found)) (value.erase :: live))
            Stateful.TupleBranchesRel.nil
          have headOfTail := (remaining next List.mem_cons_self).2
          have clean : ¬isEmptyOrError (Entry.Value.expression .active (next :: rest)).erase = true := by
            intro bad
            rcases (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr bad with empty | error
            · simp [Entry.Value.erase, Atom.empty] at empty
            · obtain ⟨tail, shape⟩ := error
              simp only [Entry.Value.erase, List.map_cons, Atom.expression.injEq, List.cons.injEq] at shape
              exact headOfTail shape.1
          simpa only [List.map_singleton, List.append_nil, Completed.tuplePrepend, if_neg clean] using combined

def demandPut : Entry.Value := command "put" (.symbol "written-by-demand")
def demandWritten (label : Bool) : World :=
  Function.update libraryWorld label (libraryWorld label ++ [.symbol "written-by-demand"])

private def unitReply : Entry.Value := .expression .active []

private theorem evaluate_unit {before : World} (label : Bool) (live : List Atom) (scope : List String)
    (frame : Frame) :
    AtomRel environment label before live scope unitReply Atom.undefinedType frame [(unitReply, frame)] before := by
  apply scalar_cast label live frame unitReply Atom.undefinedType Atom.undefinedType
    (by simp [Frame.read, unitReply, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked])
    (scope := scope)
  · have entered : Entry.Rel Policy.unmarked.reentry .active Atom.unit Atom.undefinedType .cast :=
      .cast (by simp [Atom.unit, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (.expression []) (by decide) (Or.inr (Or.inr rfl)) (fun _ => Or.inr rfl)
    simpa only [unitReply, Entry.Value.erase, Entry.Value.status, Atom.unit, List.map_nil] using entered
  · simpa only [unitReply, Entry.Value.erase, List.map_nil] using (StorageTypesRel.unit (environment.view before label))
  · exact .undefinedLeft _ _

private theorem command_returns_unit {world after : World} (label : Bool)
    (live : List Atom) (scope : List String) (frame : Frame) (name : String) (argument : Atom)
    (fields : ∀ word ∈ ["call-native", "model-store", name], NativeWord world label word)
    (literal : (∃ word, argument = .symbol word ∧ NativeWord world label word) ∨ argument = Atom.unit)
    (executed : execute label world (.symbol name) argument = ([Atom.unit], after)) :
    AtomRel environment label world live scope (command name argument) Atom.undefinedType frame
      [(unitReply, frame)] after := by
  let call := command name argument
  let operands : List Entry.Value := [.symbol "model-store", .symbol name, Entry.Value.ofAtom argument]
  have shape : call = .expression .active (.symbol "call-native" :: operands) := rfl
  have ordinaryWords (word : String) (member : word ∈ ["call-native", "model-store", name]) :
      ¬IsEmptyOrErrorRel (Entry.Value.symbol word).erase ∧ (Entry.Value.symbol word).erase ≠ .symbol "Error" := by
    obtain ⟨noEmpty, noError, _⟩ := fields word member
    simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, noEmpty, noError]
  have literalBoth : ¬IsEmptyOrErrorRel (Entry.Value.ofAtom argument).erase ∧
      (Entry.Value.ofAtom argument).erase ≠ .symbol "Error" := by
    rcases literal with ⟨word, rfl, noEmpty, noError, _⟩ | rfl <;>
      simp [Entry.Value.erase_ofAtom, Atom.unit, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, *]
  have prepared : TupleRel environment label world (Atom.undefinedType :: live) scope
      (.symbol "call-native" :: operands) frame [(call, frame)] world := by
    rw [shape]
    apply native_fields_tuple
    · intro field member
      simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact ordinaryWords "call-native" (by simp)
      · exact ordinaryWords "model-store" (by simp)
      · exact ordinaryWords name (by simp)
      · exact literalBoth
    · intro field member pending
      simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact native_word_eval world label pending scope frame "call-native" (fields _ (by simp))
      · exact native_word_eval world label pending scope frame "model-store" (fields _ (by simp))
      · exact native_word_eval world label pending scope frame name (fields _ (by simp))
      · rcases literal with ⟨word, rfl, untyped⟩ | rfl
        · simpa only [Entry.Value.ofAtom] using native_word_eval world label pending scope frame word untyped
        · simpa only [Atom.unit, Entry.Value.ofAtom, List.map_nil, unitReply] using evaluate_unit label pending scope frame
  have callRead : frame.read .unmarked call = call := by
    rcases literal with ⟨word, rfl, _⟩ | rfl <;>
      simp [call, command, native, Atom.unit, Entry.Value.ofAtom, Frame.read,
        Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked]
  have noHost : ¬Minimal.HostCall environment.dispatch call.erase := by
    simp [call, command, native, Entry.Value.erase, Minimal.HostCall, environment]
  have builtin : Minimal.embeddedInstruction call.erase = true := by
    simp [call, command, native, Entry.Value.erase, Minimal.embeddedInstruction]
  have ran : MinimalRel environment label world (Atom.undefinedType :: live) scope none
      call frame [(unitReply, frame)] after := by
    apply (command_exact label world name argument _ _ none .unmarked frame _ _).mpr
    simp [executed, unitReply, Atom.unit, Entry.Value.ofAtom]
  have nativeCall : CallRel environment label world live scope call Atom.undefinedType
      frame [(unitReply, frame)] after :=
    .embedded (by simp [call, command, native, Entry.Value.erase, IsErrorRel]) noHost builtin
      (.embedded noHost builtin ran)
      (Stateful.BoundaryBatchRel.single_iff.mpr (.returned
        (.evaluate (by simp [unitReply, Entry.Value.erase, Atom.notReducible])
          (by simp [unitReply, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
          (evaluate_unit label live scope frame))))
  have unitRead : frame.read .unmarked unitReply = unitReply := by
    simp [Frame.read, unitReply, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked]
  have priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ([(unitReply, frame)].map (readResult .unmarked)) [(unitReply, frame)] := by
    have chosen := SuccessPriorityRel.successes
      (isError := fun result : Result => isErrorAtom result.1.erase)
      (raw := [(unitReply, frame)])
      ⟨(unitReply, frame), by simp, by simp [unitReply, Entry.Value.erase, isErrorAtom]⟩
    simp only [List.map_singleton, readResult, unitRead]
    simpa [unitReply, Entry.Value.erase, isErrorAtom] using chosen
  have started : Entry.Rel Policy.unmarked.reentry call.status call.erase Atom.undefinedType .interpret := by
    rw [shape]
    simpa only [Entry.Value.erase, List.map_cons, Entry.Value.status] using
      (Entry.Rel.expression (policy := Policy.unmarked.reentry) (status := .active)
        (head := .symbol "call-native") (tail := operands.map Entry.Value.erase) (expected := Atom.undefinedType)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
  have played := Stateful.AtomRel.tuple
    (environment := environment) (label := label) (world0 := world)
    (live := live) (scope := scope) (value := call) (expected := Atom.undefinedType)
    (frame := frame) (operator := .symbol "call-native") (arguments := operands)
    (world1 := world) (world2 := after)
    (rows := [(call, frame)]) (raw := [(unitReply, frame)]) (policy := .unmarked)
    (by simpa only [callRead] using started)
    (by rw [callRead, shape])
    (by simpa [Entry.Value.erase] using (fields "call-native" (by simp)).2.2.occurrences)
    prepared
    (by simpa only [List.append_nil] using Stateful.CallsRel.cons nativeCall Stateful.CallsRel.nil)
    priority
  have published := unmarked_publish (frame.read .unmarked call).erase (unitReply, frame) (by rfl)
  simpa only [List.map_singleton, published] using played

private theorem demand_put_evaluates_in (world : World) (label : Bool) (live : List Atom) (scope : List String)
    (fields : ∀ word ∈ ["call-native", "model-store", "put", "written-by-demand"], NativeWord world label word) :
    AtomRel environment label world live scope demandPut Atom.undefinedType Frame.empty
      [(unitReply, Frame.empty)] (Function.update world label (world label ++ [.symbol "written-by-demand"])) := by
  apply command_returns_unit label live scope Frame.empty "put" (.symbol "written-by-demand")
  · intro word member
    apply fields word
    simpa only [List.cons_append, List.nil_append] using List.mem_append_left ["written-by-demand"] member
  · exact .inl ⟨_, rfl, fields _ (by simp)⟩
  · simp [execute, Atom.unit]

/-- The operand is evaluated by the ordinary stateful source evaluator,
not supplied as an already prepared result. The host appends one row. -/
theorem demand_put_evaluates (label : Bool) (live : List Atom) (scope : List String) :
    AtomRel environment label libraryWorld live scope demandPut Atom.undefinedType Frame.empty
      [(unitReply, Frame.empty)] (demandWritten label) := by
  apply demand_put_evaluates_in libraryWorld label live scope
  intro word found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, untyped_library_symbol label _ (by decide) (by decide)⟩

/-- Only the authored let row and its two relevant type declarations are
needed for this control. The store and native write are the same as above. -/
def letWorld : World := fun _ =>
  [CollectionStdlibSource.declaration "let" CollectionStdlibSource.letType,
   CollectionStdlibSource.equation CollectionStdlibSource.letPattern CollectionStdlibSource.letBody,
   CollectionStdlibSource.declaration "unify" CollectionStdlibSource.unifyType]

def letReached (label : Bool) : World :=
  Function.update letWorld label (letWorld label ++ [Atom.unit])

def letOperand : Entry.Value := command "put" Atom.unit
def letTemplate : Entry.Value := command "take" (.var "picked")

def letPrepared : Entry.Value := .expression .active [.symbol "let", .var "picked", unitReply, letTemplate]

private def letSignature : SelectedTypePolicy :=
  ⟨CollectionStdlibSource.letType, _, _, CollectionStdlibSource.let_declared_arguments⟩

private def unifySignature : SelectedTypePolicy :=
  ⟨CollectionStdlibSource.unifyType, [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType], Atom.undefinedType, rfl⟩

private theorem no_let_annotation (subject : Atom)
    (notLet : subject ≠ .symbol "let") (notUnify : subject ≠ .symbol "unify") (label : Bool)
    (extra : List Atom) (tail : AnnotationTypesRel subject extra []) :
    AnnotationTypesRel subject (letWorld label ++ extra) [] := by
  refine .skip ?_ (.skip ?_ (.skip ?_ tail)) <;>
    intro type <;> simp [CollectionStdlibSource.declaration, CollectionStdlibSource.equation,
      CollectionStdlibSource.app, Ne.symm notLet, Ne.symm notUnify]

private theorem let_world_word (label : Bool) (word : String)
    (noEmpty : word ≠ "Empty") (noError : word ≠ "Error") (noLet : word ≠ "let") (noUnify : word ≠ "unify") :
    NativeWord letWorld label word :=
  ⟨noEmpty, noError, .symbolUndefined (by
    simpa [environment] using no_let_annotation (.symbol word) (by simpa) (by simpa) label [] .nil)⟩

private theorem let_reached_word (label : Bool) (word : String)
    (noEmpty : word ≠ "Empty") (noError : word ≠ "Error") (noLet : word ≠ "let") (noUnify : word ≠ "unify") :
    NativeWord (letReached label) label word := by
  refine ⟨noEmpty, noError, .symbolUndefined ?_⟩
  have tail : AnnotationTypesRel (.symbol word) [Atom.unit] [] :=
    .skip (by intro; simp [Atom.unit]) .nil
  have declared := no_let_annotation (.symbol word) (by simpa) (by simpa) label _ tail
  simpa [environment, letReached] using declared

/-- Use the authored let signature at the argument boundary. The operand
appends the very unit it yields; the body remains open syntax here. -/
theorem authored_let_prepares_from_reached_world (label : Bool) (live : List Atom) (scope : List String) :
    let pattern : Entry.Value := .var "picked"
    ArgumentsRel environment label letWorld live scope
      ([pattern, letOperand, letTemplate].zip letSignature.argumentTypes) Frame.empty
      [(Entry.Value.argumentPacket [pattern, unitReply, letTemplate], Frame.empty)] (letReached label)
    ∧ letReached label ≠ letWorld := by
  dsimp only
  constructor
  · refine (HEArgumentContexts.let_arguments_exact (by
      simpa only [Frame.read_empty] using
        HEArgumentContexts.unchanged_error_is_not_argument_stop (.var "picked") Frame.empty)).mpr
      ⟨[(unitReply, Frame.empty)], command_returns_unit label _ scope Frame.empty "put" Atom.unit ?_
        (.inr rfl) (by simp [execute, letReached, Atom.unit]), ?_⟩
    · intro word found
      simp only [List.mem_cons, List.not_mem_nil, or_false] at found
      rcases found with rfl | rfl | rfl <;>
        exact let_world_word label _ (by decide) (by decide) (by decide) (by decide)
    · simp [HEArgumentContexts.finishForcedThenHeld, HEArgumentContexts.finishLastArgument,
        Frame.read_empty, unitReply, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]
  · intro noWrite
    have sameRows := congrFun noWrite label
    simpa [letReached, letWorld] using congrArg List.length sameRows

private def letLocal (name : String) : String := "let#" ++ name

private def letCaptured : Entry.Value := command "take" (.var "let#pattern")
private def letInstruction : Entry.Value :=
  .expression .active [.symbol "unify", unitReply, .var "let#pattern", letCaptured, .symbol "Empty"]

private def letAliasEnv : Entry.Value.Environment := [("picked", .var "let#pattern")]
private def letDataEnv : Entry.Value.Environment := ("let#atom", unitReply) :: letAliasEnv
private def letRuleEnv : Entry.Value.Environment := ("let#template", letCaptured) :: letDataEnv

private theorem let_capture_trace :
    Entry.Value.UnifyRel Policy.unmarked.rebuilding Frame.empty.environment letPrepared
      (Entry.Value.ofAtom (renameTypeVars letLocal CollectionStdlibSource.letPattern)) letRuleEnv := by
  have aliasTrace : Entry.Value.UnifyRel .preserve [] (.var "picked") (.var "let#pattern") letAliasEnv := by
    apply Entry.Value.UnifyRel.ordinary
    simpa [letAliasEnv, Entry.Value.bind, Entry.Value.substitute, Entry.Value.resolve] using
      (Entry.Value.AppliedUnifyRel.bindLeft (policy := .preserve) (environment := [])
        (name := "picked") (right := .var "let#pattern")
        (by simp [Entry.Value.erase, TypeSubst.typeVars]))
  have operand : Entry.Value.UnifyRel .preserve letAliasEnv unitReply (.var "let#atom") letDataEnv := by
    apply Entry.Value.UnifyRel.ordinary
    simpa [letDataEnv, letAliasEnv, unitReply, Entry.Value.bind, Entry.Value.substitute, Entry.Value.resolve,
      Entry.Value.rebuildStatus, List.lookup_cons, List.lookup_nil] using
      (Entry.Value.AppliedUnifyRel.bindRight (policy := .preserve) (environment := letAliasEnv)
        (left := unitReply) (name := "let#atom") (by intro; simp [unitReply, Entry.Value.erase])
        (by simp [unitReply, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]))
  have template : Entry.Value.UnifyRel .preserve letDataEnv letTemplate (.var "let#template") letRuleEnv := by
    apply Entry.Value.UnifyRel.ordinary
    simpa [letRuleEnv, letDataEnv, letAliasEnv, letCaptured, letTemplate, unitReply, command, native,
      Entry.Value.bind, Entry.Value.substitute, Entry.Value.resolve, Entry.Value.rebuildStatus,
      Entry.Value.ofAtom, List.lookup_cons, List.lookup_nil] using
      (Entry.Value.AppliedUnifyRel.bindRight (policy := .preserve) (environment := letDataEnv)
        (left := letCaptured) (name := "let#template")
        (by intro; simp [letCaptured, command, native, Entry.Value.erase])
        (by simp [letCaptured, command, native, Entry.Value.ofAtom, Entry.Value.erase,
          TypeSubst.typeVars, TypeSubst.typeVarsList]))
  have head : Entry.Value.UnifyRel .preserve [] (.symbol "let") (.symbol "let") [] := by
    apply Entry.Value.UnifyRel.ordinary
    exact .identical rfl
  apply Entry.Value.UnifyRel.ordinary
  change Entry.Value.AppliedUnifyRel .preserve []
    (Frame.empty.read .unmarked letPrepared)
    (Frame.empty.read .unmarked (Entry.Value.ofAtom (renameTypeVars letLocal CollectionStdlibSource.letPattern)))
    letRuleEnv
  rw [Frame.read_empty, Frame.read_empty]
  simpa only [letPrepared, CollectionStdlibSource.letPattern, CollectionStdlibSource.app,
    renameTypeVars, Entry.Value.ofAtom, List.map_cons, List.map_nil, letLocal,
    show "let#" ++ "pattern" = "let#pattern" by decide,
    show "let#" ++ "atom" = "let#atom" by decide,
    show "let#" ++ "template" = "let#template" by decide] using
    (Entry.Value.AppliedUnifyRel.expression (policy := .preserve)
      (.cons head (.cons aliasTrace (.cons operand (.cons template (.nil _))))))

private theorem let_fresh :
    AlphaVariantRel [Atom.undefinedType] letPrepared.erase Frame.empty.bindings
      CollectionStdlibSource.letPattern CollectionStdlibSource.letBody
      (renameTypeVars letLocal CollectionStdlibSource.letPattern)
      (renameTypeVars letLocal CollectionStdlibSource.letBody) := by
  refine ⟨letLocal, ?_, EquationFreshening.rename_alpha _ _, EquationFreshening.rename_alpha _ _, ?_⟩
  · intro first second equal
    exact (String.append_right_inj "let#").mp equal
  · intro name appears
    have vars := appears.elim
      (fun left => List.mem_append_left (TypeSubst.typeVars CollectionStdlibSource.letBody)
        (atomOccurs_mem_typeVars left))
      (fun right => List.mem_append_right (TypeSubst.typeVars CollectionStdlibSource.letPattern)
        (atomOccurs_mem_typeVars right))
    rw [show TypeSubst.typeVars CollectionStdlibSource.letPattern ++
      TypeSubst.typeVars CollectionStdlibSource.letBody =
        ["pattern", "atom", "template", "atom", "pattern", "template"] by rfl] at vars
    have oneOf : name = "pattern" ∨ name = "atom" ∨ name = "template" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at vars
      tauto
    rcases oneOf with rfl | rfl | rfl <;>
      simp [QueryVisibleName, atomOccurs_iff_mem_typeVars, Frame.empty, Bindings.empty,
        letPrepared, letTemplate, command, native, unitReply, Entry.Value.ofAtom, Entry.Value.erase,
        letLocal, TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.undefinedType]

/-- The actual store reached by the write contains one selected let equation.
The fresh rule aliases the open caller variable instead of replacing it
with a ground guess. The match and the readout are both source-certified. -/
theorem authored_let_activates_from_reached_world (label : Bool) :
    ∃ (work : EquationWork) (frame : Frame),
      EquationFrontierRel (environment.view (letReached label) label) [Atom.undefinedType]
        letPrepared.erase Frame.empty.bindings [work] ∧
      frame.bindings = work.bindings ∧
      Entry.Value.UnifyRel Policy.unmarked.rebuilding Frame.empty.environment
        letPrepared (Entry.Value.ofAtom work.pattern) frame.environment ∧
      frame.environment = letRuleEnv ∧
      frame.read .unmarked (Entry.Value.ofAtom work.body) = letInstruction := by
  let pattern := renameTypeVars letLocal CollectionStdlibSource.letPattern
  let body := renameTypeVars letLocal CollectionStdlibSource.letBody
  obtain ⟨frame, environmentEq, annotated⟩ := ContextualUnificationFrame.frame_of_unification
    .unmarked Frame.empty letPrepared (Entry.Value.ofAtom pattern) letRuleEnv let_capture_trace
  have candidate : UnifyCandidateRel letPrepared.erase pattern Frame.empty.bindings frame.bindings :=
    by simpa only [Entry.Value.erase_ofAtom] using annotated
  obtain ⟨matched, matchRule, merged⟩ := candidate
  let work : EquationWork := ⟨1, CollectionStdlibSource.letPattern, CollectionStdlibSource.letBody,
    pattern, body, frame.bindings⟩
  have selected : EquationRowResultsRel [Atom.undefinedType] letPrepared.erase Frame.empty.bindings
      1 (CollectionStdlibSource.equation CollectionStdlibSource.letPattern CollectionStdlibSource.letBody)
        [work] := .hit _ _ _ _ _ _ _ let_fresh matchRule merged
  refine ⟨work, frame, ?_, rfl, ?_, environmentEq, ?_⟩
  · have rows : (environment.view (letReached label) label).atoms =
        letWorld label ++ [Atom.unit] := by simp [environment, letReached]
    apply EquationFrontierRel.completed (blocks := [[], [work], [], []])
    rw [rows]
    exact .cons (.irrelevant _ _ (by intro _ _; simp [CollectionStdlibSource.declaration, CollectionStdlibSource.app]))
      (.cons selected (.cons
        (.irrelevant _ _ (by intro _ _; simp [CollectionStdlibSource.declaration, CollectionStdlibSource.app]))
        (.cons (.irrelevant _ _ (by intro _ _; simp [Atom.unit])) .nil)))
  · simpa only [work, environmentEq] using let_capture_trace
  · simp [work, body, Frame.read, environmentEq, letRuleEnv, letDataEnv, letAliasEnv, letInstruction,
      CollectionStdlibSource.letBody, CollectionStdlibSource.app, renameTypeVars, letLocal, Atom.empty,
      Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.resolve, Entry.Value.rebuildStatus,
      Policy.unmarked, List.lookup_cons, List.lookup_nil]

private theorem wildcard_checks (space : Space) (expression : Atom) (frame : Frame)
    {arguments demands : List Atom}
    (known : List.Forall₂ (fun argument demand =>
      (demand = Atom.atomType ∨ demand = Atom.undefinedType) ∧
        ∃ actual, StorageTypesRel space argument [actual]) arguments demands)
    (position : Nat) :
    ApplicabilityArgumentsRel space (rawTypeLookupRel space) .unmarked expression position
      arguments demands [frame] [frame] [] := by
  induction known generalizing position with
  | nil => exact .nil
  | @cons argument demand arguments demands one _ ih =>
    obtain ⟨wild, actual, queried⟩ := one
    have checked : TypeCheckRel .unmarked demand frame actual (.inr frame) := by
      rcases wild with rfl | rfl
      · exact .accepted (.unchanged (frame.preserved_type_match .unmarked (.atomLeft _ _)))
      · exact .accepted (.unchanged (frame.preserved_type_match .unmarked (.undefinedLeft _ _)))
    have oneCheck : ArgumentChecksRel space (rawTypeLookupRel space) .unmarked expression
        argument demand position [frame] [frame] [] := by
      simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := expression) (position := position)
          queried (.cons checked .nil) .nil)
    simpa only [List.nil_append] using ApplicabilityArgumentsRel.cons oneCheck (ih (position + 1))

private theorem selected_wildcards (label : Bool) (world : World) (live : List Atom)
    (frame : Frame) (operator : String) (arguments : List Atom) (signature : SelectedTypePolicy)
    (head : StorageTypesRel (environment.view world label) (.symbol operator) [signature.functionType])
    (known : List.Forall₂ (fun argument demand =>
      (demand = Atom.atomType ∨ demand = Atom.undefinedType) ∧
        ∃ actual, StorageTypesRel (environment.view world label) argument [actual]) arguments signature.argumentTypes) :
    environment.arguments.selection (environment.view world label) environment.lookup .unmarked live []
      (.expression (.symbol operator :: arguments)) (.symbol operator) Atom.undefinedType frame
      (.selected signature [frame]) := by
  have checks : ApplicationChecksRel (environment.view world label)
      (rawTypeLookupRel (environment.view world label)) .unmarked
      (.expression (.symbol operator :: arguments)) Atom.undefinedType signature frame [frame] [] := by
    have returned : TypeCheckRel .unmarked Atom.undefinedType frame signature.returnType (.inr frame) :=
      .accepted (.unchanged (frame.preserved_type_match .unmarked (.undefinedLeft _ _)))
    simpa [checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (selected := signature) (before := frame) (operator := .symbol operator)
        (arguments := arguments) rfl (wildcard_checks _ _ frame known 1) (.cons returned .nil))
  exact ⟨_, head, .selected checks (by simp)⟩

private theorem identical_symbol_spine (names : List String) :
    MatchListAccRel equalityGroundedSemantic (names.map Atom.symbol) (names.map Atom.symbol)
      Bindings.empty Bindings.empty := by
  induction names with
  | nil => exact .nil
  | cons name _ ih =>
    exact .cons (.symSym name semanticLoopFree_empty) empty_merge ih

private theorem word_at_declared_type (label : Bool) (world : World) (live : List Atom)
    (scope : List String) (frame : Frame) (head : String) (signature : List String)
    (ordinary : head ≠ "Empty")
    (declared : StorageTypesRel (environment.view world label) (.symbol head)
      [.expression (signature.map Atom.symbol)]) :
    AtomRel environment label world live scope (.symbol head) (.expression (signature.map Atom.symbol)) frame
      [(.symbol head, frame)] world := by
  let arrow := Atom.expression (signature.map Atom.symbol)
  have entered : Entry.Rel Policy.unmarked.reentry .active (.symbol head) arrow .cast :=
    .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, ordinary]) (.symbol _)
      (by simp [arrow, Atom.atomType, Atom.symbolType, Atom.variableType])
      (Or.inl ⟨_, rfl⟩) (by intro impossible; cases impossible)
  apply scalar_cast label live frame _ arrow arrow (by simp [Frame.read, Entry.Value.substitute])
    (by simpa only [Entry.Value.erase, Entry.Value.status] using entered)
    (by simpa only [arrow, Entry.Value.erase] using declared) (scope := scope)
  exact .structural (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (.expression (identical_symbol_spine signature) semanticLoopFree_empty) (.mk (.refl _) .nil)

private theorem let_head_type (label : Bool) :
    StorageTypesRel (environment.view letWorld label) (.symbol "let") [letSignature.functionType] := by
  apply StorageTypesRel.symbolKnown ?_ (by simp)
  refine .hit (.skip ?_ (.skip ?_ .nil)) <;>
    intro type <;> simp [CollectionStdlibSource.declaration, CollectionStdlibSource.equation, CollectionStdlibSource.app]

private theorem unify_head_type (label : Bool) :
    StorageTypesRel (environment.view (letReached label) label) (.symbol "unify")
      [unifySignature.functionType] := by
  have rows : (environment.view (letReached label) label).atoms = letWorld label ++ [Atom.unit] := by
    simp [environment, letReached]
  apply StorageTypesRel.symbolKnown ?_ (by simp)
  rw [rows]
  refine .skip ?_ (.skip ?_ (.hit (.skip ?_ .nil))) <;>
    intro type <;> simp [CollectionStdlibSource.declaration, CollectionStdlibSource.equation, CollectionStdlibSource.app, Atom.unit]

private theorem reached_has_unit (label : Bool) : Atom.unit ∈ letReached label label := by
  simp [letReached]

private theorem bound_template_executes (label : Bool) (frame : Frame) (environmentEq : frame.environment = letRuleEnv) :
    ∃ result : Frame,
      CallRel environment label (letReached label) [] [] letInstruction Atom.undefinedType frame
        [(unitReply, result)] letWorld ∧ result.read .unmarked (.var "picked") = unitReply := by
  have readLocal : frame.read .unmarked (.var "let#pattern") = .var "let#pattern" := by
    simp [Frame.read, environmentEq, letRuleEnv, letDataEnv, letAliasEnv, Entry.Value.substitute,
      Entry.Value.resolve, List.lookup_cons, List.lookup_nil]
  have closed : TypeSubst.typeVars unitReply.erase = [] := by
    simp [unitReply, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]
  obtain ⟨after, retained, candidate, unified⟩ := ContextualUnificationFrame.bind_fixed
    .unmarked frame "let#pattern" unitReply readLocal closed
  have readPayload : after.read .unmarked (.var "picked") = unitReply := by
    simp [Frame.read, retained, environmentEq, letRuleEnv, letDataEnv, letAliasEnv, letCaptured, unitReply,
      command, native, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.rebuildStatus,
      Entry.Value.bind, Entry.Value.resolve, List.lookup_cons, Policy.unmarked]
  have readBody : after.read .unmarked letCaptured = command "take" Atom.unit := by
    simp [Frame.read, retained, environmentEq, letRuleEnv, letDataEnv, letAliasEnv, letCaptured, unitReply,
      command, native, Atom.unit, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.rebuildStatus,
      Entry.Value.bind, Entry.Value.resolve, Policy.unmarked]
  have taken : AtomRel environment label (letReached label) [] [] (command "take" Atom.unit)
      Atom.undefinedType after [(unitReply, after)] letWorld := by
    refine command_returns_unit label [] [] after "take" Atom.unit ?_ (.inr rfl) ?_
    · intro word found
      simp only [List.mem_cons, List.not_mem_nil, or_false] at found
      rcases found with rfl | rfl | rfl <;>
        exact let_reached_word label _ (by decide) (by decide) (by decide) (by decide)
    · rw [execute, if_neg (by decide), if_pos rfl, if_pos (reached_has_unit label)]
      congr 1
      funext other
      by_cases same : other = label
      · subst other
        simp [letReached, letWorld, Atom.unit, CollectionStdlibSource.declaration, CollectionStdlibSource.equation,
          CollectionStdlibSource.app, List.erase_cons_tail]
      · simp [letReached, Function.update_of_ne same]
  have primitive : MinimalRel environment label (letReached label) [Atom.undefinedType] [] none
      letInstruction frame [(after.read .unmarked letCaptured, after)] (letReached label) := by
    exact Stateful.MinimalRel.unifyYes (by simpa only [Entry.Value.erase] using candidate) unified
  have noHost : ¬Minimal.HostCall environment.dispatch letInstruction.erase := by
    simp [letInstruction, Entry.Value.erase, Minimal.HostCall, environment]
  have embedded : Minimal.embeddedInstruction letInstruction.erase = true := by
    simp [letInstruction, Entry.Value.erase, Minimal.embeddedInstruction]
  refine ⟨after, .embedded ?_ noHost embedded (.embedded noHost embedded primitive) ?_, readPayload⟩
  · simp [letInstruction, Entry.Value.erase, IsErrorRel]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    rw [readBody]
    exact .returned (.evaluate
      (by simp [command, native, Entry.Value.erase, Atom.notReducible])
      (by simp [command, native, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) taken)

private def letOperands : List Entry.Value := [.var "picked", letOperand, letTemplate]
def letInput : Entry.Value := .expression .active (.symbol "let" :: letOperands)

open RecursiveTasks.Contextual (WorldConfiguration Control Continuation)
open RecursiveMachine.Contextual (WorldLocalSteps WorldSteps)
open RecursiveExecution.Contextual.Stateful (function_complete local_steps_lift)

def letEntry (label : Bool) : WorldConfiguration Bool World :=
  ⟨letWorld, label, .work (.atom [] [] letInput Atom.undefinedType Frame.empty), [], []⟩

private def letRemaining : RecursiveTasks.Contextual.Task :=
  .invocations [] [] Atom.undefinedType letSignature (.symbol "let") letOperands []

private def letSaved : List Continuation :=
  [.calls [] [] Atom.undefinedType, .append letRemaining, .publish letInput.erase]

/-- The prepared application is returning to its saved call site. There
has been a world write, but there is not yet a published answer. -/
def letArgumentCut (label : Bool) : WorldConfiguration Bool World :=
  ⟨letReached label, label, .returning [(letPrepared, Frame.empty)], letSaved, []⟩

theorem let_cannot_take_before_operand (label : Bool) :
    execute label letWorld (.symbol "take") Atom.unit = ([], letWorld) := by
  simp [execute, letWorld, Atom.unit, CollectionStdlibSource.declaration, CollectionStdlibSource.equation,
    CollectionStdlibSource.app]

private theorem unmarked_application (head : String) (arguments : List Entry.Value) (ordinary : head ≠ "Error") :
    Entry.Rel Policy.unmarked.reentry .active
      (Entry.Value.expression .active (.symbol head :: arguments)).erase Atom.undefinedType .interpret := by
  simpa only [Entry.Value.erase, List.map_cons] using
    (Entry.Rel.expression (head := .symbol head) (tail := arguments.map Entry.Value.erase)
      (policy := Policy.unmarked.reentry) (status := .active) (expected := Atom.undefinedType)
      (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, ordinary]) (by decide) (Or.inr rfl))

private theorem unify_instruction_executes (label : Bool) (frame : Frame) (environmentEq : frame.environment = letRuleEnv) :
    ∃ result : Frame, AtomRel environment label (letReached label) [] [] letInstruction Atom.undefinedType
      frame [(unitReply, result)] letWorld ∧ result.read .unmarked (.var "picked") = unitReply := by
  obtain ⟨result, called, readPayload⟩ := bound_template_executes label frame environmentEq
  let operands : List Entry.Value := [unitReply, .var "let#pattern", letCaptured, .symbol "Empty"]
  have unchanged (value : Entry.Value) (member : value ∈ operands) : frame.read .unmarked value = value := by
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [Frame.read, environmentEq, letRuleEnv, letDataEnv, letAliasEnv, letCaptured, unitReply,
        command, native, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.resolve,
        List.lookup_cons, List.lookup_nil, Entry.Value.rebuildStatus, Policy.unmarked]
  have fixed : frame.read .unmarked letInstruction = letInstruction := by
    have each : operands.map (frame.read .unmarked) = operands := by
      calc
        _ = operands.map id := List.map_congr_left unchanged
        _ = _ := List.map_id _
    change frame.read .unmarked (.expression .active (.symbol "unify" :: operands)) = _
    have readChildren : (operands.map (Entry.Value.substitute .preserve (Entry.Value.resolve frame.environment))) = operands := each
    simp only [Frame.read, Policy.unmarked, Entry.Value.substitute, Entry.Value.rebuildStatus, List.map_cons,
      readChildren, letInstruction, operands]
  have recorded (subject : Atom) (notLet : subject ≠ .symbol "let") (notUnify : subject ≠ .symbol "unify") :
      AnnotationTypesRel subject (environment.view (letReached label) label).atoms [] := by
    have rows := no_let_annotation subject notLet notUnify label [Atom.unit]
      (.skip (by intro; simp [Atom.unit]) .nil)
    simpa [environment, letReached] using rows
  have known : List.Forall₂ (fun operand demand =>
      (demand = Atom.atomType ∨ demand = Atom.undefinedType) ∧
      ∃ actual, StorageTypesRel (environment.view (letReached label) label) operand [actual])
      (operands.map Entry.Value.erase) unifySignature.argumentTypes := by
    simp only [operands, unifySignature, unitReply, Entry.Value.erase, List.map_cons, List.map_nil]
    refine .cons ⟨Or.inl rfl, _, .unit _⟩ (.cons ⟨Or.inl rfl, _, .variable _ _⟩
      (.cons ⟨Or.inl rfl, Atom.undefinedType, ?_⟩ (.cons ⟨Or.inl rfl, Atom.undefinedType, ?_⟩ .nil)))
    · have annotations := recorded letCaptured.erase
        (by simp [letCaptured, command, native, Entry.Value.erase])
        (by simp [letCaptured, command, native, Entry.Value.erase])
      simp only [letCaptured, command, native, Entry.Value.erase, List.map_cons, List.map_nil] at annotations ⊢
      exact .expressionUndefined annotations
    · exact .symbolUndefined (recorded _ (by decide) (by decide))
  have selected := selected_wildcards label (letReached label) [] frame "unify"
    (operands.map Entry.Value.erase) unifySignature (unify_head_type label) known
  have held : ArgumentsRel environment label (letReached label) [.symbol "unify", Atom.undefinedType] []
      (operands.zip unifySignature.argumentTypes) frame [(Entry.Value.argumentPacket operands, frame)]
      (letReached label) := by
    have delivered := DeliveredArgumentPackets.source environment .unmarked label (letReached label) []
      frame (operands.map fun value => (value, Atom.atomType))
      (by
        intro request present
        obtain ⟨value, member, rfl⟩ := List.mem_map.mp present
        exact unchanged value member)
      (by
        intro request present
        obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
        exact Entry.atom_demand _ _ _)
      [.symbol "unify", Atom.undefinedType]
    simpa only [operands, unifySignature, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left] using delivered
  have function : FunctionRel environment label (letReached label) [Atom.undefinedType] [] Atom.undefinedType
      unifySignature (.symbol "unify") operands frame [(letInstruction, frame)] (letReached label) := by
    have evaluated := HEArgumentContexts.function_of_one_operator (head := .symbol "unify")
      (signature := unifySignature) (frame := frame) (expected := Atom.undefinedType)
      (live := [Atom.undefinedType]) (operator := .symbol "unify")
      (arguments := operands) rfl
      (word_at_declared_type label (letReached label) _ _ frame "unify"
        ["->", "Atom", "Atom", "Atom", "Atom", "%Undefined%"] (by decide) (unify_head_type label))
      (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (by simpa only [Entry.Value.erase] using held)
    simpa only [List.map_singleton, functionAssemble, Entry.Value.unpackArguments_packet, operands, letInstruction] using evaluated
  have complete := HEArgumentContexts.completed_typed_one
    (policy := .unmarked) (caller := frame) (signature := unifySignature)
    (original := letInstruction) (readiness := .active) (operands := operands)
    (operator := .symbol "unify") (expected := Atom.undefinedType)
    (by
      rw [fixed]
      simpa only [letInstruction, operands, Entry.Value.status] using unmarked_application "unify" operands (by decide))
    (by rw [fixed]; rfl)
    (by
      rw [fixed]
      simpa only [letInstruction, Entry.Value.erase, List.map_cons, List.map_nil, operands] using selected)
    function called
  refine ⟨result, ?_, readPayload⟩
  have readUnit : result.read .unmarked unitReply = unitReply := by
    simp [Frame.read, unitReply, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked]
  simpa only [readResult, readUnit,
    unmarked_publish (frame.read .unmarked letInstruction).erase (unitReply, result) rfl] using complete

/-- The authored let row forces its operand, binds the unit through the
ordinary typed unify, then takes that unit from the reached world.
Both writes admit before the one returned value; the public variable
still reads as that unit. -/
theorem authored_effectful_let (label : Bool) :
    ∃ result : Frame,
      WorldSteps environment.view environment.services environment.dispatch environment.lookup .unmarked
        (letEntry label) (letArgumentCut label) (admission := environment.arguments) ∧
      (letArgumentCut label).SourceRel environment .unmarked [(unitReply, result)] letWorld ∧
      result.read .unmarked (.var "picked") = unitReply := by
  obtain ⟨work, frame, frontier, binds, trace, environmentEq, readCode⟩ :=
    authored_let_activates_from_reached_world label
  obtain ⟨result, ranBody, readPayload⟩ := unify_instruction_executes label frame environmentEq
  have called : CallRel environment label (letReached label) [] [] letPrepared Atom.undefinedType Frame.empty
      [(unitReply, result)] letWorld := by
    apply Stateful.CallRel.equations (works := [work])
    · simp [letPrepared, Entry.Value.erase, IsErrorRel]
    · simp [letPrepared, Entry.Value.erase, NonGroundedCallRel, Minimal.HostCall, environment, Minimal.embeddedInstruction]
    · exact frontier
    · simp
    · have produced : BoundaryRel environment label (letReached label) [Atom.undefinedType] []
          (some letPrepared.erase) .producer (frame.read .unmarked (Entry.Value.ofAtom work.body)) frame
          [(letInstruction, frame)] (letReached label) := by
        rw [readCode]
        exact .producerRaw (by simp [FunctionPending, Minimal.IsFunction, letInstruction, Entry.Value.erase])
      have returned : BoundaryRel environment label (letReached label) [] [] none (.returned letPrepared Atom.undefinedType)
          letInstruction frame [(unitReply, result)] letWorld :=
        .returned (.evaluate
          (by simp [letInstruction, Entry.Value.erase, Atom.notReducible])
          (by simp [letInstruction, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) ranBody)
      simpa only [List.append_nil] using Stateful.EquationBodiesRel.cons binds trace produced
        (Stateful.BoundaryBatchRel.single_iff.mpr returned) Stateful.EquationBodiesRel.nil
  let arguments := letOperands
  have noAnnotation (name : String) (atom : Atom) :
      StorageTypesRel (environment.view letWorld label) (command name atom).erase [Atom.undefinedType] := by
    have all := no_let_annotation (command name atom).erase
      (by simp [command, native, Entry.Value.erase]) (by simp [command, native, Entry.Value.erase]) label [] .nil
    simp only [command, native, Entry.Value.erase, List.map_cons, List.map_nil]
    apply StorageTypesRel.expressionUndefined
    simpa [environment, command, native, Entry.Value.erase] using all
  have known : List.Forall₂ (fun operand demand =>
      (demand = Atom.atomType ∨ demand = Atom.undefinedType) ∧
      ∃ actual, StorageTypesRel (environment.view letWorld label) operand [actual])
      (arguments.map Entry.Value.erase) letSignature.argumentTypes := by
    simp only [arguments, letOperands, letSignature, List.map_cons, List.map_nil]
    exact .cons ⟨Or.inl rfl, _, by simpa only [Entry.Value.erase] using StorageTypesRel.variable _ "picked"⟩
      (.cons ⟨Or.inr rfl, _, noAnnotation "put" Atom.unit⟩
      (.cons ⟨Or.inl rfl, _, noAnnotation "take" (.var "picked")⟩ .nil))
  have selected := selected_wildcards label letWorld [] Frame.empty "let"
    (arguments.map Entry.Value.erase) letSignature (let_head_type label) known
  have function : FunctionRel environment label letWorld [Atom.undefinedType] [] Atom.undefinedType
      letSignature (.symbol "let") arguments Frame.empty [(letPrepared, Frame.empty)] (letReached label) := by
    have entered := HEArgumentContexts.function_of_one_operator (head := .symbol "let")
      (signature := letSignature) (frame := Frame.empty) (expected := Atom.undefinedType)
      (live := [Atom.undefinedType]) (operator := .symbol "let")
      (arguments := arguments) rfl
      (word_at_declared_type label letWorld _ _ Frame.empty "let"
        ["->", "Atom", "%Undefined%", "Atom", "%Undefined%"] (by decide) (let_head_type label))
      (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (by simpa only [arguments, letOperands, Entry.Value.erase] using
        (authored_let_prepares_from_reached_world label [.symbol "let", Atom.undefinedType] []).1)
    simpa only [List.map_singleton, functionAssemble, Entry.Value.unpackArguments_packet, letPrepared] using entered
  have enters : WorldLocalSteps environment .unmarked label letWorld
      ((letEntry label).control, []) letWorld
      (.work (.invocations [] [] Atom.undefinedType letSignature (.symbol "let") letOperands [Frame.empty]),
        [.publish letInput.erase]) := by
    apply Relation.ReflTransGen.single
    have entered : Entry.Rel Policy.unmarked.reentry (Frame.empty.read .unmarked letInput).status
        (Frame.empty.read .unmarked letInput).erase Atom.undefinedType .interpret := by
      simpa only [Frame.read_empty, letInput, Entry.Value.status] using
        unmarked_application "let" arguments (by decide)
    have shape : Frame.empty.read .unmarked letInput = .expression .active (.symbol "let" :: letOperands) := by
      rw [Frame.read_empty]; rfl
    have chosen : environment.arguments.selection (environment.view letWorld label) environment.lookup
        .unmarked [] [] (Frame.empty.read .unmarked letInput).erase (Entry.Value.symbol "let").erase Atom.undefinedType
        Frame.empty (.selected letSignature [Frame.empty]) := by
      simpa only [Frame.read_empty, letInput, Entry.Value.erase, List.map_cons] using selected
    exact .core (by constructor) rfl
      (by simpa only [Frame.read_empty] using
        RecursiveMachine.Contextual.LocalStepWith.atomFunction (stack := []) entered shape chosen)
      (by constructor)
  have selects : WorldLocalSteps environment .unmarked label letWorld
      (.work (.invocations [] [] Atom.undefinedType letSignature (.symbol "let") letOperands [Frame.empty]),
        [.publish letInput.erase]) letWorld
      (.work (.function [Atom.undefinedType] [] Atom.undefinedType letSignature (.symbol "let") letOperands Frame.empty),
        letSaved) :=
    .single (.core (by constructor) rfl .invocationsCons (by constructor))
  have preparedRun := local_steps_lift (enters.trans (selects.trans (function_complete function letSaved))) []
  have replies : CallsRel environment label (letReached label) [] [] Atom.undefinedType [(letPrepared, Frame.empty)]
      [(unitReply, result)] letWorld := by
    simpa only [List.append_nil] using Stateful.CallsRel.cons called Stateful.CallsRel.nil
  have readUnit : result.read .unmarked unitReply = unitReply := by
    simp [Frame.read, unitReply, Entry.Value.substitute, Entry.Value.rebuildStatus, Policy.unmarked]
  have publish : Continuation.WorldApplies environment .unmarked label letWorld (.publish letInput.erase)
      [(unitReply, result)] [(unitReply, result)] letWorld := by
    have good : isErrorAtom unitReply.erase = false := by simp [unitReply, Entry.Value.erase, isErrorAtom]
    have raw : [(unitReply, result)].map (readResult .unmarked) = [(unitReply, result)] := by
      simp only [List.map_singleton, readResult, readUnit]
    have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
        ([(unitReply, result)].map (readResult .unmarked)) [(unitReply, result)] := by
      rw [raw]
      simpa only [List.filter_cons, good, Bool.not_false, if_true, List.filter_nil] using
        (SuccessPriorityRel.successes (isError := fun row : Result => isErrorAtom row.1.erase)
          (raw := [(unitReply, result)]) ⟨_, List.mem_singleton_self _, good⟩)
    simpa only [List.map_singleton, unmarked_publish letInput.erase (unitReply, result) rfl] using
      (Continuation.WorldApplies.publish (environment := environment) (label := label)
        (world := letWorld) (original := letInput.erase) priority)
  have rest : letRemaining.WorldSourceRel environment .unmarked label letWorld [] letWorld :=
    Stateful.InvocationsRel.nil
  have resumed : (letArgumentCut label).SourceRel environment .unmarked [(unitReply, result)] letWorld := by
    unfold WorldConfiguration.SourceRel letArgumentCut
    dsimp only
    refine ⟨_, _, _, .returning _, .cons (.calls replies) ?_, rfl⟩
    simpa only [List.append_nil] using
      (RecursiveTasks.Contextual.WorldStackRel.cons (Continuation.WorldApplies.append
          (before := [(unitReply, result)]) rest)
        (RecursiveTasks.Contextual.WorldStackRel.cons publish (.nil _)))
  exact ⟨result, preparedRun, resumed, readPayload⟩

/-- The same closed operand crosses both actual typed preparation
paths. Only the strict domain runs the native store update. -/
theorem caller_demand_prepares_different_worlds (label : Bool) (live : List Atom) :
    FunctionRel environment label libraryWorld live [] Atom.undefinedType (librarySignature false)
      (.symbol "quote") [demandPut] Frame.empty
      [(.expression .active [.symbol "quote", demandPut], Frame.empty)] libraryWorld ∧
    FunctionRel environment label libraryWorld live [] Atom.undefinedType (librarySignature true)
      (.symbol "unquote") [demandPut] Frame.empty
      [(.expression .active [.symbol "unquote", unitReply], Frame.empty)] (demandWritten label) := by
  constructor
  · exact library_prepares false label live
      (HEArgumentContexts.unchanged_atom_argument environment label libraryWorld
        (.symbol "quote" :: live) [] .unmarked demandPut)
  · apply library_prepares true label live
    apply HEArgumentContexts.singleton_arguments_exact.mpr
    refine ⟨[(unitReply, Frame.empty)], demand_put_evaluates label _ [], ?_⟩
    have noStop : ¬ArgumentStopped demandPut (unitReply, Frame.empty) := by
      simp [ArgumentStopped, unitReply, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    simp [HEArgumentContexts.finishLastArgument_of_ordinary noStop]

def demandInput (release : Bool) : Entry.Value :=
  .expression .active [.symbol (libraryName release), demandPut]

def demandOutcome (release : Bool) : Entry.Value :=
  if release then .expression .active [.symbol "unquote", unitReply] else demandInput false

def reachedByDemand (release label : Bool) : World :=
  if release then demandWritten label else libraryWorld

private def releaseUnit : Atom := .expression [.symbol "unquote", Atom.unit]

private theorem unquote_unit_misses (release : Bool) (position : Nat) :
    EquationRowResultsRel [Atom.undefinedType] releaseUnit Frame.empty.bindings position (row release) [] := by
  have fresh : ¬ QueryVisibleName [Atom.undefinedType] releaseUnit Frame.empty.bindings "atom" := by
    simp [QueryVisibleName, releaseUnit, Atom.unit, Frame.empty, Bindings.empty, Atom.undefinedType,
      atomOccurs_iff_mem_typeVars, TypeSubst.typeVars, TypeSubst.typeVarsList]
  apply EquationRowResultsRel.miss position _ _ _ _
    (fresh_rule release [Atom.undefinedType] releaseUnit Frame.empty.bindings "atom" fresh)
  intro pattern body renamed candidate output viable
  obtain ⟨renamer, _, shaped, _, _⟩ := renamed
  have matching := viable.1
  rw [EquationFreshening.alphaRename_eq shaped] at matching
  cases release
  · have wrongHead : MatchRel equalityGroundedSemantic releaseUnit (quote (.var (renamer "atom"))) candidate := by
      simpa [form, quote, renameTypeVars] using matching
    cases wrongHead with
    | expression items _ =>
      cases items with
      | cons head _ _ => exact symbol_mismatch_not_match (by decide) _ head
  · have wrongArgument : MatchRel equalityGroundedSemantic releaseUnit
      (unquote (.var (renamer "atom"))) candidate := by
      simpa [form, quote, unquote, renameTypeVars] using matching
    cases wrongArgument with
    | expression items _ =>
      cases items with
      | cons _ _ arguments =>
        cases arguments with
        | cons argument _ _ =>
          cases argument with
          | expression contents _ => cases contents

private theorem no_rule_after_write (label : Bool) :
    CallRel environment label (demandWritten label) [] [] (demandOutcome true) Atom.undefinedType
      Frame.empty [(demandOutcome true, Frame.empty)] (demandWritten label) := by
  have erased : (demandOutcome true).erase = releaseUnit := by
    simp [demandOutcome, unitReply, releaseUnit, Entry.Value.erase, Atom.unit]
  apply Stateful.CallRel.absent
  · rw [erased]
    simp [releaseUnit, IsErrorRel]
  · rw [erased]
    simp [releaseUnit, NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction, environment]
  · rw [erased]
    have initial : EquationFrontierRel (environment.view libraryWorld label) [Atom.undefinedType]
        releaseUnit Frame.empty.bindings [] := by
      apply EquationFrontierRel.completed (blocks := [[], [], [], []])
      exact .cons (.irrelevant 0 _ (declaration_irrelevant false))
        (.cons (unquote_unit_misses false 1)
          (.cons (.irrelevant 2 _ (declaration_irrelevant true)) (.cons (unquote_unit_misses true 3) .nil)))
    have current := EquationFrontierRel.append_rejected (environment.view libraryWorld label)
      [Atom.undefinedType] releaseUnit Frame.empty.bindings [] [.symbol "written-by-demand"] initial
      (by intro datum member position
          obtain rfl := List.mem_singleton.mp member
          exact .irrelevant position _ (fun _ _ incompatible => by cases incompatible))
    simpa [environment, demandWritten, Space.ofList] using current

/-- Starting from the actual authored outer syntax, the held path
publishes the operand as part of the wrapper without touching the store.
The strict path performs the operand write before looking for its
unquote rule in the reached world. Its unit is not a quoted argument. -/
theorem authored_caller_demand (release label : Bool) :
    ∃ output : Frame,
      AtomRel environment label libraryWorld [] [] (demandInput release) Atom.undefinedType
        Frame.empty [(demandOutcome release, output)] (reachedByDemand release label) := by
  have noAnnotation : StorageTypesRel (environment.view libraryWorld label) demandPut.erase
      [Atom.undefinedType] := by
    simpa [demandPut, command, native, Entry.Value.ofAtom, Entry.Value.erase] using
      unannotated_application label (.symbol "call-native")
        [.symbol "model-store", .symbol "put", .symbol "written-by-demand"]
  cases release with
  | false =>
      have closed : ∀ name, ¬AtomOccurs demandPut.erase name := by
        intro name
        rw [atomOccurs_iff_mem_typeVars]
        simp [demandPut, command, native, Entry.Value.ofAtom, Entry.Value.erase,
          TypeSubst.typeVars, TypeSubst.typeVarsList]
      obtain ⟨output, _, called⟩ := prepared_quote label demandPut.erase
        (by simp [demandPut, command, native, Entry.Value.erase, isVariableB]) closed
      refine ⟨output, ?_⟩
      apply library_completes false label [] (operand := demandPut) (prepared := demandPut)
        (middleFrame := Frame.empty) (middle := libraryWorld) (actual := Atom.undefinedType)
      · simp only [Frame.read_empty, demandInput]
      · exact noAnnotation
      · exact (caller_demand_prepares_different_worlds label
          [invocationReturnType (librarySignature false)]).1
      · simpa [reachedByDemand, demandOutcome, demandInput, demandPut, command, native, quote,
          Entry.Value.ofAtom, Entry.Value.erase, libraryName, invocationReturnType,
          librarySignature, argumentDemand, demandName, Atom.atomType, Atom.expressionType]
          using called
      · apply Frame.read_variable_free
        intro name
        rw [atomOccurs_iff_mem_typeVars]
        simp [demandInput, demandOutcome, libraryName, demandPut, command, native, Entry.Value.ofAtom,
          Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]
      · simp [demandInput, demandOutcome, Entry.Value.status]
  | true =>
      refine ⟨Frame.empty, ?_⟩
      apply library_completes true label [] (operand := demandPut) (prepared := unitReply)
        (middleFrame := Frame.empty) (middle := demandWritten label) (actual := Atom.undefinedType)
      · simp only [Frame.read_empty, demandInput]
      · exact noAnnotation
      · exact (caller_demand_prepares_different_worlds label
          [invocationReturnType (librarySignature true)]).2
      · simpa [reachedByDemand, demandOutcome, libraryName, invocationReturnType, librarySignature,
          argumentDemand, demandName, Atom.undefinedType, Atom.expressionType] using no_rule_after_write label
      · exact Frame.read_empty _ _
      · simp [demandOutcome, Entry.Value.status]

end Quotation

namespace ExpressionSize

open Spec.Type Spec.Match.Merge Spec.Type.RuntimeRefinement Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.ContextualTransform.HEArgumentContexts

def operator : Atom := .symbol "size-atom"
def size (argument : Atom) : Atom := .expression [operator, argument]
def counted (n : Nat) : Entry.Value := .grounded (.int n)

private def numberType : Atom := .symbol "Number"

private def signature : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", Atom.expressionType, numberType], [Atom.expressionType], numberType, rfl⟩

private def declaration : Atom := .expression [.symbol ":", operator, signature.functionType]

private def dispatch : Spec.Eval.GroundedDispatch where
  executable head := head = operator
  outcome := fun _ _ _ => False
  valueProvenance := fun _ _ => .completed
  bindingMode := fun _ _ => .raw

private def report (items : List Atom) : GroundedResult Entry.Value :=
  .ok [(counted items.length, Bindings.empty)]

/-- The registered size primitive inspects the children of its prepared
expression. It does not receive a continuation or call an evaluator. -/
def environment : WorldEnvironment Bool World where
  view world label := Space.ofList (declaration :: world label)
  services := { HEWorldControls.services with
    groundedCall := fun _ before call outcome after =>
      ∃ items, call.erase = size (.expression items) ∧ outcome = report items ∧ after = before }
  dispatch := dispatch
  lookup := rawLookup

/-- These data fixtures supply no more type declarations. The type view
still contains the reached rows of the selected space. -/
def DataOnly (world : World) (label : Bool) : Prop :=
  ∀ row ∈ world label, ∀ subject type : Atom, row ≠ .expression [.symbol ":", subject, type]

private theorem no_data_annotations (subject : Atom) (rows : List Atom)
    (data : ∀ row ∈ rows, ∀ subject type : Atom, row ≠ .expression [.symbol ":", subject, type]) :
    AnnotationTypesRel subject rows [] := by
  induction rows with
  | nil => exact .nil
  | cons row rest ih =>
    exact .skip (data row List.mem_cons_self subject)
      (ih (fun x live => data x (List.mem_cons_of_mem row live)))

private theorem head_type (world : World) (label : Bool) (data : DataOnly world label) :
    StorageTypesRel (environment.view world label) operator [signature.functionType] := by
  exact .symbolKnown (.hit (no_data_annotations operator (world label) data)) (by simp)

private theorem operand_type (world : World) (label : Bool) (items : List Atom) (data : DataOnly world label) :
    StorageTypesRel (environment.view world label) (.expression items) [Atom.undefinedType] := by
  cases items with
  | nil => exact .unit _
  | cons head tail =>
    apply StorageTypesRel.expressionUndefined
    refine .skip ?_ (no_data_annotations (.expression (head :: tail)) (world label) data)
    intro type
    simp [declaration, operator]

private theorem selection (world : World) (label : Bool) (live : List Atom) (items : List Atom)
    (data : DataOnly world label) :
    InvocationSelectionRel (environment.view world label) environment.lookup .unmarked live []
      (size (.expression items)) operator Atom.undefinedType Frame.empty
      (.selected signature [Frame.empty]) := by
  have arg : TypeCheckRel .unmarked Atom.expressionType Frame.empty Atom.undefinedType (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match .unmarked (.undefinedRight _ _)))
  have argument : ArgumentChecksRel (environment.view world label)
      (rawTypeLookupRel (environment.view world label)) .unmarked
      (size (.expression items)) (.expression items) Atom.expressionType 1 [Frame.empty] [Frame.empty] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := size (.expression items)) (position := 1)
        (operand_type world label items data) (.cons arg .nil) .nil)
  have result : TypeCheckRel .unmarked Atom.undefinedType Frame.empty numberType (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match .unmarked (.undefinedLeft _ _)))
  have checked : ApplicationChecksRel (environment.view world label)
      (rawTypeLookupRel (environment.view world label)) .unmarked
      (size (.expression items)) Atom.undefinedType signature Frame.empty [Frame.empty] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (selected := signature) (before := Frame.empty)
        (show size (.expression items) = .expression [operator, .expression items] by rfl)
        (.cons argument .nil) (.cons result .nil))
  exact ⟨_, head_type world label data, .selected checked (by simp)⟩

private theorem head_evaluates (world : World) (label : Bool) (live : List Atom) (scope : List String)
    (data : DataOnly world label) :
    AtomRel environment label world live scope (.symbol "size-atom") signature.functionType Frame.empty
      [(.symbol "size-atom", Frame.empty)] world := by
  apply Quotation.scalar_cast label live Frame.empty (.symbol "size-atom") _ signature.functionType
    (Frame.read_empty _ _) (scope := scope)
  · have entry : Entry.Rel Policy.unmarked.reentry .active (.symbol "size-atom") signature.functionType .cast :=
      .cast (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (.symbol _) (by decide) (Or.inl ⟨_, rfl⟩) (by intro impossible; cases impossible)
    simpa only [Entry.Value.status, Entry.Value.erase] using entry
  · simpa only [operator, Entry.Value.erase] using head_type world label data
  · refine TypeMatchRel.structural (matched := Bindings.empty)
      (by decide) (by decide) (by decide) (by decide) ?_ Quotation.empty_merge
    exact .expression (.cons (.symSym "->" semanticLoopFree_empty) Quotation.empty_merge
      (.cons (.symSym "Expression" semanticLoopFree_empty) Quotation.empty_merge
        (.cons (.symSym "Number" semanticLoopFree_empty) Quotation.empty_merge .nil))) semanticLoopFree_empty

private theorem reply_type (world : World) (label : Bool) (live : List Atom)
    (original : Entry.Value) (n : Nat) :
    Stateful.BoundaryRel environment label world live [] none
      (.native original (some numberType) .completed) (counted n) Frame.empty [(counted n, Frame.empty)] world := by
  apply Stateful.BoundaryRel.nativeCompletedReturn
  apply NativeCompletedReturnRel.cast (raw := [((counted n).erase, Bindings.empty)])
  · simp only [counted, Entry.Value.erase]
    intro holds
    rcases holds with stopped | undefined | atom | ⟨_, inType, same | impossible⟩
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty] at stopped
    · exact (by decide : numberType ≠ Atom.undefinedType) undefined
    · exact (by decide : numberType ≠ Atom.atomType) atom
    · cases inType
      exact (by decide : numberType ≠ Atom.groundedType) same
    · cases inType
      exact (by decide : Atom.groundedType ≠ Atom.variableType) impossible
  · have types : StorageTypesRel (environment.view world label) (counted n).erase [numberType] := by
      simp only [counted, Entry.Value.erase, numberType]
      exact .groundedKnown (.int n) (by decide)
    have matched : TypeMatchRel numberType numberType Bindings.empty Bindings.empty :=
      .structural (by decide) (by decide) (by decide) (by decide)
        (.symSym "Number" semanticLoopFree_empty) Quotation.empty_merge
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) types rfl (by simp)
      (Frame.empty.preserved_type_match .unmarked matched)
  · exact .cons ⟨rfl, .same Frame.empty, by simp⟩ .nil

theorem prepared_size_counts (world : World) (label : Bool) (live : List Atom) (items : List Atom) :
    CallRel environment label world live [] (Entry.Value.ofAtom (size (.expression items))) numberType
      Frame.empty [(counted items.length, Frame.empty)] world := by
  let original := Entry.Value.ofAtom (size (.expression items))
  have whole : original.erase = .expression [operator, .expression items] := by
    simp [original, size]
  have supplied : environment.services.groundedAt label world live [] Frame.empty original (report items) world :=
    ⟨items, whole, rfl, rfl⟩
  have rows : NativeRowsRel .unmarked dispatch operator [.expression items] Frame.empty
      [(counted items.length, Bindings.empty)] [(counted items.length, Frame.empty)] := by
    simpa [nativeValue, dispatch, counted] using
      (NativeRowsRel.cons (head := (counted items.length, Bindings.empty))
        (Frame.NativeRenewRel.empty .unmarked Frame.empty)
        (dispatch := dispatch) (operator := operator) (arguments := [.expression items]) .nil)
  exact .groundedResume whole rfl (by rw [whole]; simp [operator, IsErrorRel])
    supplied (.success rows)
    (Stateful.BoundaryBatchRel.single_iff.mpr (reply_type world label live original items.length))

/-- From the authored outer application, the declared Expression slot
delivers the operand, the host counts its syntax and the Number return
gate publishes that count. No child or changed world is needed. -/
theorem expression_size_counts (world : World) (label : Bool) (items : List Atom)
    (data : DataOnly world label) :
    AtomRel environment label world [] [] (Entry.Value.ofAtom (size (.expression items))) Atom.undefinedType
      Frame.empty [(counted items.length, Frame.empty)] world := by
  let operand := Entry.Value.ofAtom (.expression items)
  let original := Entry.Value.ofAtom (size (.expression items))
  have shape : Frame.empty.read .unmarked original = .expression .active [.symbol "size-atom", operand] := by
    simp only [Frame.read_empty, original, size, operator, operand, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have entered : Entry.Rel .reinterpret .active (size (.expression items)) Atom.undefinedType .interpret :=
    .expression (by simp [operator, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl)
  have arguments : ArgumentsRel environment label world
      [.symbol "size-atom", numberType] [] [(operand, Atom.expressionType)] Frame.empty
      [(Entry.Value.argumentPacket [operand], Frame.empty)] world := by
    apply (singleton_expression_exact (items := items) (by simp [Frame.read_empty, operand])).mpr
    rw [Frame.read_empty, finishLastArgument_of_ordinary (unchanged_error_is_not_argument_stop _ _)]
    exact ⟨rfl, rfl⟩
  have prepared : FunctionRel environment label world [numberType] [] Atom.undefinedType signature
      (.symbol "size-atom") [operand] Frame.empty [(original, Frame.empty)] world := by
    have built := function_of_one_operator (arguments := [operand]) (signature := signature)
      (live := [numberType]) (scope := []) (expected := Atom.undefinedType)
      (head := .symbol "size-atom") rfl (head_evaluates world label _ _ data)
      (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (by simpa [Entry.Value.erase, signature] using arguments)
    simpa [original, size, operator, operand, Entry.Value.ofAtom, functionAssemble] using built
  have active : original.status = .active := by
    rw [← Frame.read_empty .unmarked original, shape, Entry.Value.status]
  have checked := completed_typed_one (environment := environment) (label := label)
    (policy := .unmarked) (original := original) (expected := Atom.undefinedType)
    (before := world) (signature := signature) (live := []) (scope := [])
    (by rw [Frame.read_empty, active]
        simpa only [original, Entry.Value.erase_ofAtom, Policy.unmarked] using entered)
    shape
    (by simpa [Frame.read_empty, original, Entry.Value.erase, operator, environment, ArgumentService.selection]
      using selection world label [] items data)
    prepared (prepared_size_counts world label [] items)
  simpa [readResult, Frame.read_empty, publishResult, Entry.Value.publish, Entry.Value.withStatus, counted] using checked

end ExpressionSize

namespace DriverControls

open RecursiveTasks.Contextual (Task WorldConfiguration)
open RecursiveMachine.Contextual (WorldStep WorldSteps WorldStepWith WorldLocalStepWith)
open RecursiveExecution.Contextual.Stateful.Protocol
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Concrete native model-store operations at the execution-entry boundary. No
source answer is supplied to the driver as an opaque input. -/
private def initialWorld : World :=
  fun label => if label then [failure (.symbol "first")] else [.symbol "outside"]

private def writtenWorld : World :=
  Function.update initialWorld true [failure (.symbol "first"), .symbol "inserted"]

private def writeSilently : Task :=
  .minimal [] [] none (command "silent-put" (.symbol "inserted")) Frame.empty

private def inspect : Task :=
  .minimal [] [] none (command "read" (.symbol "ignored")) Frame.empty

private def lateWrite : Task :=
  .minimal [] [] none (command "put" (.symbol "too-late")) Frame.empty

private def request (world : World) (task : Task) : WorldConfiguration Bool World :=
  ⟨world, true, .work task, [], []⟩

private def badRow : Result := (Entry.Value.ofAtom (failure (.symbol "first")), Frame.empty)
private def laterRow : Result := (.symbol "inserted", Frame.empty)
private def batch : List Result := [badRow, laterRow]
private def midBatch : WorldConfiguration Bool World :=
  ⟨writtenWorld, true, .returning [laterRow], [], [badRow]⟩

private theorem silent_source :
    (request initialWorld writeSilently).SourceRel environment .unmarked [] writtenWorld := by
  refine ⟨[], [], writtenWorld, .work ?_, .nil _, rfl⟩
  exact (command_exact true initialWorld "silent-put" (.symbol "inserted") [] [] none .unmarked Frame.empty
    [] writtenWorld).mpr (by simp [execute, writtenWorld, initialWorld])

private theorem get_first_internal :
    WorldSteps (admission := environment.arguments) environment.view environment.services
      environment.dispatch environment.lookup .unmarked (request writtenWorld inspect) midBatch := by
  have read : WorldStep (admission := environment.arguments) environment.view environment.services
      environment.dispatch environment.lookup .unmarked (request writtenWorld inspect)
      ⟨writtenWorld, true, .returning batch, [], []⟩ := by
    apply WorldStepWith.internal
    exact WorldLocalStepWith.native (by
      simp [environment, services, execute, writtenWorld, batch, badRow, laterRow,
        Entry.Value.erase, Entry.Value.ofAtom])
  exact (Relation.ReflTransGen.single read).tail WorldStepWith.publish

/-- An answerless write followed by EOF still contributes one empty report. -/
theorem empty_report_before_eof :
    ∃ fuel, Derivation (FileCommands.Step environment .unmarked) fuel
      (FileCommands.start initialWorld true [writeSilently]) [[]]
      (.finished ⟨writtenWorld, true, [], .eof⟩) := by
  apply FileCommands.complete_trace_iff.mp
  refine ⟨rfl, Or.inl ⟨rfl, rfl, ?_⟩⟩
  exact Mettapedia.Machines.OrderedProtocol.Completion.OrderedStateFlatMapRel.singleton
    (show FileCommands.CleanCommand environment .unmarked true writeSilently initialWorld [[]] writtenWorld
      from ⟨[], rfl, silent_source, rfl⟩)

/-- Even after the evaluator has internally published an error occurrence, the
driver has not published a batch or entered the next command. The next
answer remains pending in the same configuration. -/
theorem pauses_inside_error_batch :
    ∃ fuel, Derivation (FileCommands.Step environment .unmarked) fuel
      (.active (request writtenWorld inspect) [lateWrite]) []
      (.exhausted (.active midBatch [lateWrite])) :=
  FileCommands.retain_prefix [lateWrite] get_first_internal

/-- The write's empty report does not mean exhaustion. The read sees
the written row and publishes its *whole* batch before the file stops.
The reached world has the first write and not the unvisited late write. -/
theorem empty_then_error_preserves_file_cut :
    ∃ fuel,
      Derivation (FileCommands.Step environment .unmarked) fuel
        (FileCommands.start initialWorld true [writeSilently, inspect, lateWrite]) [[], batch]
        (.finished ⟨writtenWorld, true, [lateWrite], .errorBatch⟩) ∧
      writtenWorld true = [failure (.symbol "first"), .symbol "inserted"] ∧
      writtenWorld false = [.symbol "outside"] := by
  obtain ⟨first, wrote⟩ := FileCommands.report_source silent_source [inspect, lateWrite]
  obtain ⟨beforeCut, readPart⟩ := pauses_inside_error_batch
  have resumed : midBatch.SourceRel environment .unmarked batch writtenWorld :=
    ⟨[laterRow], [laterRow], writtenWorld, .returning _, .nil _, rfl⟩
  obtain ⟨afterCut, reported⟩ := FileCommands.report_source resumed [lateWrite]
  have after : FileCommands.afterBatch writtenWorld true [lateWrite] batch =
      .ended ⟨writtenWorld, true, [lateWrite], .errorBatch⟩ := by
    simp [FileCommands.afterBatch, FileCommands.hasError, batch, badRow, failure,
      Entry.Value.erase_ofAtom, isErrorAtom]
  have halted : Derivation (FileCommands.Step environment .unmarked) afterCut (.active midBatch [lateWrite])
      [batch] (.exhausted (.ended ⟨writtenWorld, true, [lateWrite], .errorBatch⟩)) := by
    simpa only [midBatch, after] using reported
  have finish : Derivation (FileCommands.Step environment .unmarked) 1
      (.ended ⟨writtenWorld, true, [lateWrite], .errorBatch⟩) []
      (.finished ⟨writtenWorld, true, [lateWrite], .errorBatch⟩) := .finished (.finish _)
  have wrote' : Derivation (FileCommands.Step environment .unmarked) first
      (FileCommands.start initialWorld true [writeSilently, inspect, lateWrite]) [[]]
      (.exhausted (.active (request writtenWorld inspect) [lateWrite])) := by
    simpa only [FileCommands.after_empty, request, FileCommands.start] using wrote
  refine ⟨first + (beforeCut + (afterCut + 1)), ?_, ?_, ?_⟩
  · simpa only [List.nil_append, List.append_nil, List.singleton_append] using
      wrote'.resume (readPart.resume (halted.resume finish))
  · simp [writtenWorld]
  · simp [writtenWorld, initialWorld]

/-- A parsed `!` entry containing an actual error goes through the ordinary Atom
entry judgment. It reports the error, not an empty result, before stopping. -/
theorem literal_error_stops_file (world : World) (label : Bool) (remaining : List Task) :
    let value := failure (.symbol "direct")
    let answer : Result := (Entry.Value.ofAtom value, Frame.empty)
    ∃ fuel, Derivation (FileCommands.Step environment .unmarked) fuel
      (FileCommands.start world label (FileCommands.entry value :: remaining)) [[answer]]
      (.finished ⟨world, label, remaining, .errorBatch⟩) := by
  intro value answer
  let current : WorldConfiguration Bool World :=
    ⟨world, label, .work (FileCommands.entry value), [], []⟩
  have evaluated : AtomRel environment label world [] [] (Entry.Value.ofAtom value) Atom.undefinedType
      Frame.empty [answer] world := by
    have entered := Stateful.AtomRel.delivered (environment := environment) (label := label)
      (world0 := world) (live := []) (scope := []) (value := Entry.Value.ofAtom value)
      (expected := Atom.undefinedType) (frame := Frame.empty) (policy := .unmarked)
      (by rw [Frame.read_empty]
          exact .stopped (Or.inr ⟨[.symbol "direct", .symbol "BadDestination"], by
            simp [value, failure, Entry.Value.erase_ofAtom]⟩))
    simpa only [Frame.read_empty, answer] using entered
  have source : current.SourceRel environment .unmarked [answer] world :=
    ⟨[answer], [answer], world, .work evaluated, .nil _, rfl⟩
  obtain ⟨fuel, report⟩ := FileCommands.report_source source remaining
  have terminal : FileCommands.afterBatch world label remaining [answer] =
      .ended ⟨world, label, remaining, .errorBatch⟩ := by
    simp [FileCommands.afterBatch, FileCommands.hasError, answer, value, failure, Entry.Value.erase_ofAtom,
      isErrorAtom]
  have reported : Derivation (FileCommands.Step environment .unmarked) fuel
      (FileCommands.start world label (FileCommands.entry value :: remaining)) [[answer]]
      (.exhausted (.ended ⟨world, label, remaining, .errorBatch⟩)) := by
    simpa only [FileCommands.start, current, terminal] using report
  have endNow : Derivation (FileCommands.Step environment .unmarked) 1
      (.ended ⟨world, label, remaining, .errorBatch⟩) []
      (.finished ⟨world, label, remaining, .errorBatch⟩) := .finished (.finish _)
  exact ⟨fuel + 1, by simpa only [List.append_nil] using (reported.resume endNow)⟩

end DriverControls
end Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
