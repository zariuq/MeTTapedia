import Mettapedia.Languages.TransitionSystem.LanguageDef
import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# The theory of a transition table through its contexts

The language of a transition table has constants only.  Its terms at an
interface of the sort of states include the listed states, at every binding
stage.  A context applied to a term gives a state only when the context is
the hole, so a context-labelled transition of a table is a move of the table
under a label that acts as the identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TransitionSystem

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- A filled one-hole context is a constant only when the context is the
hole. -/
theorem eq_hole_of_fill_eq_state {context : OneHoleContext} {pattern : Pattern}
    {label : String} (filled : context.fill pattern = state label) :
    context = .hole ∧ pattern = state label := by
  cases context with
  | hole => exact ⟨rfl, filled⟩
  | apply constructor before inner after => simp [OneHoleContext.fill, state] at filled
  | lambda binder inner => simp [OneHoleContext.fill, state] at filled
  | multiLambda arity binders inner => simp [OneHoleContext.fill, state] at filled
  | substBody inner replacement => simp [OneHoleContext.fill, state] at filled
  | substReplacement body inner => simp [OneHoleContext.fill, state] at filled
  | collection kind before inner after rest => simp [OneHoleContext.fill, state] at filled

namespace Table

variable {table : Table}

/-- A listed state is well sorted at every binding stage. -/
theorem state_sorted {label : String} (listed : label ∈ table.states) (stage : List TypeExpr) :
    OpenPatternWellSorted table.language FreeTypeContext.empty stage (.base "Proc")
      (state label) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact HasType.constructor (rule := stateDeclaration label) (List.mem_map_of_mem listed)
      (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil
  · simp [state, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  · simp [state, isObjectPattern, isObjectPatternList]
  · simp [ScopeSafeAt, state, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- A listed state as a term of an interface of the sort of states. -/
def stateTerm {interface : Interface} (ofStates : interface.type = .base "Proc")
    {label : String} (listed : label ∈ table.states) : Term table.language interface :=
  ⟨state label, by rw [ofStates]; exact state_sorted listed interface.stage⟩

@[simp] theorem stateTerm_val {interface : Interface} (ofStates : interface.type = .base "Proc")
    {label : String} (listed : label ∈ table.states) :
    (stateTerm ofStates listed).1 = state label := rfl

/-- A term that is a state lives at an interface of the sort of states, and
the state is listed. -/
theorem interface_of_state {interface : Interface} (term : Term table.language interface)
    {label : String} (shape : term.1 = state label) :
    interface.type = .base "Proc" ∧ label ∈ table.states := by
  have typed := term.2.1
  rw [shape] at typed
  obtain ⟨rule, ruleMember, ruleLabel, typeEq, -, -⟩ := HasType.apply_inv typed
  obtain ⟨listedLabel, listed, rfl⟩ := List.mem_map.mp ruleMember
  have same : listedLabel = label := ruleLabel
  subst same
  exact ⟨typeEq, listed⟩

variable (wellFormed : table.WellFormed)

/-- The validated presentation of a well-formed table. -/
def validated : ValidatedLanguageDef := ⟨table.language, validate_eq_nil wellFormed⟩

/-- The theory of a well-formed table through its contexts. -/
abbrev theory : ContextTheory.{0} := contextTheory base (validated wellFormed)

/-- **The reductions between terms of an interface are the moves of the
table.** -/
theorem rewrites_iff {interface : Interface} {term next : Term table.language interface} :
    (theory wellFormed).rewrites term next ↔
      ∃ move ∈ table.moves, term.1 = state move.2.1 ∧ next.1 = state move.2.2 :=
  (termStep_iff_step base table.language table.isEquationFree term next).trans table.step_iff

/-- A label under which some term is a state acts on every term as the
identity. -/
theorem label_identity_of_state {origin result : Interface}
    (label : (theory wellFormed).Label origin result) {witness : Term table.language origin}
    {name : String} (shape : ((theory wellFormed).apply label witness).1 = state name) :
    ∀ term : Term table.language origin, ((theory wellFormed).apply label term).1 = term.1 := by
  obtain ⟨context, plugs⟩ := exists_oneHole_of_label base label
  rw [plugs witness] at shape
  obtain ⟨rfl, -⟩ := eq_hole_of_fill_eq_state shape
  intro term
  rw [plugs term]
  rfl

/-- **A context-labelled transition of a table is a move of the table, under
a label that acts as the identity.** -/
theorem transition_iff {origin result : Interface}
    (label : (theory wellFormed).Label origin result) {term : Term table.language origin}
    {next : Term table.language result} :
    (theory wellFormed).Transition term label next ↔
      (∀ other : Term table.language origin,
        ((theory wellFormed).apply label other).1 = other.1) ∧
      ∃ move ∈ table.moves, term.1 = state move.2.1 ∧ next.1 = state move.2.2 := by
  constructor
  · intro transition
    obtain ⟨move, moveMember, source, target⟩ := (rewrites_iff wellFormed).mp transition
    have identity := label_identity_of_state wellFormed label source
    exact ⟨identity, move, moveMember, (identity term).symm.trans source, target⟩
  · rintro ⟨identity, move, moveMember, source, target⟩
    exact (rewrites_iff wellFormed).mpr ⟨move, moveMember, (identity term).trans source, target⟩

end Table

end Mettapedia.Languages.TransitionSystem
