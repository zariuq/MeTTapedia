import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.RuleInstances
import Mettapedia.OSLF.MeTTaIL.UnaryNumerals

/-!
# A finite transition system as a language definition

A finite transition table is a list of states and a list of moves between
them.  It is a language definition with one sort, one constant per state and
one premise-free rule per move.  Nothing else reduces: there is no
constructor with an argument, no equation and no contextual rule.

The definition passes the declaration gate as soon as the table is well
formed: no state and no rule name is listed twice, and every move is between
listed states.  Its reductions are exactly the moves of the table.

Controls that need a small transition system with prescribed branching are
tables; none of them repeats these proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TransitionSystem

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- A finite transition table: the states, and the moves, each with the name
of its rule, the state it leaves and the state it reaches. -/
structure Table where
  states : List String
  moves : List (String × String × String)

/-- The term of a state. -/
def state (label : String) : Pattern := .apply label []

/-- A state is a constant of the one sort. -/
def stateDeclaration (label : String) : GrammarRule :=
  { label := label, category := "Proc", params := [], syntaxPattern := [] }

/-- The rule of a move. -/
def moveRule (move : String × String × String) : RewriteRule where
  name := move.1
  typeContext := []
  premises := []
  left := state move.2.1
  right := state move.2.2

theorem state_injective {first second : String} (same : state first = state second) :
    first = second := by
  simpa [state] using same

namespace Table

/-- The language of a table. -/
def language (table : Table) : LanguageDef :=
  { name := "TransitionSystem"
    types := ["Proc"]
    terms := table.states.map stateDeclaration
    equations := []
    rewrites := table.moves.map moveRule }

/-- The table is well formed: no state and no rule name is listed twice, and
every move is between listed states. -/
def WellFormed (table : Table) : Prop :=
  table.states.Nodup ∧ (table.moves.map (·.1)).Nodup ∧
    ∀ move ∈ table.moves, move.2.1 ∈ table.states ∧ move.2.2 ∈ table.states

instance (table : Table) : Decidable table.WellFormed := by
  unfold WellFormed
  infer_instance

variable {table : Table}

/-- Among the declarations of a table without repeated states, exactly one
has a given listed label. -/
theorem filter_label {states : List String} (distinct : states.Nodup) {label : String}
    (listed : label ∈ states) :
    (states.map stateDeclaration).filter (fun declaration => declaration.label == label) =
      [stateDeclaration label] := by
  induction states with
  | nil => cases listed
  | cons head tail recurse =>
      obtain ⟨headFresh, tailDistinct⟩ := List.nodup_cons.mp distinct
      by_cases same : head = label
      · subst same
        have none : (tail.map stateDeclaration).filter
            (fun declaration => declaration.label == head) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro declaration membership
          obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp membership
          have differs : other ≠ head := fun equal => headFresh (equal ▸ otherMember)
          simpa [stateDeclaration] using differs
        simp [stateDeclaration, none]
      · have inTail : label ∈ tail := by
          rcases List.mem_cons.mp listed with isHead | inTail
          · exact absurd isHead.symm same
          · exact inTail
        have skip : ((stateDeclaration head).label == label) = false := by
          simpa [stateDeclaration] using same
        rw [List.map_cons, List.filter_cons_of_neg (by simpa using skip)]
        exact recurse tailDistinct inTail

/-- A listed state is declared once, as a constant. -/
theorem referenceDeclared_state (wellFormed : table.WellFormed) {label : String}
    (listed : label ∈ table.states) :
    LanguageDef.referenceDeclared table.language.terms (label, 0) = true := by
  simp only [LanguageDef.referenceDeclared, language, filter_label wellFormed.1 listed]
  rfl

/-- The rule of a move between listed states passes the rule gate. -/
theorem moveRule_validates (wellFormed : table.WellFormed) {move : String × String × String}
    (membership : move ∈ table.moves) :
    LanguageDef.validateRewrite table.language (moveRule move) = [] := by
  obtain ⟨sourceListed, targetListed⟩ := wellFormed.2.2 move membership
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
  · rfl
  · intro entry entryMember
    cases entryMember
  · intro reference referenceMember
    have same : reference = (move.2.1, 0) := by
      simpa [moveRule, state, Pattern.constructorRefs_apply_nil] using referenceMember
    rw [same]
    exact referenceDeclared_state wellFormed sourceListed
  · intro reference referenceMember
    have same : reference = (move.2.2, 0) := by
      simpa [moveRule, state, Pattern.constructorRefs_apply_nil] using referenceMember
    rw [same]
    exact referenceDeclared_state wellFormed targetListed
  · rule_patterns [moveRule, state]

/-- **The language of a well-formed table passes the declaration gate.** -/
theorem validate_eq_nil (wellFormed : table.WellFormed) : table.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · exact List.nodup_singleton "Proc"
  · have labels : (table.language.terms.map (·.label)) = table.states := by
      change (table.states.map stateDeclaration).map (·.label) = table.states
      rw [List.map_map]
      exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)
    rw [labels]
    exact wellFormed.1
  · have names : (table.language.rewrites.map (·.name)) = table.moves.map (·.1) := by
      change (table.moves.map moveRule).map (·.name) = table.moves.map (·.1)
      rw [List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [names]
    exact wellFormed.2.1
  · intro term membership
    obtain ⟨label, -, rfl⟩ := List.mem_map.mp membership
    exact List.mem_singleton.mpr rfl
  · intro term membership parameter parameterMember
    obtain ⟨label, -, rfl⟩ := List.mem_map.mp membership
    cases parameterMember
  · intro term membership
    obtain ⟨label, -, rfl⟩ := List.mem_map.mp membership
    exact Or.inl rfl
  · intro rewrite membership
    obtain ⟨move, moveMember, rfl⟩ := List.mem_map.mp membership
    exact moveRule_validates wellFormed moveMember

/-- The language of a table generates no static equation. -/
theorem isEquationFree (table : Table) : table.language.isEquationFree = true := by
  simp [LanguageDef.isEquationFree, LanguageDef.usesCollection,
    LanguageDef.hasAlgebraDeclarations, language, stateDeclaration]

/-- The rules of a table carry no premise and bind nothing. -/
theorem plainRules (table : Table) : PlainRules table.language := by
  intro rule membership
  obtain ⟨move, -, rfl⟩ := List.mem_map.mp membership
  exact ⟨rfl, ruleDepthAligned_of_binderFree _ (by simp [moveRule, state, binderFree, binderFreeList])
    (by simp [moveRule, state, binderFree, binderFreeList])⟩

theorem matchCorrect (table : Table) :
    ∀ rule ∈ table.language.rewrites, Pattern.isMatchCorrect rule.left = true := by
  intro rule membership
  obtain ⟨move, -, rfl⟩ := List.mem_map.mp membership
  simp [moveRule, state, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux]

/-- A state matches itself, binding nothing. -/
theorem state_matches_itself (label : String) :
    ([] : Bindings) ∈ matchPattern (state label) (state label) := by
  simp [state, matchPattern, matchArgs]

/-- **The reductions of the language of a table are the moves of the
table.** -/
theorem step_iff (table : Table) {relations : RelationEnv} {source target : Pattern} :
    Step (engineBasePremises relations) table.language source target ↔
      ∃ move ∈ table.moves, source = state move.2.1 ∧ target = state move.2.2 := by
  constructor
  · intro step
    obtain ⟨rule, membership, bindings, rfl, rfl⟩ :=
      sides_of_step table.plainRules table.matchCorrect step
    obtain ⟨move, moveMember, rfl⟩ := List.mem_map.mp membership
    exact ⟨move, moveMember, by simp [moveRule, state, applyBindings],
      by simp [moveRule, state, applyBindings]⟩
  · rintro ⟨move, moveMember, rfl, rfl⟩
    exact (step_iff_exists_match table.plainRules).mpr
      ⟨moveRule move, List.mem_map_of_mem moveMember, [], state_matches_itself move.2.1,
        by simp [moveRule, state, applyBindings]⟩

end Table

end Mettapedia.Languages.TransitionSystem
