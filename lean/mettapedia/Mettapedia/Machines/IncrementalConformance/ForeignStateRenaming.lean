import Mettapedia.Machines.IncrementalConformance.ForeignState
import Mathlib.Data.Fintype.Sum

/-!
# Stable renaming and adding fresh variables to finite foreign states

Renaming transports goals and inert attributes by variable identity. A valuation
on the target variables restricts along that map; this gives exact observation
laws. Attribute lookup at an old variable requires an injective map. Lookup at
a variable outside its image is absent.

Adding an arbitrary finite set of fresh variables uses `Sum Var Fresh`. The
retained extension is constructed from the previous solution store, without
replaying its history: an extended valuation is kept precisely when its old
restriction was kept. Old attributes are copied and fresh attributes start
absent. This construction preserves the independently defined reference
relation. With a nonempty value domain, restriction is onto the old solution
set, so fresh variables preserve satisfiability and call acceptance.

Equality goals equate valuation values; they do not merge variable identities
or their attributes. These are finite-domain and inert-attribute admission laws,
not a semantics of SWI attribute hooks, fresh runtime handle allocation or
solver cost. The variable universe may grow at each proved extension boundary;
no infinite valuation space is enumerated by this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignState.Renaming

universe u v w x y

variable {Var : Type u} {Target : Type x} {Fresh : Type y}
  {Val : Type v} {Attr : Type w}

def renameGoal (mapVar : Var → Target) : Goal Var Val → Goal Target Val
  | .bind key value => .bind (mapVar key) value
  | .equal left right => .equal (mapVar left) (mapVar right)
  | .different left right => .different (mapVar left) (mapVar right)

def renameEvent (mapVar : Var → Target) : Event Var Val Attr → Event Target Val Attr
  | .post goal => .post (renameGoal mapVar goal)
  | .putAttribute key payload => .putAttribute (mapVar key) payload

def renameHistory (mapVar : Var → Target) (history : List (Event Var Val Attr)) :
    List (Event Target Val Attr) := history.map (renameEvent mapVar)

def restrict (mapVar : Var → Target) (valuation : Valuation Target Val) :
    Valuation Var Val := valuation ∘ mapVar

variable [DecidableEq Var] [DecidableEq Target] [DecidableEq Val]

omit [DecidableEq Var] [DecidableEq Target] in
theorem accepts_rename_goal (mapVar : Var → Target) (goal : Goal Var Val)
    (valuation : Valuation Target Val) :
    (renameGoal mapVar goal).accepts valuation = goal.accepts (restrict mapVar valuation) := by
  cases goal <;> rfl

omit [DecidableEq Var] [DecidableEq Target] in
theorem accepts_rename_event (mapVar : Var → Target) (event : Event Var Val Attr)
    (valuation : Valuation Target Val) :
    (renameEvent mapVar event).accepts valuation = event.accepts (restrict mapVar valuation) := by
  cases event with
  | post goal => exact accepts_rename_goal mapVar goal valuation
  | putAttribute key payload => rfl

variable [Fintype Var] [Fintype Target] [Fintype Val]

/-- A target solution is exactly a valuation satisfying the old history on its
restricted variables. This direction is valid even for noninjective maps. -/
theorem reference_solutions_restrict (mapVar : Var → Target)
    (history : List (Event Var Val Attr)) (valuation : Valuation Target Val) :
    valuation ∈ referenceSolutions (renameHistory mapVar history) ↔
      restrict mapVar valuation ∈ referenceSolutions history := by
  simp [referenceSolutions, renameHistory, accepts_rename_event]

omit [DecidableEq Val] [Fintype Var] [Fintype Target] [Fintype Val] in
/-- Injectivity prevents an attribute written on one old variable overwriting
another old variable's attribute after transport. -/
theorem reference_attribute_old (mapVar : Var → Target)
    (injective : Function.Injective mapVar) (history : List (Event Var Val Attr)) (key : Var) :
    referenceAttribute (renameHistory mapVar history) (mapVar key) =
      referenceAttribute history key := by
  induction history with
  | nil => rfl
  | cons event history ih =>
      cases event with
      | post goal => exact ih
      | putAttribute old payload =>
          simp only [renameHistory, List.map_cons, renameEvent, referenceAttribute]
          simpa only [injective.eq_iff, renameHistory] using congrArg
            (fun rest => if key = old then some payload else rest) ih

omit [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Target] [Fintype Val] in
/-- A target variable outside the transported identity range has no old attribute. -/
theorem reference_attribute_fresh (mapVar : Var → Target)
    (history : List (Event Var Val Attr)) (key : Target)
    (fresh : ∀ old, mapVar old ≠ key) :
    referenceAttribute (renameHistory mapVar history) key = none := by
  induction history with
  | nil => rfl
  | cons event history ih =>
      cases event with
      | post goal => exact ih
      | putAttribute old payload =>
          simp only [renameHistory, List.map_cons, renameEvent, referenceAttribute]
          rw [if_neg (Ne.symm (fresh old))]
          exact ih

/-- This extension is constructive once an arbitrary value for fresh variables
is supplied. It does not identify any old variable with a fresh one. -/
def extendValuation (seed : Val) (valuation : Valuation Var Val) :
    Valuation (Sum Var Fresh) Val := Sum.elim valuation (fun _ => seed)

omit [DecidableEq Var] [DecidableEq Target] [DecidableEq Val] [Fintype Var] [Fintype Target] [Fintype Val] in
@[simp] theorem restrict_extend (seed : Val) (valuation : Valuation Var Val) :
    restrict (Sum.inl : Var → Sum Var Fresh) (extendValuation seed valuation) = valuation := rfl

variable [DecidableEq Fresh] [Fintype Fresh]

/-- Extend the retained domain by unconstrained fresh variables, preserving
inert old attributes without reconstructing their event history. -/
def extendState (state : Retained Var Val Attr) : Retained (Sum Var Fresh) Val Attr where
  solutions := Finset.univ.filter fun valuation =>
    restrict (Sum.inl : Var → Sum Var Fresh) valuation ∈ state.solutions
  attributes := Sum.elim state.attributes (fun _ => none)

@[simp] theorem mem_extendState (state : Retained Var Val Attr)
    (valuation : Valuation (Sum Var Fresh) Val) :
    valuation ∈ (extendState state).solutions ↔
      restrict Sum.inl valuation ∈ state.solutions := by
  simp [extendState]

@[simp] theorem extended_attribute_old (state : Retained Var Val Attr) (key : Var) :
    (extendState (Fresh := Fresh) state).attributes (.inl key) = state.attributes key := rfl

@[simp] theorem extended_attribute_fresh (state : Retained Var Val Attr) (key : Fresh) :
    (extendState state).attributes (.inr key) = none := rfl

/-- Fresh extension preserves the reference/retained simulation for every
history, including unsatisfiable histories and overwritten attributes. -/
theorem extend_related {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state) :
    Related (renameHistory (Sum.inl : Var → Sum Var Fresh) history) (extendState state) := by
  constructor
  · ext valuation
    rw [mem_extendState, related.1, reference_solutions_restrict]
  · funext key
    cases key with
    | inl old =>
        rw [extended_attribute_old, related.2]
        exact (reference_attribute_old Sum.inl Sum.inl_injective history old).symm
    | inr fresh =>
        rw [extended_attribute_fresh]
        exact (reference_attribute_fresh Sum.inl history (.inr fresh)
          (fun old => Sum.inl_ne_inr)).symm

/-- Every old retained valuation has an extension. Nonempty values are essential
when the old variable type is empty and the fresh variable type is not. -/
theorem restriction_image [Nonempty Val] (state : Retained Var Val Attr) :
    (extendState (Fresh := Fresh) state).solutions.image (restrict Sum.inl) = state.solutions := by
  ext valuation
  constructor
  · intro member
    obtain ⟨extended, kept, rfl⟩ := Finset.mem_image.mp member
    exact (mem_extendState state extended).mp kept
  · intro member
    obtain ⟨seed⟩ := ‹Nonempty Val›
    apply Finset.mem_image.mpr
    exact ⟨extendValuation seed valuation, (mem_extendState _ _).mpr member, rfl⟩

theorem extended_empty_iff [Nonempty Val] (state : Retained Var Val Attr) :
    (extendState (Fresh := Fresh) state).solutions = ∅ ↔ state.solutions = ∅ := by
  constructor
  · intro empty
    have same := restriction_image (Fresh := Fresh) state
    rw [empty, Finset.image_empty] at same
    exact same.symm
  · intro empty
    ext valuation
    simp [mem_extendState, empty]

theorem extended_nonempty_iff [Nonempty Val] (state : Retained Var Val Attr) :
    (extendState (Fresh := Fresh) state).solutions.Nonempty ↔ state.solutions.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty]
  exact not_congr (extended_empty_iff (Fresh := Fresh) state)

omit [DecidableEq Var] [DecidableEq Target] [DecidableEq Val]
  [Fintype Var] [Fintype Target] [Fintype Val] [DecidableEq Fresh] [Fintype Fresh] in
private theorem state_ext {L R : Retained Var Val Attr}
    (solutions : L.solutions = R.solutions) (attributes : L.attributes = R.attributes) : L = R := by
  cases L
  cases R
  cases solutions
  cases attributes
  rfl

/-- Updating an old variable then extending agrees with extending then updating
its transported identity. This supplies an actual commuting update square. -/
theorem advance_extend (event : Event Var Val Attr) (state : Retained Var Val Attr) :
    advance (renameEvent (Sum.inl : Var → Sum Var Fresh) event) (extendState state) =
      extendState (advance event state) := by
  apply state_ext
  · ext valuation
    simp only [advance, Finset.mem_filter, mem_extendState, accepts_rename_event]
  · funext key
    cases event with
    | post goal => rfl
    | putAttribute old payload =>
        cases key with
        | inl key =>
            change Function.update (Sum.elim state.attributes (fun _ : Fresh => none))
              (.inl old) (some payload) (.inl key) =
                Function.update state.attributes old (some payload) key
            by_cases same : key = old
            · subst key
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne (fun h => same (Sum.inl.inj h)),
                Function.update_of_ne same]
              rfl
        | inr fresh =>
            change Function.update (Sum.elim state.attributes (fun _ : Fresh => none))
              (.inl old) (some payload) (.inr fresh) = none
            rw [Function.update_of_ne Sum.inr_ne_inl]
            rfl

/-- Accept/reject statuses and resulting retained states commute with extension;
a newly introduced fresh variable cannot change an old call's success. -/
theorem call_extend [Nonempty Val] (event : Event Var Val Attr)
    (state : Retained Var Val Attr) :
    (retainedCall (renameEvent (Sum.inl : Var → Sum Var Fresh) event) (extendState state)).1 =
      (retainedCall event state).1 ∧
    (retainedCall (renameEvent (Sum.inl : Var → Sum Var Fresh) event) (extendState state)).2 =
      extendState (retainedCall event state).2 := by
  simp only [retainedCall, advance_extend, extended_empty_iff]
  split_ifs <;> exact ⟨rfl, rfl⟩

namespace Controls

abbrev S := Retained Bool Bool Nat

def oldHistory : List (Event Bool Bool Nat) :=
  [.post (.bind false true), .putAttribute false 42]

def oldState : S := (retainedCalls oldHistory.reverse initial).2

/-- Old bindings and attributes survive, while one fresh variable is initially
unconstrained and independently bindable. -/
theorem fresh_variable_can_be_bound_independently :
    let enlarged : Retained (Sum Bool Unit) Bool Nat := extendState oldState
    enlarged.attributes (.inl false) = some 42 ∧
      enlarged.attributes (.inr ()) = none ∧
      (retainedCall (.post (.bind (.inr ()) false)) enlarged).1 = true ∧
      (retainedCall (.post (.bind (.inr ()) true)) enlarged).1 = true := by decide

/-- A noninjective variable map can erase satisfiability. -/
theorem identifying_distinct_variables_rejects :
    let event : Event Bool Bool Nat := .post (.different false true)
    (retainedCall event (initial : S)).1 = true ∧
      (retainedCall (renameEvent (fun _ : Bool => false) event) (initial : S)).1 = false := by
  decide

/-- Colliding identities also change inert attribute lookup. -/
theorem identifying_variables_overwrites_attribute :
    let history : List (Event Bool Bool Nat) :=
      [.putAttribute true 2, .putAttribute false 1]
    referenceAttribute history false = some 1 ∧
      referenceAttribute (renameHistory (fun _ : Bool => false) history) false = some 2 := by
  decide

/-- With an empty value domain there is an empty old valuation, but no valuation
of an added variable. Dropping Nonempty Val would make the theorem false. -/
theorem empty_value_domain_breaks_extension :
    (initial : Retained Empty Empty Nat).solutions.Nonempty ∧
      ¬ (extendState (Fresh := Unit) (initial : Retained Empty Empty Nat)).solutions.Nonempty := by
  decide

end Controls

end Mettapedia.Machines.IncrementalConformance.ForeignState.Renaming
