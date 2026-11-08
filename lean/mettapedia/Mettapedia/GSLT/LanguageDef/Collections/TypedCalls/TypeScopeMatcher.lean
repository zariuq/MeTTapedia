import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission

/-!
# World-independent ordered type matching from resource-free operands

This is an instance of the existing native-shaped argument driver, not a
second whole-language typer. Matching uses the actual total atom unifier,
the directional top-level Atom/Undefined shortcuts, and the runtime space
class bridge. Actual Atom is not evidence for an arbitrary expected type.
Explicit observations of
external leaves model the resource reads a native equality/unification path
could make. Resource-free source operands and substitution images remove
those observations, and the returned substitution remains resource-free.

The result is exact for every argument prefix and first-local-match choice.
The normalizer is a separate fixed primitive capability; this file does not
certify all native arithmetic representations or nested wildcard semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission
open NativeTypeViews
open RetainedTypePayloads (ExternalView observe)

abbrev State := String → Atom

def SafeState (state : State) : Prop := ∀ name, resourceFree (state name) = true

def compose (after before : State) : State := fun name => substA after (before name)

def wildcard (type_ : Atom) : Bool := type_ == Atom.undefinedType || type_ == Atom.atomType

def actualWildcard (type_ : Atom) : Bool := type_ == Atom.undefinedType

def spaceValueType : Atom → Bool
  | .expression [.symbol head, _] => head == "Space"
  | _ => false

def spaceClassBridge (actual expected : Atom) : Bool :=
  (actual == .symbol "SpaceType" && spaceValueType expected) ||
    (expected == .symbol "SpaceType" && spaceValueType actual)

def unify (external : ExternalView) (state : State) (actual expected : Atom) : Option State :=
  let left := observe external (substA state actual)
  let right := observe external (substA state expected)
  if actualWildcard left || wildcard right || spaceClassBridge left right then some state
  else (UnifyAtoms.unify left right).map fun theta => compose (UnifyAtoms.readBack theta) state

theorem unify_world (first second : ExternalView) (state : State) (safeState : SafeState state)
    (actual expected : Atom) (actualSafe : resourceFree actual = true)
    (expectedSafe : resourceFree expected = true) :
    unify first state actual expected = unify second state actual expected := by
  have left := substitute_resourceFree state safeState actual actualSafe
  have right := substitute_resourceFree state safeState expected expectedSafe
  simp [unify, observe_resourceFree first _ left, observe_resourceFree second _ left,
    observe_resourceFree first _ right, observe_resourceFree second _ right]

theorem unify_preserves (external : ExternalView) (state : State) (safeState : SafeState state)
    (actual expected : Atom) (actualSafe : resourceFree actual = true)
    (expectedSafe : resourceFree expected = true) (after : State)
    (accepted : unify external state actual expected = some after) : SafeState after := by
  have left := substitute_resourceFree state safeState actual actualSafe
  have right := substitute_resourceFree state safeState expected expectedSafe
  simp only [unify, observe_resourceFree external _ left, observe_resourceFree external _ right] at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact safeState
  · simp only [Option.map_eq_some_iff] at accepted
    obtain ⟨theta, matched, rfl⟩ := accepted
    intro name
    exact substitute_resourceFree _ (unify_resourceFree matched left right) _ (safeState name)

def metaCheckAtom (formal kind : Atom) : Option Bool :=
  if formal == Atom.atomType then some true
  else if formal == Atom.symbolType || formal == Atom.variableType ||
      formal == Atom.groundedType || formal == Atom.expressionType then some (formal == kind)
  else none

def ops (external : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) : Ops Atom State Atom where
  arrow := fun type_ =>
    (getFunctionArgTypes type_).bind fun params => (getFunctionRetType type_).map (params, ·)
  initial := Atom.var
  apply := substA
  unify := unify external
  metaCheck := metaCheckAtom
  normalize := normalize
  tuple := Atom.expression
  undefined := Atom.undefinedType
  nativeMork := .symbol "MorkSpace"
  listType := .symbol "List"
  subtypeAdditions := subtypes
  annotationPolicy := .historicalOverride

/-- Current internal application typing supplements declared rows with
arrow-derived answers. The equality port observes resource leaves; cache
admission must still establish the existing resource-free operand boundary. -/
def currentOps (external : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) : Ops Atom State Atom :=
  { ops external normalize subtypes with
    annotationPolicy := .supplement (fun left right => observe external left == observe external right) }

def ReadsSafe (reads : NativeTypeViews.Reads Atom Atom Atom) (values : List Atom) : Prop :=
  ∀ value ∈ values, resourceFreeList (reads.inferred value) = true

theorem firstResult_congr_on {α β : Type} (left right : α → Option β) (values : List α)
    (agree : ∀ value ∈ values, left value = right value) :
    StampInference.firstResult left values = StampInference.firstResult right values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [StampInference.firstResult, agree value (by simp)]
      split
      · rfl
      · exact ih (fun item member => agree item (List.mem_cons_of_mem _ member))

theorem firstResult_preserves (external : ExternalView) (state : State) (safeState : SafeState state)
    (expected : Atom) (expectedSafe : resourceFree expected = true)
    (actuals : List Atom) (actualsSafe : resourceFreeList actuals = true)
    (after : State)
    (chosen : StampInference.firstResult (fun actual => unify external state actual expected) actuals = some after) :
    SafeState after := by
  obtain ⟨pre, actual, post, shape, _, accepted⟩ :=
    (StampInference.firstResult_some_iff _ _ _).mp chosen
  have present : actual ∈ actuals := by simp [shape]
  exact unify_preserves external state safeState actual expected
    ((resourceFreeList_iff _).mp actualsSafe actual present) expectedSafe after accepted

theorem sourceArgs_preserves (external : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom) :
    ∀ formals values state,
      resourceFreeList formals = true → ReadsSafe reads values → SafeState state →
      ∀ after, sourceArgs (ops external normalize subtypes) reads formals values state = some after →
        SafeState after
  | [], [], state, _, _, safe, after, accepted => by cases Option.some.inj accepted; exact safe
  | [], _ :: _, _, _, _, _, _, accepted => by simp [sourceArgs] at accepted
  | _ :: _, [], _, _, _, _, _, accepted => by simp [sourceArgs] at accepted
  | formal :: formals, value :: values, state, formalsSafe, valuesSafe, stateSafe, after, accepted => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      have tailSafe : ReadsSafe reads values := fun other member =>
        valuesSafe other (List.mem_cons_of_mem _ member)
      simp only [sourceArgs, ops] at accepted
      split at accepted
      next metatype =>
        exact sourceArgs_preserves external normalize subtypes reads formals values state
          formalsSafe.2 tailSafe stateSafe after accepted
      next refused => simp at accepted
      next ordinary =>
        split at accepted
        next rejected => simp at accepted
        next middle matched =>
          have middleSafe := firstResult_preserves external state stateSafe (substA state formal)
            expectedSafe (reads.inferred value) (valuesSafe value (by simp)) middle matched
          exact sourceArgs_preserves external normalize subtypes reads formals values middle
            formalsSafe.2 tailSafe middleSafe after accepted

/-- Both the first-match decisions and the complete threaded substitution
are identical across worlds. Mutable annotations on child typings violate
`ReadsSafe`, even if the returned range itself is an immutable symbol. -/
theorem sourceArgs_world (first second : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom) :
    ∀ formals values state,
      resourceFreeList formals = true → ReadsSafe reads values → SafeState state →
      sourceArgs (ops first normalize subtypes) reads formals values state =
        sourceArgs (ops second normalize subtypes) reads formals values state
  | [], values, state, _, _, _ => by cases values <;> rfl
  | _ :: _, [], _, _, _, _ => rfl
  | formal :: formals, value :: values, state, formalsSafe, valuesSafe, stateSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      have tailSafe : ReadsSafe reads values := fun other member =>
        valuesSafe other (List.mem_cons_of_mem _ member)
      simp only [sourceArgs, ops]
      split
      next metatype =>
        exact sourceArgs_world first second normalize subtypes reads formals values state
          formalsSafe.2 tailSafe stateSafe
      next refused => rfl
      next ordinary =>
        have same := firstResult_congr_on
          (fun actual => unify first state actual (substA state formal))
          (fun actual => unify second state actual (substA state formal)) (reads.inferred value)
          (fun actual member => unify_world first second state stateSafe actual (substA state formal)
            ((resourceFreeList_iff _).mp (valuesSafe value (by simp)) actual member) expectedSafe)
        rw [same]
        split
        next rejected => rfl
        next middle chosen =>
          have middleSafe := firstResult_preserves second state stateSafe (substA state formal)
            expectedSafe (reads.inferred value) (valuesSafe value (by simp)) middle chosen
          exact sourceArgs_world first second normalize subtypes reads formals values middle
            formalsSafe.2 tailSafe middleSafe

theorem arrow_resourceFree (external : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) {row : Atom} {formals : List Atom} {range : Atom}
    (safe : resourceFree row = true)
    (selected : (ops external normalize subtypes).arrow row = some (formals, range)) :
    resourceFreeList formals = true ∧ resourceFree range = true := by
  simp only [ops, Option.bind_eq_some_iff, Option.map_eq_some_iff] at selected
  obtain ⟨params, args, returned, result, same⟩ := selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  unfold getFunctionArgTypes at args
  split at args <;> try contradiction
  split at args <;> try contradiction
  have paramsEq := Option.some.inj args
  rename_i ignored rest enough
  have childrenSafe : ∀ child ∈ rest, resourceFree child = true := by
    simpa [resourceFree, resourceFreeList, resourceFreeList_iff] using safe
  constructor
  · apply (resourceFreeList_iff _).mpr
    intro child member
    rw [← paramsEq] at member
    exact childrenSafe child (List.mem_of_mem_dropLast member)
  · simp only [getFunctionRetType, if_pos enough] at result
    exact childrenSafe returned (List.mem_of_getLast? result)

/-- The source row driver preserves written order and duplicate rows. Its
world-independence follows from the actual argument loop, not an assumed
invariant result list. -/
theorem sourceRows_world (first second : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values : List Atom) (valuesSafe : ReadsSafe reads values) :
    ∀ rows, resourceFreeList rows = true →
      sourceRows (ops first normalize subtypes) reads values rows =
        sourceRows (ops second normalize subtypes) reads values rows
  | [], _ => rfl
  | row :: rows, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      have tail := sourceRows_world first second normalize subtypes reads values valuesSafe rows safe.2
      simp only [sourceRows]
      cases arrow : (ops first normalize subtypes).arrow row with
      | none =>
          have arrow' : (ops second normalize subtypes).arrow row = none := arrow
          simpa only [arrow'] using tail
      | some pair =>
          obtain ⟨formals, range⟩ := pair
          have formalsSafe := (arrow_resourceFree first normalize subtypes safe.1 arrow).1
          have same := sourceArgs_world first second normalize subtypes reads formals values
            Atom.var formalsSafe valuesSafe (fun _ => rfl)
          have arrow' : (ops second normalize subtypes).arrow row = some (formals, range) := arrow
          simp only [arrow']
          dsimp only [ops] at same tail ⊢
          rw [same, tail]

theorem sourceRows_preserves (external : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values : List Atom) (valuesSafe : ReadsSafe reads values) :
    ∀ rows, resourceFreeList rows = true →
      resourceFreeList (sourceRows (ops external normalize subtypes) reads values rows) = true
  | [], _ => rfl
  | row :: rows, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      have tail := sourceRows_preserves external normalize normalizeSafe subtypes reads values
        valuesSafe rows safe.2
      simp only [sourceRows]
      cases arrow : (ops external normalize subtypes).arrow row with
      | none => exact tail
      | some pair =>
          obtain ⟨formals, range⟩ := pair
          have typesSafe := arrow_resourceFree external normalize subtypes safe.1 arrow
          simp only
          cases chosen : sourceArgs (ops external normalize subtypes) reads formals values
              (ops external normalize subtypes).initial with
          | none => exact tail
          | some state =>
              have stateSafe := sourceArgs_preserves external normalize subtypes reads formals values
                Atom.var typesSafe.1 valuesSafe (fun _ => rfl) state chosen
              exact Bool.and_eq_true_iff.mpr
                ⟨normalizeSafe _ (substitute_resourceFree state stateSafe range typesSafe.2), tail⟩

theorem sourceArgs_services_irrel (external : ExternalView)
    (firstNormalize secondNormalize : Atom → Atom) (firstSubtypes secondSubtypes : List Atom → List Atom)
    (reads : NativeTypeViews.Reads Atom Atom Atom) (formals : List Atom) :
    ∀ values state,
      sourceArgs (ops external firstNormalize firstSubtypes) reads formals values state =
        sourceArgs (ops external secondNormalize secondSubtypes) reads formals values state := by
  induction formals with
  | nil => intro values state; cases values <;> rfl
  | cons formal formals ih =>
      intro values state
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [sourceArgs, ops]
          split
          · exact ih values state
          · rfl
          · split
            · rfl
            · exact ih values _

/-- Normalizer correspondence is needed only on the resource-free range
instances actually reached by ordered argument checking. -/
theorem sourceRows_normalizer_congr (external : ExternalView)
    (firstNormalize secondNormalize : Atom → Atom)
    (agree : ∀ atom, resourceFree atom = true → firstNormalize atom = secondNormalize atom)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values : List Atom) (valuesSafe : ReadsSafe reads values) :
    ∀ rows, resourceFreeList rows = true →
      sourceRows (ops external firstNormalize subtypes) reads values rows =
        sourceRows (ops external secondNormalize subtypes) reads values rows
  | [], _ => rfl
  | row :: rows, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      have tail := sourceRows_normalizer_congr external firstNormalize secondNormalize agree subtypes
        reads values valuesSafe rows safe.2
      simp only [sourceRows]
      cases arrow : (ops external firstNormalize subtypes).arrow row with
      | none =>
          have arrow' : (ops external secondNormalize subtypes).arrow row = none := arrow
          simpa only [arrow'] using tail
      | some pair =>
          obtain ⟨formals, range⟩ := pair
          have typesSafe := arrow_resourceFree external firstNormalize subtypes safe.1 arrow
          have arrow' : (ops external secondNormalize subtypes).arrow row = some (formals, range) := arrow
          have arguments := sourceArgs_services_irrel external firstNormalize secondNormalize subtypes subtypes
            reads formals values Atom.var
          simp only [arrow']
          dsimp only [ops] at arguments tail ⊢
          rw [← arguments]
          split
          next refused => exact tail
          next state accepted =>
            have stateSafe := sourceArgs_preserves external firstNormalize subtypes reads formals values
              Atom.var typesSafe.1 valuesSafe (fun _ => rfl) state accepted
            rw [agree _ (substitute_resourceFree state stateSafe range typesSafe.2), tail]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher
