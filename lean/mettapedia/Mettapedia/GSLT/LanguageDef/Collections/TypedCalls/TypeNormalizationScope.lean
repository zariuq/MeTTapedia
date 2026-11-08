import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InertTypeDependencies

/-!
# Resource-free normalization dependencies

This extends the inert-normalization subset to actual primitive calls. Each
primitive receives the observed argument atoms. The dispatch traversal and
arity/license checks are the ones in `InertTypeDependencies.normalize`.
Resource-free operands make the observations independent of the world.

Each licensed primitive owes a separate result-closure theorem. This is
strictly smaller than assuming that the whole type inference service is
stable: the traversal, intermediate outputs and exact returned atom are
proved here. Boolean-result operations and selecting an existing operand
have direct closure proofs below. Native arithmetic, ABT and collection
codecs must instantiate their own primitive cases; a type-pure flag alone
is not a proof of those cases.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeDependencyAdmission
open InertTypeDependencies (normalize normalizeList normalizeHead)
open RetainedTypePayloads (ExternalView observeList)

abbrev Primitive := String → List Atom → Option Atom

def observed (external : ExternalView) (primitive : Primitive) : Primitive :=
  fun head args => primitive head (observeList external args)

/-- This obligation is indexed by the actual licensed head and operands.
It does not permit a primitive to fabricate a resource-valued result. -/
def ResultsClosed (active : String → Bool) (primitive : Primitive) : Prop :=
  ∀ head args, active head = true → resourceFreeList args = true →
    ∀ result, primitive head args = some result → resourceFree result = true

theorem observed_closed (active : String → Bool) (external : ExternalView)
    (primitive : Primitive) (closed : ResultsClosed active primitive) :
    ResultsClosed active (observed external primitive) := by
  intro head args licensed safe result returned
  simp only [observed, observeList_resourceFree external args safe] at returned
  exact closed head args licensed safe result returned

theorem head_preserves (active : String → Bool) (primitive : Primitive)
    (closed : ResultsClosed active primitive) (atom : Atom) (safe : resourceFree atom = true) :
    resourceFree (normalizeHead active primitive atom) = true := by
  unfold normalizeHead
  split
  next head first second rest =>
    have argsSafe : resourceFreeList (first :: second :: rest) = true := by
      simpa [resourceFree, resourceFreeList] using safe
    split
    next licensed =>
      cases returned : primitive head (first :: second :: rest) with
      | none => exact safe
      | some result => exact closed head _ licensed argsSafe result returned
    next _ => exact safe
  next _ => exact safe

mutual
theorem normalize_preserves (active : String → Bool) (primitive : Primitive)
    (closed : ResultsClosed active primitive) : ∀ atom,
    resourceFree atom = true → resourceFree (normalize active primitive atom) = true
  | .symbol _, safe => safe
  | .var _, safe => safe
  | .grounded _, safe => safe
  | .expression children, safe => by
      rw [InertTypeDependencies.normalize]
      split
      · exact safe
      · exact head_preserves active primitive closed _
          (normalizeList_preserves active primitive closed children safe)
theorem normalizeList_preserves (active : String → Bool) (primitive : Primitive)
    (closed : ResultsClosed active primitive) : ∀ atoms,
    resourceFreeList atoms = true → resourceFreeList (normalizeList active primitive atoms) = true
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      exact Bool.and_eq_true_iff.mpr
        ⟨normalize_preserves active primitive closed atom safe.1,
          normalizeList_preserves active primitive closed atoms safe.2⟩
end

theorem head_world (active : String → Bool) (first second : ExternalView)
    (primitive : Primitive) (atom : Atom) (safe : resourceFree atom = true) :
    normalizeHead active (observed first primitive) atom =
      normalizeHead active (observed second primitive) atom := by
  unfold normalizeHead
  split
  next head left right rest =>
    have argsSafe : resourceFreeList (left :: right :: rest) = true := by
      simpa [resourceFree, resourceFreeList] using safe
    simp only [observed, observeList_resourceFree first _ argsSafe,
      observeList_resourceFree second _ argsSafe]
  next _ => rfl

mutual
/-- The exact normalized result, not merely its outer type, is unchanged
under every world view once each invoked primitive's output closure holds. -/
theorem normalize_world (active : String → Bool) (first second : ExternalView)
    (primitive : Primitive) (closed : ResultsClosed active primitive) : ∀ atom,
    resourceFree atom = true →
      normalize active (observed first primitive) atom =
        normalize active (observed second primitive) atom
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, safe => by
      rw [InertTypeDependencies.normalize, InertTypeDependencies.normalize]
      split
      · rfl
      · rw [normalizeList_world active first second primitive closed children safe]
        exact head_world active first second primitive _
          (normalizeList_preserves active (observed second primitive)
            (observed_closed active second primitive closed) children safe)
theorem normalizeList_world (active : String → Bool) (first second : ExternalView)
    (primitive : Primitive) (closed : ResultsClosed active primitive) : ∀ atoms,
    resourceFreeList atoms = true →
      normalizeList active (observed first primitive) atoms =
        normalizeList active (observed second primitive) atoms
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      rw [normalizeList, normalizeList, normalize_world active first second primitive closed atom safe.1,
        normalizeList_world active first second primitive closed atoms safe.2]
end

/-- Covers value/alpha comparisons without identifying their comparison
relations. Each comparison returns a Boolean even when its operands differ. -/
def booleanResult (compare : Atom → Atom → Bool) : List Atom → Option Atom
  | [left, right] => some (.grounded (.bool (compare left right)))
  | _ => none

theorem booleanResult_closed (compare : Atom → Atom → Bool) (args : List Atom)
    (result : Atom) (returned : booleanResult compare args = some result) : resourceFree result = true := by
  unfold booleanResult at returned
  split at returned
  · cases Option.some.inj returned
    rfl
  · contradiction

/-- `if-equal` uses alpha comparison in the native source. Closure depends
on selecting an existing operand, not on replacing alpha equality by value
equality. The comparison is therefore retained as its own parameter. -/
def chooseResult (compare : Atom → Atom → Bool) : List Atom → Option Atom
  | [left, right, yes, no] => some (if compare left right then yes else no)
  | _ => none

theorem chooseResult_closed (compare : Atom → Atom → Bool) (args : List Atom)
    (safe : resourceFreeList args = true) (result : Atom)
    (returned : chooseResult compare args = some result) : resourceFree result = true := by
  unfold chooseResult at returned
  split at returned
  · cases Option.some.inj returned
    simp only [resourceFreeList, Bool.and_eq_true] at safe
    split <;> simp_all
  · contradiction

namespace Controls

def equalOnly : Primitive := fun head args =>
  if head = "==" then booleanResult (· == ·) args else none

theorem equalOnly_closed : ResultsClosed (fun head => head == "==") equalOnly := by
  intro head args _ _ result returned
  unfold equalOnly at returned
  split at returned
  · exact booleanResult_closed _ args result returned
  · contradiction

def immutableExpression : Atom := .expression [.symbol "==", .grounded (.int 3), .grounded (.int 3)]

theorem active_comparison_runs (world : ExternalView) :
    normalize (fun head => head == "==") (observed world equalOnly) immutableExpression =
      .grounded (.bool true) := by
  simp [InertTypeDependencies.normalize, normalizeList, normalizeHead, observed, equalOnly, booleanResult,
    immutableExpression, observeList, RetainedTypePayloads.observe]

def mutableExpression : Atom := .expression [.symbol "==",
  RetainedTypePayloads.Controls.state "A", RetainedTypePayloads.Controls.state "B"]

theorem licensed_comparison_can_read_resources :
    normalize (fun head => head == "==") (observed RetainedTypePayloads.Controls.initial equalOnly)
        mutableExpression = .grounded (.bool true) ∧
    normalize (fun head => head == "==") (observed RetainedTypePayloads.Controls.changed equalOnly)
        mutableExpression = .grounded (.bool false) ∧
    resourceFree mutableExpression = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationScope
