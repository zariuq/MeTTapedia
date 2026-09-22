import Mettapedia.TypeTheory.ContextualBindingConflict
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Ground refinement as a categorical common extension

Objects are the existing partial ground stores. An arrow adds information
without changing any known binding. The ambient category includes arbitrary
such extensions; finite runs select particular arrows in it. With this
orientation a successful binding
is a coproduct: it is the least common extension of the incoming store and the
proposed assignment. Equivalently, its set of possible further extensions is
the intersection of their extension sets. A conflicting pair has no cocone.

The colimit witness is constructed from the actual `refineStep`/`refineRun`,
not from an assumed universal-property contract. Completion is a functor on
the compatible-input domain. Arbitrary stronger input need not remain in that
domain: extra information can expose an incompatibility.

These laws concern repeated occurrences of the same logical store name and
information-preserving refinement. They neither forbid separate lexical
binders nor identify failure with silence, an empty value, or an unhandled
exception. A rejection handler can retain the input context while the proposed
conjunction remains unsatisfied. Non-ground term unification and most-general
substitution factorization are separate structures, not claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GroundBindingCategory

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open CategoryTheory CategoryTheory.Limits

universe u v
variable {N : Type u} {V : Type v}

/-- A wrapper avoids confusing information order with any order on values. -/
structure Context (N : Type u) (V : Type v) where
  store : Store N V

theorem store_antisymm {s t : Store N V} (forward : Store.LE s t)
    (backward : Store.LE t s) : s = t := by
  funext name
  cases hs : s name with
  | none =>
      cases ht : t name with
      | none => rfl
      | some value => have impossible := backward name value ht; rw [hs] at impossible; cases impossible
  | some value => exact (forward name value hs).symm

instance : PartialOrder (Context N V) where
  le s t := Store.LE s.store t.store
  le_refl s := Store.LE.refl s.store
  le_trans _ _ _ := Store.LE.trans
  le_antisymm s t forward backward := by
    cases s
    cases t
    congr
    exact store_antisymm forward backward

/-- The full constraint asserted by a finite list, independent of evaluation. -/
def Satisfies (store : Store N V) (steps : Steps N V) : Prop :=
  ∀ proposal ∈ steps, store proposal.1 = some proposal.2

/-- All future ground stores compatible with a given partial context. -/
def extensions (context : Context N V) : Set (Context N V) := { future | context ≤ future }

variable [DecidableEq N] [DecidableEq V]

def assignment (proposal : N × V) : Context N V :=
  ⟨fun name => if name = proposal.1 then some proposal.2 else none⟩

omit [DecidableEq V] in
theorem assignment_le_iff (proposal : N × V) (context : Context N V) :
    assignment proposal ≤ context ↔ context.store proposal.1 = some proposal.2 := by
  constructor
  · intro extensionMap
    exact extensionMap proposal.1 proposal.2 (by simp [assignment])
  · intro bound name value lookup
    by_cases same : name = proposal.1
    · subst name
      have sameValue : proposal.2 = value := by simpa [assignment] using lookup
      cases sameValue
      exact bound
    · simp [assignment, same] at lookup

/-- The actual successful step adds no information beyond what is required
by its input and proposal. -/
theorem refineStep_least {s t future : Store N V} {proposal : N × V}
    (accepted : refineStep s proposal = some t)
    (prior : Store.LE s future) (bound : future proposal.1 = some proposal.2) :
    Store.LE t future := by
  unfold refineStep at accepted
  cases lookup : s proposal.1 with
  | none =>
      rw [lookup] at accepted
      cases accepted
      intro name value found
      by_cases same : name = proposal.1
      · subst name
        have sameValue : proposal.2 = value := by simpa using found
        cases sameValue
        exact bound
      · simp only [if_neg same] at found
        exact prior name value found
  | some old =>
      rw [lookup] at accepted
      by_cases equal : old = proposal.2
      · simp only [if_pos equal, Option.some.injEq] at accepted
        cases accepted
        exact prior
      · simp [equal] at accepted

/-- Exact universal common-extension law for the computed sequential result. -/
theorem refineRun_le_iff {s t future : Store N V} {steps : Steps N V}
    (accepted : refineRun s steps = some t) :
    Store.LE t future ↔ Store.LE s future ∧ Satisfies future steps := by
  constructor
  · intro extensionMap
    exact ⟨(refineRun_mono accepted).trans extensionMap,
      fun proposal member => extensionMap _ _ (refineRun_asserts accepted proposal member)⟩
  · rintro ⟨prior, satisfies⟩
    induction steps generalizing s with
    | nil =>
        cases accepted
        exact prior
    | cons proposal rest ih =>
        cases step : refineStep s proposal with
        | none => simp [refineRun, step] at accepted
        | some middle =>
            have follows : refineRun middle rest = some t := by
              simpa only [refineRun, step] using accepted
            exact ih follows
              (refineStep_least step prior (satisfies proposal List.mem_cons_self))
              (fun p member => satisfies p (List.mem_cons_of_mem proposal member))

/-- Successful computation exists exactly when the input and all proposals
have a common information-preserving extension. -/
theorem refineRun_success_iff (s : Store N V) (steps : Steps N V) :
    (∃ t, refineRun s steps = some t) ↔
      ∃ future, Store.LE s future ∧ Satisfies future steps := by
  constructor
  · rintro ⟨t, accepted⟩
    exact ⟨t, refineRun_mono accepted, refineRun_asserts accepted⟩
  · rintro ⟨future, prior, satisfies⟩
    have consistent : Consistent steps := by
      intro p hp q hq same
      have first := satisfies p hp
      have second := satisfies q hq
      rw [same] at first
      exact Option.some.inj (first.symm.trans second)
    have compatible : ∀ p ∈ steps, ∀ value, s p.1 = some value → value = p.2 := by
      intro p hp value lookup
      exact Option.some.inj ((prior _ _ lookup).symm.trans (satisfies p hp))
    obtain ⟨t, accepted, _, _⟩ := refineRun_of_consistent consistent s compatible
    exact ⟨t, accepted⟩

theorem refineRun_failure_iff (s : Store N V) (steps : Steps N V) :
    refineRun s steps = none ↔
      ¬ ∃ future, Store.LE s future ∧ Satisfies future steps := by
  rw [← refineRun_success_iff]
  cases refineRun s steps <;> simp

/-- A computed step supplies the two genuine refinement arrows. -/
def stepCofan {s t : Store N V} {proposal : N × V}
    (accepted : refineStep s proposal = some t) :
    BinaryCofan (Context.mk s) (assignment proposal) :=
  BinaryCofan.mk (P := Context.mk t) (homOfLE (refineStep_mono accepted))
    (homOfLE ((assignment_le_iff proposal ⟨t⟩).mpr (refineStep_binds accepted)))

/-- Binding computes a categorical coproduct whenever it succeeds. -/
def step_isColimit {s t : Store N V} {proposal : N × V}
    (accepted : refineStep s proposal = some t) : IsColimit (stepCofan accepted) := by
  refine BinaryCofan.IsColimit.mk _
    (fun {future} left right => homOfLE (show Context.mk t ≤ future from
      refineStep_least accepted (leOfHom left)
        ((assignment_le_iff proposal future).mp (leOfHom right)))) ?_ ?_ ?_
  all_goals intros; exact Subsingleton.elim _ _

/-- Sequential conjunction gives the common extension of the initial store
and the separately computed conjunction of its proposals. -/
def runCofan {s conjunction result : Store N V} {steps : Steps N V}
    (solved : refineRun Store.empty steps = some conjunction)
    (accepted : refineRun s steps = some result) :
    BinaryCofan (Context.mk s) (Context.mk conjunction) :=
  BinaryCofan.mk (P := Context.mk result) (homOfLE (refineRun_mono accepted))
    (homOfLE ((refineRun_le_iff solved).mpr
      ⟨(by intro name value impossible; cases impossible), refineRun_asserts accepted⟩))

def run_isColimit {s conjunction result : Store N V} {steps : Steps N V}
    (solved : refineRun Store.empty steps = some conjunction)
    (accepted : refineRun s steps = some result) :
    IsColimit (runCofan solved accepted) := by
  refine BinaryCofan.IsColimit.mk _
    (fun {future} left right => homOfLE (show Context.mk result ≤ future from
      (refineRun_le_iff accepted).mpr
        ⟨leOfHom left, ((refineRun_le_iff solved).mp (leOfHom right)).2⟩)) ?_ ?_ ?_
  all_goals intros; exact Subsingleton.elim _ _

/-- With arrows oriented toward more information, joining constraints
intersects their sets of future extensions. -/
theorem completion_extensions_intersection
    {s conjunction result : Store N V} {steps : Steps N V}
    (solved : refineRun Store.empty steps = some conjunction)
    (accepted : refineRun s steps = some result) :
    extensions (Context.mk result) =
      extensions (Context.mk s) ∩ extensions (Context.mk conjunction) := by
  ext future
  change Store.LE result future.store ↔
    Store.LE s future.store ∧ Store.LE conjunction future.store
  rw [refineRun_le_iff accepted, refineRun_le_iff solved]
  have emptyExtends : Store.LE (Store.empty : Store N V) future.store :=
    fun _ _ impossible => by cases impossible
  simp only [emptyExtends, true_and]

omit [DecidableEq V] in
/-- Incompatibility excludes every cocone, not just this algorithm's output. -/
theorem conflicting_assignments_no_cocone (name : N) (old proposed : V)
    (different : old ≠ proposed) :
    ¬ Nonempty (BinaryCofan (assignment (name, old)) (assignment (name, proposed))) := by
  rintro ⟨cocone⟩
  have first := (assignment_le_iff (name, old) cocone.pt).mp (leOfHom cocone.inl)
  have second := (assignment_le_iff (name, proposed) cocone.pt).mp (leOfHom cocone.inr)
  exact different (Option.some.inj (first.symm.trans second))

/-! ## Completion is functorial on the successful-input domain -/

abbrev Successful (steps : Steps N V) :=
  { context : Context N V // ∃ output, refineRun context.store steps = some output }

def completed {steps : Steps N V} (input : Successful steps) : Context N V :=
  ⟨(refineRun input.val.store steps).get (Option.isSome_iff_exists.mpr input.property)⟩

theorem completed_spec {steps : Steps N V} (input : Successful steps) :
    refineRun input.val.store steps = some (completed input).store :=
  Option.eq_some_of_isSome _

theorem completion_mono {steps : Steps N V} {left right : Successful steps}
    (prior : left ≤ right) : completed left ≤ completed right :=
  (refineRun_le_iff (completed_spec left)).mpr
    ⟨Store.LE.trans prior (refineRun_mono (completed_spec right)),
      refineRun_asserts (completed_spec right)⟩

def completionFunctor (steps : Steps N V) : Successful steps ⥤ Context N V where
  obj := completed
  map arrow := homOfLE (completion_mono (leOfHom arrow))

def inputFunctor (steps : Steps N V) : Successful steps ⥤ Context N V where
  obj := Subtype.val
  map arrow := homOfLE (leOfHom arrow)

/-- Refining before or after mapping compatible inputs gives the same
information-preserving arrow. This is naturality of actual completion. -/
def completionUnit (steps : Steps N V) :
    inputFunctor steps ⟶ completionFunctor steps where
  app input := homOfLE (refineRun_mono (completed_spec input))

/-- Success on a stronger input implies success on a weaker input; the
converse is deliberately absent because stronger input can conflict. -/
theorem compatible_input_downward {s stronger : Store N V} {steps : Steps N V}
    (prior : Store.LE s stronger) (success : ∃ output, refineRun stronger steps = some output) :
    ∃ output, refineRun s steps = some output := by
  obtain ⟨output, accepted⟩ := success
  exact (refineRun_success_iff s steps).mpr
    ⟨output, prior.trans (refineRun_mono accepted), refineRun_asserts accepted⟩

namespace Controls

def start : Store String String := ContextualBindingConflict.exampleStore
def extension : Store String String :=
  fun name => if name = "y" then some "b" else start name

theorem distinct_new_binding_colimit :
    refineStep start ("y", "b") = some extension ∧
      Nonempty (IsColimit (stepCofan (s := start) (t := extension)
        (proposal := ("y", "b")) (by rfl))) :=
  ⟨rfl, ⟨step_isColimit (by rfl)⟩⟩

theorem no_arrow_back : ¬ Nonempty (Context.mk extension ⟶ Context.mk start) := by
  rintro ⟨arrow⟩
  have impossible := leOfHom arrow "y" "b" (by rfl)
  cases impossible

theorem stronger_input_can_destroy_success :
    Store.LE (Store.empty : Store String String) start ∧
      (∃ output, refineRun (Store.empty : Store String String) [("x", "b")] = some output) ∧
      refineRun start [("x", "b")] = none := by
  exact ⟨(fun _ _ impossible => by cases impossible), ⟨_, rfl⟩, rfl⟩

/-- The no-cocone theorem coexists with useful recovery. It does not choose
silence or forbid an exception or explicit rejection continuation. -/
theorem rejection_does_not_determine_handler :
    ¬ Nonempty (BinaryCofan (assignment ("x", "a")) (assignment ("x", "b"))) ∧
    (ContextualBindingConflict.tryBind start ("x", "b")).acceptedStore = none ∧
    (ContextualBindingConflict.tryBind start ("x", "b")).handle
      (fun store => store "x") (fun store _ _ _ => store "x") = some "a" := by
  exact ⟨conflicting_assignments_no_cocone "x" "a" "b" (by decide), rfl, rfl⟩

/-- Identical rejection and successful-answer projection permit distinct
public observations. Neither the coproduct law nor absence of its cocone
chooses between these two handlers. -/
theorem silent_and_reporting_handlers_differ :
    (ContextualBindingConflict.tryBind start ("x", "b")).acceptedStore = none ∧
    (ContextualBindingConflict.tryBind start ("x", "b")).handle
      (fun _ => ([] : List String)) (fun _ _ _ _ => []) = [] ∧
    (ContextualBindingConflict.tryBind start ("x", "b")).handle
      (fun _ => ([] : List String)) (fun _ _ _ _ => ["conflict"]) = ["conflict"] ∧
    ([] : List String) ≠ ["conflict"] := by
  exact ⟨rfl, rfl, rfl, by intro impossible; cases impossible⟩

end Controls

#print axioms refineRun_le_iff
#print axioms refineRun_success_iff
#print axioms step_isColimit
#print axioms run_isColimit
#print axioms completion_extensions_intersection
#print axioms conflicting_assignments_no_cocone
#print axioms completion_mono
#print axioms completionUnit
#print axioms Controls.distinct_new_binding_colimit
#print axioms Controls.no_arrow_back
#print axioms Controls.stronger_input_can_destroy_success
#print axioms Controls.rejection_does_not_determine_handler
#print axioms Controls.silent_and_reporting_handlers_differ

end Mettapedia.TypeTheory.GroundBindingCategory
