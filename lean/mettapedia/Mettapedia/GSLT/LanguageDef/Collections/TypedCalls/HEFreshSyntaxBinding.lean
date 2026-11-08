import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeFrame

/-!
# Fresh bindings retain complete annotated branch values

Source equation matching binds branch syntax, not merely its bare erasure.
The existing contextual binding operation and source certificate are used
directly, so nested evaluation marks survive capture in a fresh variable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation

theorem resolve_fresh (before : Frame) (name : String) (fresh : name ∉ specBindingVars before.bindings) :
    Entry.Value.resolve before.environment name = .var name :=
  Entry.Value.resolve_of_not_mem_keys before.environment name
    (TypeSubst.not_mem_keys_of_lookup_eq_none (before.certified.lookup_none_of_outside fresh))

def bindFrame (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (absent : name ∉ TypeSubst.typeVars value.erase) : Frame :=
  ⟨before.bindings.assign name value.erase,
   Entry.Value.bind policy.rebuilding before.environment name value, by
     rw [Entry.Value.erase_bind]
     exact before.certified.fresh_assignment name value.erase fresh absent⟩

theorem ground_substitution (policy : Entry.RebuildPolicy) (environment : String → Entry.Value)
    (value : Entry.Value) (closed : TypeSubst.typeVars value.erase = []) :
    Entry.Value.substitute policy environment value = value := by
  apply Entry.Value.substitute_variable_free
  intro name occurs
  have member := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
  simp only [closed, List.not_mem_nil] at member

theorem ground_nonvariable (value : Entry.Value) (closed : TypeSubst.typeVars value.erase = []) :
    ∀ name, value.erase ≠ .var name := by
  intro name same
  rw [same] at closed
  simp [TypeSubst.typeVars] at closed

theorem source_binding (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (closed : TypeSubst.typeVars value.erase = []) :
    Entry.Value.UnifyRel policy.rebuilding before.environment value (.var name)
      (bindFrame policy before name value fresh (by simp [closed])).environment := by
  apply Entry.Value.UnifyRel.ordinary
  rw [ground_substitution policy.rebuilding _ value closed]
  simp only [Entry.Value.substitute, resolve_fresh before name fresh]
  exact Entry.Value.AppliedUnifyRel.bindRight (ground_nonvariable value closed) (by simp [closed])

/-- The entire stored value is returned, including every nested mark. -/
theorem bound_read (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (closed : TypeSubst.typeVars value.erase = [])
    (readingPolicy : Policy) :
    (bindFrame policy before name value fresh (by simp [closed])).read readingPolicy (.var name) = value := by
  simp only [bindFrame, Frame.read, Entry.Value.substitute, Entry.Value.bind, Entry.Value.resolve,
    List.lookup_cons, beq_self_eq_true, Option.getD_some]
  exact ground_substitution policy.rebuilding _ value closed

theorem binding_keeps_caller (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (absent : name ∉ TypeSubst.typeVars value.erase) :
    (bindFrame policy before name value fresh absent).bindings =
      HEFreshRangeFrame.extend before.bindings name value.erase :=
  HEFreshRangeFrame.assign_eq_extend before.bindings name value.erase fresh

theorem other_stays_fresh (policy : Policy) (before : Frame) (left right : String) (value : Entry.Value)
    (fresh : left ∉ specBindingVars before.bindings) (other : right ∉ specBindingVars before.bindings)
    (different : right ≠ left) (closed : TypeSubst.typeVars value.erase = []) :
    right ∉ specBindingVars (bindFrame policy before left value fresh (by simp [closed])).bindings := by
  rw [binding_keeps_caller]
  simpa [HEFreshRangeFrame.extend, specBindingVars, closed, and_assoc, and_left_comm, and_comm]
    using And.intro other different

theorem prior_binding_read (policy : Policy) (before : Frame) (left right : String) (yes no : Entry.Value)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (different : right ≠ left) (yesClosed : TypeSubst.typeVars yes.erase = [])
    (noClosed : TypeSubst.typeVars no.erase = []) (readingPolicy : Policy) :
    let middle := bindFrame policy before left yes leftFresh (by simp [yesClosed])
    let after := bindFrame policy middle right no
      (other_stays_fresh policy before left right yes leftFresh rightFresh different yesClosed) (by simp [noClosed])
    after.read readingPolicy (.var left) = yes := by
  dsimp only
  simp only [bindFrame, Frame.read, Entry.Value.substitute, Entry.Value.bind]
  rw [ground_substitution policy.rebuilding _ no noClosed,
    ground_substitution policy.rebuilding _ yes yesClosed]
  have reverse : left ≠ right := Ne.symm different
  have comparison : (left == right) = false := by simp [reverse]
  simp only [Entry.Value.resolve, List.lookup_cons, List.filter_cons]
  rw [comparison]
  simp only [bne_iff_ne]
  rw [if_pos reverse]
  simp only [List.map_cons, List.lookup_cons, beq_self_eq_true, Option.getD_some]
  exact ground_substitution policy.rebuilding _ yes yesClosed

/-- Matching an actual conditional call with its two fresh parameter slots
retains both full branch values. The trace is built from the existing bind
and unification rules, with a certificate for each reached source record. -/
theorem conditional_parameters (policy : Policy) (before : Frame) (left right : String)
    (yes no : Entry.Value) (condition : Bool)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (different : right ≠ left) (yesClosed : TypeSubst.typeVars yes.erase = [])
    (noClosed : TypeSubst.typeVars no.erase = []) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (.expression .active [.symbol "if", .grounded (.bool condition), yes, no])
        (Entry.Value.ofAtom (.expression [.symbol "if", .grounded (.bool condition), .var left, .var right]))
        after.environment ∧
      (∀ readingPolicy, after.read readingPolicy (.var left) = yes ∧ after.read readingPolicy (.var right) = no) ∧
      after.bindings = (before.bindings.assign left yes.erase).assign right no.erase := by
  let middle := bindFrame policy before left yes leftFresh (by simp [yesClosed])
  have rightStillFresh : right ∉ specBindingVars middle.bindings :=
    other_stays_fresh policy before left right yes leftFresh rightFresh different yesClosed
  let after := bindFrame policy middle right no rightStillFresh (by simp [noClosed])
  have first := source_binding policy before left yes leftFresh yesClosed
  have second := source_binding policy middle right no rightStillFresh noClosed
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment
      (.expression .active [.symbol "if", .grounded (.bool condition), yes, no])
      (Entry.Value.ofAtom (.expression [.symbol "if", .grounded (.bool condition), .var left, .var right]))
      after.environment := by
    apply Entry.Value.UnifyRel.ordinary
    simp only [Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.substitute,
      resolve_fresh before left leftFresh, resolve_fresh before right rightFresh,
      ground_substitution policy.rebuilding _ yes yesClosed,
      ground_substitution policy.rebuilding _ no noClosed,
      HEFreshEquationFrames.Range.active_rebuild]
    exact .expression (.cons (.ordinary (.identical (by simp [Entry.Value.substitute])))
      (.cons (.ordinary (.identical (by simp [Entry.Value.substitute])))
        (.cons first (.cons second (.nil _)))))
  refine ⟨after, unified, ?_, rfl⟩
  intro readingPolicy
  exact ⟨prior_binding_read policy before left right yes no leftFresh rightFresh different yesClosed noClosed readingPolicy,
    bound_read policy middle right no rightStillFresh noClosed readingPolicy⟩

namespace Controls

def branch : Entry.Value := .expression .held
  [.symbol "Keep", .expression .held [.symbol "Box", .grounded (.int 7)]]

theorem retained_branch_marks (policy readingPolicy : Policy) :
    (bindFrame policy Frame.empty "branch" branch (by simp [Frame.empty, specBindingVars, Bindings.empty])
      (by simp [branch, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])).read
      readingPolicy (.var "branch") = branch :=
  bound_read policy Frame.empty "branch" branch _
    (by simp [branch, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]) readingPolicy

theorem erasing_branch_marks_changes_the_value :
    Entry.Value.ofAtom branch.erase ≠ branch := by
  simp [branch, Entry.Value.ofAtom, Entry.Value.erase]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding
