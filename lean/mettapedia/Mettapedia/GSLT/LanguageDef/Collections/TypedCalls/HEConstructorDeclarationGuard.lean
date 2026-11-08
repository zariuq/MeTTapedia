import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownBuildCounterexample
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InertTypeDependencies

/-!
# What the constructor's declaration-only guard earns

The successful ordinary-row portion of the native same-head index guard
requires a nonempty chain containing only `(: head type)` rows. The complete
captured row packet determines that chain here. Dirty/open/headless flags,
index coverage, dependency visibility and revision validity remain separate
native representation obligations; this is not an assumption that one local
index covers every module read.

The guard excludes direct expression-subject typings at the reached head.
With one arrow row, the existing inference traversal can then return a
typing only after its actual argument checker succeeds. The resulting type
is normalization of the range under the reached substitution, not an assumed
copy of the written range. Interpretation and argument delivery are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorDeclarationGuard

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeViews

def subjectHead : Atom → Option String
  | .symbol head => some head
  | .expression (.symbol head :: _) => some head
  | _ => none

def belongs (head : String) : Atom → Bool
  | .expression [.symbol ":", subject, _] => subjectHead subject == some head
  | _ => false

def declares (head : String) : Atom → Bool
  | .expression [.symbol ":", .symbol subject, _] => subject == head
  | _ => false

def chain (rows : List Atom) (head : String) : List Atom := rows.filter (belongs head)

def accepts (rows : List Atom) (head : String) : Bool :=
  !(chain rows head).isEmpty && (chain rows head).all (declares head)

/-- Each relevant physical row is checked; duplicate declarations remain
duplicate occurrences rather than changing the guard's meaning. -/
theorem relevant_declares (rows : List Atom) (head : String) (accepted : accepts rows head = true)
    (row : Atom) (member : row ∈ rows) (relevant : belongs head row = true) : declares head row = true := by
  have checked := (Bool.and_eq_true_iff.mp accepted).2
  exact List.all_eq_true.mp checked row (List.mem_filter.mpr ⟨member, relevant⟩)

theorem no_expression_annotations (rows : List Atom) (head : String)
    (accepted : accepts rows head = true) (arguments : List Atom) :
    getAnnotatedTypes ⟨rows⟩ (.expression (.symbol head :: arguments)) = [] := by
  unfold getAnnotatedTypes
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨row, stored, returned⟩ := List.mem_filterMap.mp member
  split at returned
  next subject type_ =>
    split at returned
    next same =>
      have equal : subject = .expression (.symbol head :: arguments) := by simpa using same
      subst subject
      have checked := relevant_declares rows head accepted _ stored (by simp [belongs, subjectHead])
      simp [declares] at checked
    next _ => contradiction
  next _ => contradiction

/-- The source row walker itself, not a surrogate type checker: one admitted
arrow contributes a result exactly when its first-match argument loop succeeds. -/
theorem one_arrow_nonempty_iff {Value TypeAtom Bind Kind : Type}
    (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (values : List Value) (row range : TypeAtom) (formals : List TypeAtom)
    (arrow : ops.arrow row = some (formals, range)) :
    sourceRows ops reads values [row] ≠ [] ↔
      ∃ state, sourceArgs ops reads formals values ops.initial = some state := by
  simp only [sourceRows, arrow]
  cases checked : sourceArgs ops reads formals values ops.initial with
  | none => simp
  | some state => simp

theorem one_arrow_result {Value TypeAtom Bind Kind : Type}
    (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (values : List Value) (row range : TypeAtom) (formals : List TypeAtom) (state : Bind)
    (arrow : ops.arrow row = some (formals, range))
    (checked : sourceArgs ops reads formals values ops.initial = some state) :
    sourceRows ops reads values [row] = [ops.normalize (ops.apply state range)] := by
  simp only [sourceRows, arrow, checked]

theorem node_uses_own_arrow {Bind Kind : Type} (ops : Ops Atom Bind Kind) (reads : Reads Atom Atom Kind)
    (rows : List Atom) (head : String) (values : List Atom)
    (accepted : accepts rows head = true)
    (annotationRead : reads.annotations (.symbol head) values =
      getAnnotatedTypes ⟨rows⟩ (.expression (.symbol head :: values)))
    (ordinary : reads.classify (.symbol head) values = .ordinary)
    (row range : Atom) (formals : List Atom)
    (headRead : reads.headRows (.symbol head) = [row])
    (arrow : ops.arrow row = some (formals, range)) :
    sourceNode ops reads true (.symbol head) values = sourceRows ops reads values [row] := by
  simp only [sourceNode, ordinary, annotationRead, no_expression_annotations rows head accepted values,
    if_true, List.isEmpty_nil, headRead, List.any_cons, arrow, Option.isSome_some,
    Bool.true_or]

/-- This is the precise extra conclusion earned by the new declaration-only
guard. It proves post-build typing applicability, not earlier source delivery. -/
theorem positive_count_earns_argument_check {Bind Kind : Type}
    (ops : Ops Atom Bind Kind) (reads : Reads Atom Atom Kind)
    (rows : List Atom) (head : String) (values : List Atom)
    (accepted : accepts rows head = true)
    (annotationRead : reads.annotations (.symbol head) values =
      getAnnotatedTypes ⟨rows⟩ (.expression (.symbol head :: values)))
    (ordinary : reads.classify (.symbol head) values = .ordinary)
    (row range : Atom) (formals : List Atom)
    (headRead : reads.headRows (.symbol head) = [row])
    (arrow : ops.arrow row = some (formals, range))
    (positive : sourceNode ops reads true (.symbol head) values ≠ []) :
    ∃ state, sourceArgs ops reads formals values ops.initial = some state ∧
      sourceNode ops reads true (.symbol head) values = [ops.normalize (ops.apply state range)] := by
  have selected := node_uses_own_arrow ops reads rows head values accepted annotationRead ordinary row range formals headRead arrow
  rw [selected] at positive
  obtain ⟨state, checked⟩ := (one_arrow_nonempty_iff ops reads values row range formals arrow).mp positive
  exact ⟨state, checked, selected.trans (one_arrow_result ops reads values row range formals state arrow checked)⟩

/-- The existing structural query role ignores only top-level annotations;
unrelated metadata need not force the entire constructor off the fast path. -/
theorem structural_question_uses_arrow {Value TypeAtom Bind Kind : Type}
    (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (head : Value) (values : List Value) (row range : TypeAtom) (formals : List TypeAtom)
    (ordinary : reads.classify head values = .ordinary)
    (headRead : reads.headRows head = [row]) (arrow : ops.arrow row = some (formals, range)) :
    sourceNode ops reads false head values = sourceRows ops reads values [row] := by
  simp only [sourceNode, ordinary, Bool.false_eq_true, if_false, List.isEmpty_nil, if_true,
    headRead, List.any_cons, arrow, Option.isSome_some, Bool.true_or]

theorem structural_count_earns_argument_check {Value TypeAtom Bind Kind : Type}
    (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (head : Value) (values : List Value) (row range : TypeAtom) (formals : List TypeAtom)
    (ordinary : reads.classify head values = .ordinary)
    (headRead : reads.headRows head = [row]) (arrow : ops.arrow row = some (formals, range))
    (positive : sourceNode ops reads false head values ≠ []) :
    ∃ state, sourceArgs ops reads formals values ops.initial = some state ∧
      sourceNode ops reads false head values = [ops.normalize (ops.apply state range)] := by
  have selected := structural_question_uses_arrow ops reads head values row range formals ordinary headRead arrow
  rw [selected] at positive
  obtain ⟨state, checked⟩ := (one_arrow_nonempty_iff ops reads values row range formals arrow).mp positive
  exact ⟨state, checked, selected.trans (one_arrow_result ops reads values row range formals state arrow checked)⟩

namespace Controls

open HEShownBuildCounterexample

theorem ordinary_open_constructor_admitted :
    accepts [declaration (.symbol "OpenShownBox") signature] "OpenShownBox" = true := by decide

theorem expression_row_refuses_even_the_owed_range :
    accepts selfAnnotatedSource.atoms "OpenShownBox" = false := by decide

theorem expression_row_refuses_unrelated_typing : accepts source.atoms "OpenShownBox" = false := by decide

theorem unrelated_head_annotation_does_not_refuse :
    accepts [declaration (.symbol "OpenShownBox") signature,
      declaration (.expression [.symbol "OtherBox", .grounded (.int 7)]) range] "OpenShownBox" = true := by decide

theorem duplicate_declarations_are_not_erased :
    let rows := [declaration (.symbol "OpenShownBox") signature, declaration (.symbol "OpenShownBox") signature]
    accepts rows "OpenShownBox" = true ∧ (chain rows "OpenShownBox").length = 2 := by decide

theorem local_packet_is_not_an_import_closure :
    let own := [declaration (.symbol "OpenShownBox") signature]
    let imported := [declaration built range]
    accepts own "OpenShownBox" = true ∧ accepts (own ++ imported) "OpenShownBox" = false := by decide

/-- The source checks the constructor at top level too. A caller wrapper
is not what creates the argument obligation. -/
theorem direct_bad_constructor_is_rejected_by_source :
    evalAtom selfAnnotatedSource GroundedDispatch.none built Atom.undefinedType Bindings.empty 128 =
      [(sourceError, Bindings.empty)] := by decide +kernel

def sourceOps : Ops Atom TypeScopeMatcher.State Atom :=
  TypeScopeMatcher.ops (fun tag key => .grounded (.custom tag key))
    (InertTypeDependencies.normalize (fun _ => false) (fun _ _ => none)) (fun _ => [])

def sourceReads : Reads Atom Atom Atom where
  classify _ _ := .ordinary
  annotations head args := getAnnotatedTypes selfAnnotatedSource (.expression (head :: args))
  headRows := getAtomTypes selfAnnotatedSource
  tupleHead := getAtomTypes selfAnnotatedSource
  kind := getMetaType
  inferred := getAtomTypes selfAnnotatedSource
  tuplePart := getAtomTypes selfAnnotatedSource

/-- The two real query roles differ even with one shared open signature.
The actual unifier rejects Number/String against the same formal variable. -/
theorem annotation_count_and_structural_count_differ :
    sourceNode sourceOps sourceReads true (.symbol "OpenShownBox")
      [.grounded (.int 1), .grounded (.string "wrong-field")] = [range] ∧
    sourceNode sourceOps sourceReads false (.symbol "OpenShownBox")
      [.grounded (.int 1), .grounded (.string "wrong-field")] = [] := by cbv

theorem structural_role_keeps_valid_shared_formals :
    sourceNode sourceOps sourceReads false (.symbol "OpenShownBox")
      [.grounded (.int 1), .grounded (.int 2)] = [range] := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorDeclarationGuard
