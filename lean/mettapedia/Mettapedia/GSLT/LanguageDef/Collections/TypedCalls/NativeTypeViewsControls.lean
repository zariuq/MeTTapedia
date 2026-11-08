import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Native type-view counterexamples and corrected descriptors

These fixtures use the full Atom carrier and the actual annotation reader.
Their child values are symbols or scalar leaves. The single subtype edge has
one closure round; there is no claim that this fixture implements general
subtype inference. Both key failures also have executable native probes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViewsControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeViews

def sym (s : String) : Atom := .symbol s
def expr (xs : List Atom) : Atom := .expression xs
def annotation (name : String) (type_ : Atom) : Atom := expr [sym ":", sym name, type_]

def arrowView (type_ : Atom) : Option (List Atom × Atom) :=
  if isFunctionType type_ then
    (getFunctionArgTypes type_).bind fun params => (getFunctionRetType type_).map (params, ·)
  else none

def metaCheck (formal kind : Atom) : Option Bool :=
  if formal == Atom.atomType then some true
  else if formal == Atom.symbolType || formal == Atom.variableType || formal == Atom.groundedType ||
      formal == Atom.expressionType then some (formal == kind)
  else none

/-- The actual ground subtype rows of these fixtures. -/
def directSupers (space : Space) (type_ : Atom) : List Atom :=
  space.atoms.filterMap fun row => match row with
    | .expression [.symbol ":<", source, target] => if source == type_ then some target else none
    | _ => none

/-- One round is complete for the only fixture edge, A <: B. It preserves
the native round's duplicate-occurrence policy. -/
def additions (space : Space) (types : List Atom) : List Atom :=
  types.flatMap fun type_ => (directSupers space type_).filter fun target => !types.contains target

/-- Closed declarations in the fixtures need no variable-binding store. The
generic theorem itself supports an arbitrary binding-state carrier. -/
def ops (space : Space) : Ops Atom Unit Atom where
  arrow := arrowView
  initial := ()
  apply := fun _ type_ => type_
  unify := fun _ actual expected =>
    if actual == expected || actual == Atom.undefinedType || expected == Atom.undefinedType then some () else none
  metaCheck := metaCheck
  normalize := id
  tuple := Atom.expression
  undefined := Atom.undefinedType
  nativeMork := sym "MorkSpace"
  listType := sym "List"
  subtypeAdditions := additions space

def classify (head : Atom) (args : List Atom) : HeadClass :=
  if head == sym "NativeHandle" then
    match args with
    | [kind, _] =>
        if kind == sym "mork-space" || kind == .grounded (.string "mork-space") then .nativeMork
        else .ordinary
    | _ => .ordinary
  else .ordinary

def keepTuple (atHead : Bool) (type_ : Atom) : Bool :=
  type_ != Atom.undefinedType && (!atHead || !isFunctionType type_)

/-- Question-qualified reads for the symbol/scalar children used below.
Symbol inference includes supertypes; its tuple-part read does not. -/
def reads (space : Space) : Reads Atom Atom Atom where
  classify := classify
  annotations := fun head args => getAnnotatedTypes space (expr (head :: args))
  headRows := getAnnotatedTypes space
  tupleHead := fun head => (getAnnotatedTypes space head).filter (keepTuple true)
  kind := getMetaType
  inferred := fun value => (ops space).close (getAtomTypes space value)
  tuplePart := fun value =>
    (match value with
      | .symbol _ => getAnnotatedTypes space value
      | .grounded g => [getGroundedType g]
      | _ => getAtomTypes space value).filter (keepTuple false)

/-- The information retained by the old transition key, with arity implicit
in the list length and one fixed scope in each control. -/
def coarse (view : Descriptor Atom Atom Atom) : Atom × Bool × List (Atom × List Atom) :=
  (view.head, view.question, view.children.map fun child => (child.kind, child.inferred))

def subtypeSpace : Space := Space.ofList
  [annotation "h" (sym "H"), annotation "x" (sym "A"), annotation "y" (sym "A"),
   annotation "y" (sym "B"), expr [sym ":<", sym "A", sym "B"]]

def subtypeLeft := descriptor (reads subtypeSpace) true (sym "h") [sym "x"]
def subtypeRight := descriptor (reads subtypeSpace) true (sym "h") [sym "y"]

theorem subtype_same_old_key : coarse subtypeLeft = coarse subtypeRight := by cbv

theorem subtype_raw_tuple_answers :
    sourceNode (ops subtypeSpace) (reads subtypeSpace) true (sym "h") [sym "x"] =
      [expr [sym "H", sym "A"]] ∧
    sourceNode (ops subtypeSpace) (reads subtypeSpace) true (sym "h") [sym "y"] =
      [expr [sym "H", sym "A"], expr [sym "H", sym "B"]] := by cbv

theorem subtype_refined_views_differ : subtypeLeft ≠ subtypeRight := by decide +kernel

/-- No computation from the old key can produce both correct tuple results. -/
theorem subtype_no_coarse_factorization :
    ¬ ∃ compute : (Atom × Bool × List (Atom × List Atom)) → List Atom,
      ∀ value, compute (coarse (descriptor (reads subtypeSpace) true (sym "h") [value])) =
        sourceNode (ops subtypeSpace) (reads subtypeSpace) true (sym "h") [value] := by
  rintro ⟨compute, correct⟩
  have same := congrArg compute subtype_same_old_key
  change compute (coarse (descriptor (reads subtypeSpace) true (sym "h") [sym "x"])) =
    compute (coarse (descriptor (reads subtypeSpace) true (sym "h") [sym "y"])) at same
  rw [correct, correct, subtype_raw_tuple_answers.1, subtype_raw_tuple_answers.2] at same
  have lengths := congrArg List.length same
  simp at lengths

def handleSpace : Space := Space.ofList
  [annotation "NativeHandle" (sym "H"), annotation "mork-space" (sym "K"), annotation "other" (sym "K")]

def zero : Atom := .grounded (.int 0)
def handleLeft := descriptor (reads handleSpace) true (sym "NativeHandle") [sym "mork-space", zero]
def handleRight := descriptor (reads handleSpace) true (sym "NativeHandle") [sym "other", zero]

theorem handle_same_old_key : coarse handleLeft = coarse handleRight := by cbv

theorem handle_literal_answers :
    sourceNode (ops handleSpace) (reads handleSpace) true (sym "NativeHandle") [sym "mork-space", zero] =
      [sym "MorkSpace"] ∧
    sourceNode (ops handleSpace) (reads handleSpace) true (sym "NativeHandle") [sym "other", zero] =
      [expr [sym "H", sym "K", sym "Number"]] := by cbv

theorem handle_refined_views_differ : handleLeft ≠ handleRight := by decide +kernel

theorem handle_no_coarse_factorization :
    ¬ ∃ compute : (Atom × Bool × List (Atom × List Atom)) → List Atom,
      ∀ kind, compute (coarse (descriptor (reads handleSpace) true (sym "NativeHandle") [kind, zero])) =
        sourceNode (ops handleSpace) (reads handleSpace) true (sym "NativeHandle") [kind, zero] := by
  rintro ⟨compute, correct⟩
  have same := congrArg compute handle_same_old_key
  change compute (coarse (descriptor (reads handleSpace) true (sym "NativeHandle") [sym "mork-space", zero])) =
    compute (coarse (descriptor (reads handleSpace) true (sym "NativeHandle") [sym "other", zero])) at same
  rw [correct, correct, handle_literal_answers.1, handle_literal_answers.2] at same
  cases same

/-- The refined transition distinguishes both pairs and produces the
independently computed source answers. -/
theorem refined_transitions_correct :
    transition (ops subtypeSpace) subtypeLeft = [expr [sym "H", sym "A"]] ∧
    transition (ops subtypeSpace) subtypeRight = [expr [sym "H", sym "A"], expr [sym "H", sym "B"]] ∧
    transition (ops handleSpace) handleLeft = [sym "MorkSpace"] ∧
    transition (ops handleSpace) handleRight = [expr [sym "H", sym "K", sym "Number"]] := by
  change transition _ (descriptor _ _ _ _) = _ ∧ transition _ (descriptor _ _ _ _) = _ ∧
    transition _ (descriptor _ _ _ _) = _ ∧ transition _ (descriptor _ _ _ _) = _
  simp only [← node_factor]
  exact ⟨subtype_raw_tuple_answers.1, subtype_raw_tuple_answers.2,
    handle_literal_answers.1, handle_literal_answers.2⟩

def duplicateRowsSpace : Space := Space.ofList
  [annotation "f" (expr [sym "->", Atom.atomType, sym "R"]),
   annotation "f" (expr [sym "->", Atom.atomType, sym "S"]),
   annotation "f" (expr [sym "->", Atom.atomType, sym "R"])]

/-- No set conversion or sorting is hidden in the native-shaped driver. -/
theorem arrow_row_order_and_multiplicity :
    sourceNode (ops duplicateRowsSpace) (reads duplicateRowsSpace) true (sym "f") [zero] =
      [sym "R", sym "S", sym "R"] ∧
    transition (ops duplicateRowsSpace)
      (descriptor (reads duplicateRowsSpace) true (sym "f") [zero]) =
      [sym "R", sym "S", sym "R"] := by cbv

def heldSpace : Space := Space.ofList
  [annotation "f" (expr [sym "->", Atom.atomType, expr [sym "VecN", sym "Number", .grounded (.int 7)]])]

def heldView := descriptor (reads heldSpace) true (sym "f") [sym "unknown"]

def missingUnused : Available Atom Atom Atom :=
  ⟨heldView.header, [⟨Atom.symbolType, none, none⟩]⟩

theorem held_source_needs_no_child_type :
    sourceNode (ops heldSpace) (reads heldSpace) true (sym "f") [sym "unknown"] =
      [expr [sym "VecN", sym "Number", .grounded (.int 7)]] := by cbv

theorem missing_view_is_a_miss : missingUnused.complete = none := rfl

/-- Missing cache observations do not turn this source call into failure. -/
theorem missing_unused_view_keeps_source_result :
    runAvailable (ops heldSpace) (reads heldSpace) true (sym "f") [sym "unknown"] missingUnused =
      [expr [sym "VecN", sym "Number", .grounded (.int 7)]] := by cbv

open Mettapedia.Machines.ReadOnlyQuery in
/-- A suspended unused lookup blocks an eager construction but not a source
branch that never reads it. This is a read-protocol control, not a claim of a
third native regression. -/
theorem eagerly_forcing_unused_query_changes_completion :
    (run (fun _ : Unit => (none : Option (List Atom)))
      (.pure (some [sym "R"]) : Program Unit (Option (List Atom)) (Option (List Atom)))).answer = some [sym "R"] ∧
    (run (fun _ : Unit => (none : Option (List Atom)))
      (.read () (fun answer => .pure (answer.map fun _ => [sym "R"])) :
        Program Unit (Option (List Atom)) (Option (List Atom)))).answer = none := by
  constructor <;> rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViewsControls
