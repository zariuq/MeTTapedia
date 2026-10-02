import Mettapedia.Machines.IncrementalConformance.NominalCallables
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge

/-!
# Public observations of nominal PeTTa callables

A generated registered name is grounded to `get-metatype`. A captured partial
application is a Prolog compound, and that query has no answer for it. Both
values are non-lists: the three list observers return an empty-list value,
and `is-expr` returns false. An empty-list answer and no answer are different.

The reference observer below inspects the generated named/partial value. The
target observer independently recognizes the nominal domain of neutral `Lam`
code, then observes the public value rather than its executable code fields.
The existing preparation and value relations establish their correspondence.
A separate structural observer demonstrates the error made by exposing those
fields as expression data; it is not the callable observer's definition.
Source expressions and callable values have separate constructors at this
boundary. An authored or quoted `(partial ...)` remains expression data; its
spelling does not grant it the private callable representation.

The fragment has closed captured data and finite prepared occurrences. These
theorems do not prove native C correspondence, registration/loader behavior,
arbitrary variable variants, numeric/cyclic/foreign capture equality, or exact
printer-counter correspondence. Injective renaming can preserve callable
comparison while changing literal printed names; those contracts are distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.CallableObservationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge (patternToAtom)


universe u

inductive Observer where
  | metatype
  | size
  | car
  | cdr
  | isExpr
deriving DecidableEq, Repr

/-- Results use the existing public atom carrier. The outer list is the
query's answer sequence; `.expression []` is one possible answer value. -/
def emptyList : Atom := .expression []
def groundedType : Atom := .symbol "Grounded"
def expressionType : Atom := .symbol "Expression"
def falseValue : Atom := .grounded (.bool false)

/-- Reference classification follows the named/compound distinction, with
non-list behavior for both forms. Registration of generated names is supplied
by the translated callable carrier, rather than inferred from syntax fields. -/
def observeReference {Value : Type u} (observer : Observer) :
    NominalCallables.Reference.Callable Value → List Atom
  | .named _ =>
      match observer with
      | .metatype => [groundedType]
      | .size | .car | .cdr => [emptyList]
      | .isExpr => [falseValue]
  | .captured _ _ _ =>
      match observer with
      | .metatype => []
      | .size | .car | .cdr => [emptyList]
      | .isExpr => [falseValue]

/-- A structural observer without callable registration knowledge. Applying
it to a callable's code representation would expose its implementation. -/
def observeAtom (observer : Observer) (atom : Atom) : List Atom :=
  match observer with
  | .metatype =>
      match atom with
      | .var _ => [.symbol "Variable"]
      | .grounded _ => [groundedType]
      | .symbol _ => [.symbol "Symbol"]
      | .expression _ => [expressionType]
  | .size =>
      match atom with
      | .expression elements => [.grounded (.int elements.length)]
      | _ => [emptyList]
  | .car =>
      match atom with
      | .expression (first :: _) => [first]
      | _ => [emptyList]
  | .cdr =>
      match atom with
      | .expression (_ :: rest) => [.expression rest]
      | _ => [emptyList]
  | .isExpr =>
      match atom with
      | .expression _ => [.grounded (.bool true)]
      | _ => [falseValue]

def observeStructure (observer : Observer) (code : Pattern) : List Atom :=
  observeAtom observer (patternToAtom code)

/-- Recognition traverses the closed nominal domain; it does not infer a
public expression merely because executable code has constructor children. -/
def recognizedToken {Value : Type u} (closure : NominalCallables.Closure Value) : Option Nat :=
  (NominalCallables.domainView closure.code).bind NominalCallables.tokenView

/-- On recognized callables, capture emptiness chooses the public value form.
The absent-recognition case is outside this callable admission and has no
answer here. Ordinary expression data uses a separate input constructor below;
this observer does not turn unrecognized executable code into public data. -/
def observeNative {Value : Type u} (observer : Observer)
    (closure : NominalCallables.Closure Value) : List Atom :=
  match recognizedToken closure with
  | none => []
  | some _ =>
      match observer with
      | .metatype => if closure.captures.isEmpty then [groundedType] else []
      | .size | .car | .cdr => [emptyList]
      | .isExpr => [falseValue]

/-- This is the observation boundary for the two forms in the fragment, not
a complete language value carrier. Source-expression elements are retained
data. A translated callable has its own constructor even if its implementation
can also be printed as an expression. -/
inductive ReferenceInput (Value : Type u) where
  | callable (value : NominalCallables.Reference.Callable Value)
  | sourceExpression (elements : List Atom)

/-- Native admission uses a private callable constructor rather than a public
head spelling. Ordinary authored/quoted lists enter `sourceExpression`. -/
inductive NativeInput (Value : Type u) where
  | callable (value : NominalCallables.Closure Value)
  | sourceExpression (elements : List Atom)

def observeReferenceInput {Value : Type u} (observer : Observer) :
    ReferenceInput Value → List Atom
  | .callable value => observeReference observer value
  | .sourceExpression elements => observeAtom observer (.expression elements)

def observeNativeInput {Value : Type u} (observer : Observer) :
    NativeInput Value → List Atom
  | .callable value => observeNative observer value
  | .sourceExpression elements => observeAtom observer (.expression elements)

/-- Callable correspondence is the existing nominal value relation; expression
data correspondence retains the actual ordered elements. No cross-constructor
relation equates authored syntax with executable callable identity. -/
def RelatedInput {Value : Type u} : ReferenceInput Value → NativeInput Value → Prop
  | .callable reference, .callable closure => NominalCallables.RelatedValue reference closure
  | .sourceExpression reference, .sourceExpression elements => reference = elements
  | _, _ => False

@[simp] theorem recognizedToken_close {Value : Type u} (token : Nat)
    (source : NominalCallables.Declaration) (captures : List Value) :
    recognizedToken (NominalCallables.close token source captures) = some token := by
  simp [recognizedToken, NominalCallables.close]

@[simp] theorem observeNative_close {Value : Type u} (observer : Observer)
    (token : Nat) (source : NominalCallables.Declaration) (captures : List Value) :
    observeNative observer (NominalCallables.close token source captures) =
      match observer with
      | .metatype => if captures.isEmpty then [groundedType] else []
      | .size | .car | .cdr => [emptyList]
      | .isExpr => [falseValue] := by
  cases observer <;> simp [observeNative, recognizedToken, NominalCallables.close]

theorem related_recognition {Value : Type u} (reference : NominalCallables.Reference.Callable Value)
    (closure : NominalCallables.Closure Value) (related : NominalCallables.RelatedValue reference closure) :
    recognizedToken closure = some (NominalCallables.Reference.name reference) := by
  simp [recognizedToken, related.1]

/-- Reference results and native value observations agree from the existing
nominal value relation, including the absent captured metatype answer. -/
theorem observation_correspondence {Value : Type u} (observer : Observer)
    (reference : NominalCallables.Reference.Callable Value) (closure : NominalCallables.Closure Value)
    (related : NominalCallables.RelatedValue reference closure) :
    observeNative observer closure = observeReference observer reference := by
  have recognized := related_recognition reference closure related
  have captures := related.2
  cases reference <;>
    simp only [NominalCallables.Reference.captures] at captures <;>
    cases observer <;>
    simp [observeNative, observeReference, recognized, captures]

/-- The public boundary respects each independently represented callable and
also the ordinary source-expression case without inspecting its head spelling. -/
theorem input_observation_correspondence {Value : Type u} (observer : Observer)
    (reference : ReferenceInput Value) (native : NativeInput Value)
    (related : RelatedInput reference native) :
    observeNativeInput observer native = observeReferenceInput observer reference := by
  cases reference with
  | callable reference =>
      cases native with
      | callable closure => exact observation_correspondence observer reference closure related
      | sourceExpression elements => exact False.elim related
  | sourceExpression reference =>
      cases native with
      | callable closure => exact False.elim related
      | sourceExpression elements =>
          cases related
          rfl

theorem callable_not_related_to_source_expression {Value : Type u}
    (reference : NominalCallables.Reference.Callable Value) (elements : List Atom) :
    ¬ RelatedInput (.callable reference) (.sourceExpression elements) := by
  intro related
  exact related

theorem source_expression_not_related_to_callable {Value : Type u}
    (elements : List Atom) (closure : NominalCallables.Closure Value) :
    ¬ RelatedInput (.sourceExpression elements) (.callable closure) := by
  intro related
  exact related

/-- Every source list retains expression/list behavior regardless of its head.
In particular, `Lam` and `partial` are not reserved public data spellings. -/
theorem source_expression_observations {Value : Type u} (elements : List Atom) :
    observeNativeInput .metatype (.sourceExpression elements : NativeInput Value) = [expressionType] ∧
    observeNativeInput .size (.sourceExpression elements : NativeInput Value) =
      [.grounded (.int elements.length)] ∧
    observeNativeInput .isExpr (.sourceExpression elements : NativeInput Value) =
      [.grounded (.bool true)] := by
  constructor
  · rfl
  · constructor <;> rfl

theorem source_expression_head_and_tail {Value : Type u} (first : Atom) (rest : List Atom) :
    observeNativeInput .car (.sourceExpression (first :: rest) : NativeInput Value) = [first] ∧
    observeNativeInput .cdr (.sourceExpression (first :: rest) : NativeInput Value) = [.expression rest] := by
  constructor <;> rfl

theorem close_related {Value : Type u} (token : Nat) (source : NominalCallables.Declaration)
    (captures : List Value) :
    NominalCallables.RelatedValue (NominalCallables.Reference.close token captures) (NominalCallables.close token source captures) := by
  simp [NominalCallables.RelatedValue, NominalCallables.close]

theorem close_observation_correspondence {Value : Type u} (observer : Observer)
    (token : Nat) (source : NominalCallables.Declaration) (captures : List Value) :
    observeNative observer (NominalCallables.close token source captures) =
      observeReference observer (NominalCallables.Reference.close token captures) :=
  observation_correspondence observer _ _ (close_related token source captures)

/-- An equality for the complete prepared input derives its relation from
preparation, rather than assuming correspondence for those input values. -/
theorem prepared_observations {Value : Type u} (observer : Observer)
    (counter : Nat) (sources : List NominalCallables.Declaration) (environment : Nat → Value) :
    ((NominalCallables.prepare counter sources).2.map (NominalCallables.instantiate environment)).map (observeNative observer) =
      ((NominalCallables.Reference.translate counter sources).map (NominalCallables.Reference.instantiate environment)).map
        (observeReference observer) := by
  have mapped : ∀ (references : List (NominalCallables.Reference.Callable Value))
      (closures : List (NominalCallables.Closure Value)),
      List.Forall₂ NominalCallables.RelatedValue references closures →
      closures.map (observeNative observer) = references.map (observeReference observer) := by
    intro references closures related
    induction related with
    | nil => rfl
    | cons related _ ih =>
        simp only [List.map_cons, observation_correspondence observer _ _ related, ih]
  exact mapped _ _ (NominalCallables.prepared_values_related counter sources environment)

def observerCatalogue : List Observer := [.metatype, .size, .car, .cdr, .isExpr]

def observationsReference {Value : Type u} (reference : NominalCallables.Reference.Callable Value) :
    List (Observer × List Atom) :=
  observerCatalogue.map fun observer => (observer, observeReference observer reference)

def observationsNative {Value : Type u} (closure : NominalCallables.Closure Value) :
    List (Observer × List Atom) :=
  observerCatalogue.map fun observer => (observer, observeNative observer closure)

theorem all_observations_correspond {Value : Type u} (reference : NominalCallables.Reference.Callable Value)
    (closure : NominalCallables.Closure Value) (related : NominalCallables.RelatedValue reference closure) :
    observationsNative closure = observationsReference reference := by
  apply List.map_congr_left
  intro observer _
  exact congrArg (Prod.mk observer) (observation_correspondence observer reference closure related)

/-- Neither a different implementation body nor an unrelated nominal token
is observable through this catalogue when the capture payload stays fixed. -/
theorem public_observations_hide_code {Value : Type u} (observer : Observer)
    (left right : Nat) (earlier later : NominalCallables.Declaration) (captures : List Value) :
    observeNative observer (NominalCallables.close left earlier captures) =
      observeNative observer (NominalCallables.close right later captures) := by
  cases observer <;> simp

/-- Agreement of this public catalogue does not establish callable equality.
The nominal comparison remains an independent observer of the public value. -/
theorem catalogue_agreement_does_not_identify_callables {Value : Type u} [DecidableEq Value]
    (left right : Nat) (different : left ≠ right)
    (earlier later : NominalCallables.Declaration) (captures : List Value) :
    observationsNative (NominalCallables.close left earlier captures) =
      observationsNative (NominalCallables.close right later captures) ∧
    NominalCallables.same (NominalCallables.close left earlier captures)
      (NominalCallables.close right later captures) = false := by
  constructor
  · apply List.map_congr_left
    intro observer _
    exact congrArg (Prod.mk observer)
      (public_observations_hide_code observer left right earlier later captures)
  · exact NominalCallables.distinct_occurrences_distinguished left right different
      earlier later captures captures

theorem no_body_fields_through_list_observers {Value : Type u} (token : Nat)
    (source : NominalCallables.Declaration) (captures : List Value) :
    observeNative .size (NominalCallables.close token source captures) = [emptyList] ∧
    observeNative .car (NominalCallables.close token source captures) = [emptyList] ∧
    observeNative .cdr (NominalCallables.close token source captures) = [emptyList] ∧
    observeNative .isExpr (NominalCallables.close token source captures) = [falseValue] := by
  simp

theorem bare_metatype_grounded {Value : Type u} (token : Nat) (source : NominalCallables.Declaration) :
    observeNative .metatype (NominalCallables.close token source ([] : List Value)) = [groundedType] := by
  simp

theorem captured_metatype_absent {Value : Type u} (token : Nat) (source : NominalCallables.Declaration)
    (first : Value) (rest : List Value) :
    observeNative .metatype (NominalCallables.close token source (first :: rest)) = [] := by
  simp

/-- Replacing an opaque callable by expression data changes a public
observation, even when the data faithfully describes all of its code fields. -/
theorem source_expression_cannot_replace_callable {Value : Type u} (token : Nat)
    (source : NominalCallables.Declaration) (captures : List Value) (elements : List Atom) :
    observeNativeInput .metatype (.sourceExpression elements : NativeInput Value) ≠
      observeNativeInput .metatype (.callable (NominalCallables.close token source captures)) := by
  cases captures <;> simp [observeNativeInput, observeAtom, expressionType, groundedType]

/-- Adding a captured argument changes the public metatype behavior while
preserving nominal identity. Public non-list behavior remains unchanged. -/
theorem partial_application_changes_metatype {Value : Type u} (token : Nat)
    (source : NominalCallables.Declaration) (argument : Value) :
    observeNative .metatype (NominalCallables.close token source ([] : List Value)) = [groundedType] ∧
    observeNative .metatype (NominalCallables.bind (NominalCallables.close token source []) [argument]) = [] ∧
    observeNative .size (NominalCallables.bind (NominalCallables.close token source []) [argument]) = [emptyList] := by
  simp [observeNative, NominalCallables.bind, NominalCallables.close, recognizedToken]

/-- Coherent renaming acts on every generated callable reference. It changes
nominal spelling without changing captures or the named/compound distinction. -/
def renameNames {Value : Type u} (rename : Nat → Nat) :
    NominalCallables.Reference.Callable Value → NominalCallables.Reference.Callable Value
  | .named name => .named (rename name)
  | .captured name first rest => .captured (rename name) first rest

theorem renameNames_close {Value : Type u} (rename : Nat → Nat) (token : Nat)
    (captures : List Value) :
    renameNames rename (NominalCallables.Reference.close token captures) = NominalCallables.Reference.close (rename token) captures := by
  cases captures <;> rfl

theorem renameNames_injective {Value : Type u} (rename : Nat → Nat)
    (injective : Function.Injective rename) : Function.Injective (renameNames (Value := Value) rename) := by
  intro left right equal
  cases left <;> cases right <;>
    simp only [renameNames, NominalCallables.Reference.Callable.named.injEq,
      NominalCallables.Reference.Callable.captured.injEq, reduceCtorEq] at equal
  · exact congrArg NominalCallables.Reference.Callable.named (injective equal)
  · rcases equal with ⟨name, first, rest⟩
    cases injective name
    cases first
    cases rest
    rfl

theorem reference_comparison_survives_safe_renaming {Value : Type u} [DecidableEq Value]
    (rename : Nat → Nat) (injective : Function.Injective rename)
    (left right : NominalCallables.Reference.Callable Value) :
    NominalCallables.Reference.same (renameNames rename left) (renameNames rename right) = NominalCallables.Reference.same left right := by
  have equality : renameNames rename left = renameNames rename right ↔ left = right :=
    ⟨fun equal => renameNames_injective rename injective equal, congrArg (renameNames rename)⟩
  simp only [NominalCallables.Reference.same, equality]

theorem native_comparison_survives_safe_renaming {Value : Type u} [DecidableEq Value]
    (rename : Nat → Nat) (injective : Function.Injective rename)
    (left right : Nat) (earlier later : NominalCallables.Declaration) (capturesLeft capturesRight : List Value) :
    NominalCallables.same (NominalCallables.close (rename left) earlier capturesLeft) (NominalCallables.close (rename right) later capturesRight) =
      NominalCallables.same (NominalCallables.close left earlier capturesLeft) (NominalCallables.close right later capturesRight) := by
  have equality : rename left = rename right ↔ left = right :=
    ⟨fun equal => injective equal, congrArg rename⟩
  simp only [NominalCallables.same_close, equality]

theorem public_observations_survive_name_renaming {Value : Type u} (observer : Observer)
    (rename : Nat → Nat) (callable : NominalCallables.Reference.Callable Value) :
    observeReference observer (renameNames rename callable) = observeReference observer callable := by
  cases callable <;> cases observer <;> rfl

/-- Literal printer output is a separate observation. These strings are not
identified just because a coherent nominal renaming preserves value comparison. -/
def literalCounterName {Value : Type u} (callable : NominalCallables.Reference.Callable Value) : String :=
  "lambda_" ++ toString (NominalCallables.Reference.name callable)

namespace Controls

def source : NominalCallables.Declaration := ⟨["x"], .bvar 0, []⟩
def capturedSource : NominalCallables.Declaration := ⟨["x"], .fvar "free", [0]⟩

theorem bare_callable_observations :
    observationsNative (NominalCallables.close 1 source ([] : List Nat)) =
      [(.metatype, [groundedType]), (.size, [emptyList]), (.car, [emptyList]),
        (.cdr, [emptyList]), (.isExpr, [falseValue])] := by
  simp [observationsNative, observerCatalogue]

theorem captured_callable_observations :
    observationsNative (NominalCallables.close 1 capturedSource [42]) =
      [(.metatype, []), (.size, [emptyList]), (.car, [emptyList]),
        (.cdr, [emptyList]), (.isExpr, [falseValue])] := by
  simp [observationsNative, observerCatalogue]

theorem empty_list_answer_is_not_absent_answer :
    observeNative .size (NominalCallables.close 1 capturedSource [42]) ≠
      observeNative .metatype (NominalCallables.close 1 capturedSource [42]) := by
  simp

theorem structural_lam_reports_wrong_metatype :
    observeStructure .metatype (NominalCallables.canonical 1 source) = [expressionType] ∧
    observeStructure .metatype (NominalCallables.canonical 1 source) ≠
      observeNative .metatype (NominalCallables.close 1 source ([] : List Nat)) := by
  simp [observeStructure, observeAtom, NominalCallables.canonical, patternToAtom, expressionType, groundedType]

theorem structural_lam_exposes_wrong_size_and_head :
    observeStructure .size (NominalCallables.canonical 1 source) = [.grounded (.int 3)] ∧
    observeStructure .car (NominalCallables.canonical 1 source) = [.symbol "Lam"] ∧
    observeStructure .size (NominalCallables.canonical 1 source) ≠
      observeNative .size (NominalCallables.close 1 source ([] : List Nat)) := by
  simp [observeStructure, observeAtom, NominalCallables.canonical, patternToAtom, emptyList]

theorem structural_lam_exposes_code_tail :
    observeStructure .cdr (NominalCallables.canonical 1 source) =
      [.expression [patternToAtom (NominalCallables.nominalDomain 1),
        patternToAtom (.multiLambda 1 ["x"] (.bvar 0))]] ∧
    observeStructure .cdr (NominalCallables.canonical 1 source) ≠
      observeNative .cdr (NominalCallables.close 1 source ([] : List Nat)) := by
  simp [observeStructure, observeAtom, NominalCallables.canonical, patternToAtom, source, emptyList]

theorem structural_lam_reports_wrong_expression_status :
    observeStructure .isExpr (NominalCallables.canonical 1 source) = [.grounded (.bool true)] ∧
    observeStructure .isExpr (NominalCallables.canonical 1 source) ≠
      observeNative .isExpr (NominalCallables.close 1 source ([] : List Nat)) := by
  simp [observeStructure, observeAtom, NominalCallables.canonical, patternToAtom, falseValue]

theorem captured_metatype_is_not_grounded_or_expression :
    observeNative .metatype (NominalCallables.close 1 capturedSource [42]) ≠ [groundedType] ∧
    observeNative .metatype (NominalCallables.close 1 capturedSource [42]) ≠ [expressionType] := by
  simp

def authoredPartial : List Atom :=
  [.symbol "partial", .symbol "base", .expression [.grounded (.int 42)]]

/-- A public head spelling does not create the private callable constructor.
This authored/quoted form has precisely the ordinary list observations. -/
theorem authored_partial_remains_expression_data :
    observeNativeInput .metatype (.sourceExpression authoredPartial : NativeInput Nat) = [expressionType] ∧
    observeNativeInput .size (.sourceExpression authoredPartial : NativeInput Nat) = [.grounded (.int 3)] ∧
    observeNativeInput .car (.sourceExpression authoredPartial : NativeInput Nat) = [.symbol "partial"] ∧
    observeNativeInput .cdr (.sourceExpression authoredPartial : NativeInput Nat) =
      [.expression [.symbol "base", .expression [.grounded (.int 42)]]] ∧
    observeNativeInput .isExpr (.sourceExpression authoredPartial : NativeInput Nat) = [.grounded (.bool true)] := by
  simp [observeNativeInput, observeAtom, authoredPartial]

theorem authored_partial_agrees_with_reference_data :
    ∀ observer, observeNativeInput observer (.sourceExpression authoredPartial : NativeInput Nat) =
      observeReferenceInput observer (.sourceExpression authoredPartial : ReferenceInput Nat) := by
  intro observer
  exact input_observation_correspondence observer _ _ rfl

theorem captured_callable_is_not_authored_partial_data :
    observeNativeInput .metatype (.callable (NominalCallables.close 1 capturedSource [42])) = [] ∧
    observeNativeInput .size (.callable (NominalCallables.close 1 capturedSource [42])) = [emptyList] ∧
    observeNativeInput .car (.callable (NominalCallables.close 1 capturedSource [42])) = [emptyList] ∧
    observeNativeInput .isExpr (.callable (NominalCallables.close 1 capturedSource [42])) = [falseValue] ∧
    observeNativeInput .metatype (.callable (NominalCallables.close 1 capturedSource [42])) ≠
      observeNativeInput .metatype (.sourceExpression authoredPartial : NativeInput Nat) := by
  simp [observeNativeInput, observeAtom]

/-- Even the same canonical code fields entered as quoted data remain data.
Admission needs the private value constructor, not a source-shape heuristic. -/
theorem canonical_lam_as_source_data_is_not_callable :
    observeNativeInput .metatype
      (.sourceExpression [ .symbol "Lam", patternToAtom (NominalCallables.nominalDomain 1),
        patternToAtom (.multiLambda 1 ["x"] (.bvar 0))] : NativeInput Nat) = [expressionType] ∧
    observeNativeInput .metatype
      (.sourceExpression [ .symbol "Lam", patternToAtom (NominalCallables.nominalDomain 1),
        patternToAtom (.multiLambda 1 ["x"] (.bvar 0))] : NativeInput Nat) ≠
      observeNativeInput .metatype (.callable (NominalCallables.close 1 source ([] : List Nat))) := by
  simp [observeNativeInput, observeAtom, expressionType, groundedType]

theorem safe_renaming_preserves_comparison_but_changes_literal_name :
    NominalCallables.Reference.same (renameNames Nat.succ (.named 1 : NominalCallables.Reference.Callable Nat))
      (renameNames Nat.succ (.named 1)) = NominalCallables.Reference.same (.named 1 : NominalCallables.Reference.Callable Nat) (.named 1) ∧
    literalCounterName (renameNames Nat.succ (.named 1 : NominalCallables.Reference.Callable Nat)) ≠
      literalCounterName (.named 1 : NominalCallables.Reference.Callable Nat) := by decide

theorem colliding_renaming_changes_comparison :
    NominalCallables.Reference.same (.named 1 : NominalCallables.Reference.Callable Nat) (.named 2) = false ∧
    NominalCallables.Reference.same (renameNames (fun _ => 0) (.named 1 : NominalCallables.Reference.Callable Nat))
      (renameNames (fun _ => 0) (.named 2)) = true := by decide

end Controls

end Mettapedia.Machines.IncrementalConformance.CallableObservationBoundary
