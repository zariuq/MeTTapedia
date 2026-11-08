import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundStampMatcher
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RowAlphaInvariance

/-!
# Declaration-derived metadata for checked value-class call chains

The finite source view retains annotation subjects and written type rows.
The declaration index reuses alpha-idempotent normalization. Its executable
functional gate checks every declared subject, rather than taking a global
Functional assumption from the caller.

Head admission has three outcomes: untyped, one supported closed value-class
arrow, or unsupported. An open, structural, metatype, overloaded or malformed
declaration is not relabelled as an untyped head. The generated metadata joins
the existing checked chain entry and program theorem; it does not introduce
another evaluator. This is the closed value-class branch, not the separate
structural/polymorphic admission service.

The source view starts after declaration extraction into the existing Ty
grammar. Native source codecs, index/revision ownership and custom get-type
overrides remain explicit outer admission obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ChainRegion

abbrev Source := List (Atom × Ty String)

def subjects (source : Source) : List String := source.filterMap fun row =>
  match row.1 with
  | .symbol name => some name
  | _ => none

def rawRows (source : Source) (head : String) : List (Ty String) := source.filterMap fun row =>
  if row.1 == .symbol head then some row.2 else none

def declarations (source : Source) : Decls := Decls.idemAlpha (rawRows source)

def symbolSubjects (source : Source) : Bool := source.all fun row =>
  match row.1 with
  | .symbol _ => true
  | _ => false

def functionalCheck (source : Source) : Bool :=
  symbolSubjects source && (subjects source).all fun name =>
    decide ((declarations source name).length ≤ 1)

theorem rawRows_empty_of_absent {source : Source} {head : String}
    (absent : head ∉ subjects source) : rawRows source head = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro row member
  by_cases same : row.1 = Atom.symbol head
  · have present : head ∈ subjects source := by
      apply List.mem_filterMap.mpr
      exact ⟨row, member, by rw [same]⟩
    exact False.elim (absent present)
  · simp [same]

/-- The finite index check establishes the global declaration-space fact
used by guard idempotence, including heads absent from the source index. -/
theorem functional_of_check {source : Source} (checked : functionalCheck source = true) :
    Functional (declarations source) := by
  intro head
  have checkedHeads := (Bool.and_eq_true_iff.mp checked).2
  by_cases present : head ∈ subjects source
  · exact of_decide_eq_true (List.all_eq_true.mp checkedHeads head present)
  · rw [declarations, Decls.idemAlpha, rawRows_empty_of_absent present]
    decide

theorem checked_subjects {source : Source} (checked : functionalCheck source = true)
    (row : Atom × Ty String) (present : row ∈ source) : ∃ head, row.1 = .symbol head := by
  have typed := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).1 row present
  cases subject : row.1 with
  | symbol head => exact ⟨head, rfl⟩
  | _ => simp [subject] at typed

theorem rawRows_append (source : Source) (head owner : String) (row : Ty String) :
    rawRows (source ++ [(.symbol owner, row)]) head =
      rawRows source head ++ if owner = head then [row] else [] := by
  by_cases same : owner = head <;>
    simp [rawRows, List.filterMap_append, same]

/-- Duplicate and alpha-renamed annotations preserve the actual indexed
declaration function, not only its cardinality. -/
theorem repeat_preserves_index (source : Source) (owner : String) (row : Ty String)
    (repeated : ∃ previous ∈ rawRows source owner, AlphaEq previous row) :
    declarations (source ++ [(.symbol owner, row)]) = declarations source := by
  funext head
  unfold declarations Decls.idemAlpha
  rw [rawRows_append]
  by_cases same : owner = head
  · subst head
    simp only [if_true]
    exact dedupAlpha_append_alpha _ _ repeated
  · simp [same]

inductive Class where
  | unchecked
  | number
  | string
  | boolean
  deriving DecidableEq

def Class.type : Class → Ty Empty
  | .unchecked => .sym "%Undefined%"
  | .number => .sym "Number"
  | .string => .sym "String"
  | .boolean => .sym "Bool"

def readClass : Ty Empty → Option Class
  | .sym "%Undefined%" => some .unchecked
  | .sym "Number" => some .number
  | .sym "String" => some .string
  | .sym "Bool" => some .boolean
  | _ => none

def readClasses : List (Ty Empty) → Option (List Class)
  | [] => some []
  | type_ :: types => (readClass type_).bind fun class_ =>
      (readClasses types).map (class_ :: ·)

theorem readClass_type (class_ : Class) : readClass class_.type = some class_ := by
  cases class_ <;> rfl

theorem readClass_sound {type_ : Ty Empty} {class_ : Class}
    (read : readClass type_ = some class_) : class_.type = type_ := by
  cases type_ with
  | var impossible => exact impossible.elim
  | app _ => cases read
  | sym name =>
      unfold readClass at read
      split at read <;> (try simp only [Option.some.injEq] at read)
      all_goals cases read <;> simp_all [Class.type]

theorem readClasses_sound : ∀ {types : List (Ty Empty)} {classes : List Class},
    readClasses types = some classes → classes.map Class.type = types
  | [], _, read => by cases read; rfl
  | first :: rest, classes, read => by
      simp only [readClasses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
      obtain ⟨firstClass, firstRead, later, laterRead, equality⟩ := read
      cases equality
      simp only [List.map_cons, readClass_sound firstRead, readClasses_sound laterRead]

theorem readClasses_types (classes : List Class) :
    readClasses (classes.map Class.type) = some classes := by
  induction classes with
  | nil => rfl
  | cons first rest ih => simp [readClasses, readClass_type, ih]

/-- The existing arrow parser reconstructs exactly the row it split. -/
theorem arrowSplit_sound {V : Type} {row : Ty V} {params : List (Ty V)} {range : Ty V}
    (split : arrowSplit row = some (params, range)) : row = arrow params range := by
  cases row with
  | var _ => cases split
  | sym _ => cases split
  | app parts =>
      cases parts with
      | nil => cases split
      | cons head rest =>
          cases head with
          | var _ => cases split
          | app _ => cases split
          | sym name =>
              simp only [arrowSplit] at split
              split_ifs at split with named
              subst name
              obtain ⟨last, found, equal⟩ := Option.map_eq_some_iff.mp split
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
              have joined := List.dropLast_append_getLast? (l := rest) last found
              simp only [arrow, joined]

structure Signature where
  params : List Class
  range : Class
  deriving DecidableEq

def Signature.row (signature : Signature) : Ty String :=
  arrow ((signature.params.map Class.type).map Ty.lift) signature.range.type.lift

def Signature.closedRow (signature : Signature) : List (Ty Empty) × Ty Empty :=
  (signature.params.map Class.type, signature.range.type)

def readSignature (row : Ty String) : Option Signature :=
  (GroundStampMatcher.close row).bind fun closed =>
    (arrowSplit closed).bind fun pair =>
      (readClasses pair.1).bind fun classes =>
        (readClass pair.2).map fun result => ⟨classes, result⟩

theorem readSignature_sound {row : Ty String} {signature : Signature}
    (parsed : readSignature row = some signature) : signature.row = row := by
  simp only [readSignature, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
  obtain ⟨closed, closedRead, pair, split, classes, classesRead, result, resultRead, equality⟩ := parsed
  cases equality
  obtain ⟨params, range⟩ := pair
  have shape := arrowSplit_sound split
  have closedEq := GroundStampMatcher.close_sound row closed closedRead
  rw [shape] at closedEq
  rw [← closedEq]
  simp only [Signature.row, readClasses_sound classesRead, readClass_sound resultRead,
    arrow, GroundStampMatcher.lift_app, List.map_cons, List.map_append]
  rfl

theorem readSignature_row (signature : Signature) : readSignature signature.row = some signature := by
  have lifted : signature.row = (arrow (signature.params.map Class.type) signature.range.type).lift := by
    simp [Signature.row, arrow, Ty.lift, Ty.map]
  rw [readSignature, lifted, GroundStampMatcher.close_lift]
  simp only [Option.bind_some, arrowSplit_arrow, readClasses_types, readClass_type, Option.map_some]

inductive HeadStatus where
  | untyped
  | typed (signature : Signature)
  | unsupported
  deriving DecidableEq

def status (source : Source) (head : String) : HeadStatus :=
  match declarations source head with
  | [] => .untyped
  | [row] => match readSignature row with
      | some signature => .typed signature
      | none => .unsupported
  | _ => .unsupported

theorem status_untyped_iff (source : Source) (head : String) :
    status source head = .untyped ↔ declarations source head = [] := by
  unfold status
  cases found : declarations source head with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => cases parsed : readSignature first <;> simp [parsed]
      | cons _ _ => simp

theorem status_typed_source {source : Source} {head : String} {signature : Signature}
    (admitted : status source head = .typed signature) :
    declarations source head = [signature.row] := by
  unfold status at admitted
  cases found : declarations source head with
  | nil => simp [found] at admitted
  | cons row rest =>
      cases rest with
      | cons _ _ => simp [found] at admitted
      | nil =>
          cases parsed : readSignature row with
          | none => simp [found, parsed] at admitted
          | some actual =>
              have eq : actual = signature := by simpa [found, parsed] using admitted
              subst actual
              rw [readSignature_sound parsed]

/-- The outer option distinguishes unsupported metadata from an untyped
head. A caller must never erase this distinction with a default `none`. -/
def lookup (source : Source) (head : String) : Option (Option (List (Ty Empty) × Ty Empty)) :=
  match status source head with
  | .untyped => some none
  | .typed signature => some (some signature.closedRow)
  | .unsupported => none

theorem lookup_untyped_iff (source : Source) (head : String) :
    lookup source head = some none ↔ declarations source head = [] := by
  rw [← status_untyped_iff]
  unfold lookup
  cases status source head <;> simp

def Class.accepts (class_ : Class) (value : Atom) : Bool :=
  match class_ with
  | .unchecked => true
  | .number => decide (Literal "Number" value)
  | .string => decide (Literal "String" value)
  | .boolean => decide (Literal "Bool" value)

theorem class_accepts_iff (class_ : Class) (value : Atom) :
    class_.accepts value = true ↔ ValueFormal class_.type value := by
  cases class_ <;> simp [Class.accepts, Class.type, ValueFormal, demand, Unchecked, Ty.lift, Ty.map]

def argumentsAccepted : List Class → List Atom → Bool
  | [], [] => true
  | class_ :: classes, value :: values => class_.accepts value && argumentsAccepted classes values
  | _, _ => false

theorem argumentsAccepted_iff : ∀ classes values,
    argumentsAccepted classes values = true ↔ ValueArguments (classes.map Class.type) values
  | [], [] => by simp [argumentsAccepted, ValueArguments]
  | [], _ :: _ => by simp [argumentsAccepted, ValueArguments]
  | _ :: _, [] => by simp [argumentsAccepted, ValueArguments]
  | class_ :: classes, value :: values => by
      simp only [argumentsAccepted, Bool.and_eq_true, List.map_cons, ValueArguments,
        List.forall₂_cons, class_accepts_iff, argumentsAccepted_iff]

def owed (class_ : Class) : Option (Ty Empty) :=
  match class_ with
  | .unchecked => none
  | _ => some class_.type

theorem owed_eq_rowOwe (class_ : Class) : owed class_ = rowOwe class_.type := by
  cases class_ <;> decide

/-- Typed metadata gives exactly the existing checked activation boundary.
The literal-class test is not substituted for an arbitrary type witness. -/
theorem typed_entry_exact {source : Source} {head : String} {signature : Signature}
    (typed : status source head = .typed signature) (args : List Atom) :
    (if argumentsAccepted signature.params args then some (owed signature.range) else none) =
      entryAdmission (fun name => (lookup source name).join) head args := by
  simp only [entryAdmission, lookup, typed, Signature.closedRow, Option.join_some]
  rw [← owed_eq_rowOwe]
  simp only [argumentsAccepted_iff]

/-- The native metadata lookup is arity-sensitive. A declaration for a
different arity declines; it does not make this call an untyped call. -/
def statusAt (source : Source) (head : String) (arity : Nat) : HeadStatus :=
  match status source head with
  | .typed signature => if signature.params.length = arity then .typed signature else .unsupported
  | answer => answer

theorem wrong_arity_declines {source : Source} {head : String} {signature : Signature}
    (typed : status source head = .typed signature) {arity : Nat}
    (wrong : signature.params.length ≠ arity) : statusAt source head arity = .unsupported := by
  simp [statusAt, typed, wrong]

/-- A finite region's metadata check allows unrelated unsupported rows in
the enclosing space. Its result is local, not a whole-program certificate. -/
def regionCheck (source : Source) (heads : List String) : Bool :=
  heads.all fun head => (lookup source head).isSome

theorem region_lookup_supported {source : Source} {heads : List String}
    (checked : regionCheck source heads = true) {head : String} (member : head ∈ heads) :
    ∃ row, lookup source head = some row := by
  exact Option.isSome_iff_exists.mp (List.all_eq_true.mp checked head member)

/-- A stronger closed value-class source profile, used for the whole
program corollary below. General native compilation may instead admit only
the reached region and keep unrelated declaration kinds in the space. -/
def closedSourceCheck (source : Source) : Bool :=
  functionalCheck source && regionCheck source (subjects source)

theorem closedSource_lookup {source : Source} (checked : closedSourceCheck source = true)
    (head : String) : ∃ row, lookup source head = some row := by
  by_cases present : head ∈ subjects source
  · exact region_lookup_supported (Bool.and_eq_true_iff.mp checked).2 present
  · exact ⟨none, (lookup_untyped_iff source head).mpr (by
      rw [declarations, Decls.idemAlpha, rawRows_empty_of_absent present]
      rfl)⟩

/-- The source protocol reads the first alpha-distinct declaration, with
absence meaning genuinely untyped. Under the functional gate there is no
second distinct candidate. -/
def sourceSignature (source : Source) (head : String) : Option (Ty String) :=
  (declarations source head).head?

/-- This projection is used only behind a supported-lookup theorem. The
outer admission result remains available through `lookup` and `statusAt`. -/
def generatedRows (source : Source) (head : String) : Option (List (Ty Empty) × Ty Empty) :=
  (lookup source head).join

theorem signature_of_supported {source : Source} {head : String}
    (supported : ∃ row, lookup source head = some row) :
    sigOf (generatedRows source) head = sourceSignature source head := by
  cases typed : status source head with
  | unsupported => simp [lookup, typed] at supported
  | untyped =>
      have absent := (status_untyped_iff source head).mp typed
      simp [sigOf, generatedRows, lookup, typed, sourceSignature, absent]
  | typed signature =>
      have declared := status_typed_source typed
      simp [sigOf, generatedRows, lookup, typed, sourceSignature, declared,
        Signature.closedRow, Signature.row]

theorem region_signature_exact {source : Source} {heads : List String}
    (checked : regionCheck source heads = true) {head : String} (member : head ∈ heads) :
    sigOf (generatedRows source) head = sourceSignature source head :=
  signature_of_supported (region_lookup_supported checked member)

theorem closedSource_signatures {source : Source} (checked : closedSourceCheck source = true) :
    sigOf (generatedRows source) = sourceSignature source := by
  funext head
  exact signature_of_supported (closedSource_lookup checked head)

/-- The source-derived gate supplies both the declaration space's global
functional fact and the machine's signature table. The authored equation
evaluator, all multiplicities, arbitrary non-tail calls, and distinct owed
classes are exactly those of the existing chain theorem. -/
theorem source_program_run_eq_protocol {source : Source}
    (checked : closedSourceCheck source = true) (grounded : String → Bool)
    (environment : Env) (equations : String → List Equation)
    (fuel : Nat) (head : String) (args : List Atom) :
    run (declarations source) grounded (generatedRows source)
      (stepsOf environment equations) fuel none head args =
    protocolRunS (declarations source) grounded (sourceSignature source)
      (stepsOf environment equations) fuel head args := by
  rw [program_run_eq_protocol _ _ (functional_of_check (Bool.and_eq_true_iff.mp checked).1)]
  rw [closedSource_signatures checked]

/-- The source ownership check includes the separate custom get-type
override gate; declaration functionality alone does not authorize it. -/
def nativeFunctionalGate (source : Source) (getTypeOverridden : Bool) : Bool :=
  functionalCheck source && !getTypeOverridden

theorem native_gate_facts {source : Source} {getTypeOverridden : Bool}
    (checked : nativeFunctionalGate source getTypeOverridden = true) :
    Functional (declarations source) ∧ getTypeOverridden = false := by
  exact ⟨functional_of_check (Bool.and_eq_true_iff.mp checked).1,
    by simpa using (Bool.and_eq_true_iff.mp checked).2⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission
