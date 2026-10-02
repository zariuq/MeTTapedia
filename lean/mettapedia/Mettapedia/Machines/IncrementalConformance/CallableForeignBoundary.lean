import Mettapedia.Machines.IncrementalConformance.CallableMatchingBoundary
import Std.Data.String.ToNat

/-!
# Nominal callable values at an owned foreign-term boundary

The public foreign image of a prepared callable is a registered atom or a
partial/2 compound whose second argument is the ordered capture list. Neutral
executable code stays in a finite runtime dictionary built from actual source
preparation; decoding looks it up instead of reconstructing code from a name.

Reference images, native serialization, dictionary lookups, and native
decoding are independent definitions. Captured data use the existing Atom
carrier, including scoped variable identifiers and recursive expression data.
The term carrier models this pure serialization fragment, not SWI execution,
host pointers, attributes, cycles, or an arbitrary foreign-function interface.
Generated spellings here are chosen representatives inside one runtime scope;
neither literal counter parity nor native C correspondence is asserted.

The callable roundtrip concerns prepared lambdas owned by this dictionary.
General partial/2 values with ordinary named bases and direct foreign invocation
require separate dispatch contracts. Empty partial compounds are retained as
foreign data rather than identified with the canonical bare-name image.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.CallableForeignBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Lists and compounds are distinct. Grounded payloads are admitted data
records, not a specification of their concrete SWI representation. -/
inductive ForeignTerm where
  | atom (name : String)
  | var (identity : String)
  | grounded (value : GroundedValue)
  | list (elements : List ForeignTerm)
  | compound (name : String) (arguments : List ForeignTerm)
deriving Repr

def generatedName (scope : String) (token : Nat) : String :=
  scope ++ ":lambda_" ++ Nat.repr token

theorem generatedName_injective (scope : String) : Function.Injective (generatedName scope) := by
  intro left right equal
  apply Nat.repr_injective
  exact (String.append_right_inj (scope ++ ":lambda_")).mp equal

@[simp] theorem generatedName_eq_iff (scope : String) (left right : Nat) :
    generatedName scope left = generatedName scope right ↔ left = right :=
  ⟨fun equal => generatedName_injective scope equal, congrArg (generatedName scope)⟩

namespace Reference

def dataImage : Atom → ForeignTerm
  | .symbol name => .atom name
  | .var identity => .var identity
  | .grounded value => .grounded value
  | .expression elements => .list (elements.map dataImage)

def callableImage (scope : String) : NominalCallables.Reference.Callable Atom → ForeignTerm
  | .named token => .atom (generatedName scope token)
  | .captured token first rest =>
      .compound "partial" [.atom (generatedName scope token), .list ((first :: rest).map dataImage)]

end Reference

def serializeData : Atom → ForeignTerm
  | .symbol name => .atom name
  | .var identity => .var identity
  | .grounded value => .grounded value
  | .expression elements => .list (serializeList elements)
where
  serializeList : List Atom → List ForeignTerm
    | [] => []
    | first :: rest => serializeData first :: serializeList rest

def decodeData : ForeignTerm → Option Atom
  | .atom name => some (.symbol name)
  | .var identity => some (.var identity)
  | .grounded value => some (.grounded value)
  | .list elements => (decodeList elements).map Atom.expression
  | .compound _ _ => none
where
  decodeList : List ForeignTerm → Option (List Atom)
    | [] => some []
    | first :: rest => do
        let first ← decodeData first
        let rest ← decodeList rest
        pure (first :: rest)

theorem serializeList_eq_map (elements : List Atom) :
    serializeData.serializeList elements = elements.map serializeData := by
  induction elements with
  | nil => rfl
  | cons first rest ih => simp only [serializeData.serializeList, List.map_cons, ih]

theorem data_images_correspond (data : Atom) : serializeData data = Reference.dataImage data := by
  match data with
  | .symbol _ | .var _ | .grounded _ => simp [serializeData, Reference.dataImage]
  | .expression elements =>
      simp only [serializeData, Reference.dataImage, serializeList_eq_map]
      congr 1
      apply List.map_congr_left
      intro element present
      exact data_images_correspond element
termination_by sizeOf data

theorem decode_serialized_list (elements : List Atom) :
    decodeData.decodeList (elements.map serializeData) = some elements := by
  match elements with
  | [] => rfl
  | first :: rest =>
      have ih := decode_serialized_list rest
      simp only [List.map_cons, decodeData.decodeList]
      have firstDecoded : decodeData (serializeData first) = some first := by
        match first with
        | .symbol _ | .var _ | .grounded _ => simp [serializeData, decodeData]
        | .expression children =>
            simp only [serializeData, serializeList_eq_map, decodeData]
            rw [decode_serialized_list children]
            rfl
      rw [firstDecoded, ih]
      rfl
termination_by sizeOf elements

theorem data_roundtrip (data : Atom) : decodeData (serializeData data) = some data := by
  cases data with
  | symbol _ | var _ | grounded _ => simp [serializeData, decodeData]
  | expression elements =>
      simp only [serializeData, serializeList_eq_map, decodeData, decode_serialized_list]
      rfl

structure Entry where
  token : Nat
  name : String
  code : Pattern

/-- Only code references retained from the actual prepared plans are stored.
The traversal attaches the stable name/token to each finite occurrence. -/
def retainPlans (scope : String) (counter : Nat) : List NominalCallables.Plan → List Entry
  | [] => []
  | plan :: rest =>
      ⟨counter + 1, generatedName scope (counter + 1), plan.code⟩ ::
        retainPlans scope (counter + 1) rest

def dictionary (scope : String) (counter : Nat) (sources : List NominalCallables.Declaration) : List Entry :=
  retainPlans scope counter (NominalCallables.prepare counter sources).2

def lookupToken (token : Nat) : List Entry → Option Entry
  | [] => none
  | entry :: rest => if token = entry.token then some entry else lookupToken token rest

def lookupName (name : String) : List Entry → Option Entry
  | [] => none
  | entry :: rest => if entry.name = name then some entry else lookupName name rest

def codeToken (code : Pattern) : Option Nat :=
  (NominalCallables.domainView code).bind NominalCallables.tokenView

@[simp] theorem codeToken_canonical (token : Nat) (source : NominalCallables.Declaration) :
    codeToken (NominalCallables.canonical token source) = some token := by
  simp [codeToken]

@[simp] theorem dictionary_cons (scope : String) (counter : Nat)
    (source : NominalCallables.Declaration) (rest : List NominalCallables.Declaration) :
    dictionary scope counter (source :: rest) =
      ⟨counter + 1, generatedName scope (counter + 1), NominalCallables.canonical (counter + 1) source⟩ ::
        dictionary scope (counter + 1) rest := by
  rfl

theorem translation_cons (counter : Nat) (source : NominalCallables.Declaration)
    (rest : List NominalCallables.Declaration) :
    NominalCallables.Reference.translate counter (source :: rest) =
      ⟨counter + 1, source⟩ :: NominalCallables.Reference.translate (counter + 1) rest := by
  simp only [NominalCallables.Reference.translate, List.zipIdx_cons, List.map_cons]

theorem translated_name_lower (counter : Nat) (sources : List NominalCallables.Declaration)
    (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) :
    counter < reference.name := by
  induction sources generalizing counter with
  | nil => simp [NominalCallables.Reference.translate] at present
  | cons source rest ih =>
      rw [translation_cons, List.mem_cons] at present
      rcases present with equal | present
      · cases equal
        simp
      · have lower := ih (counter + 1) present
        omega

/-- Lookup success is derived from the actual finite catalogue traversal and
its strictly increasing names. It is not an assumed dictionary inverse law. -/
theorem prepared_token_lookup (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) :
    lookupToken reference.name (dictionary scope counter sources) =
      some ⟨reference.name, generatedName scope reference.name,
        NominalCallables.canonical reference.name reference.source⟩ := by
  induction sources generalizing counter with
  | nil => simp [NominalCallables.Reference.translate] at present
  | cons source rest ih =>
      rw [translation_cons, List.mem_cons] at present
      rcases present with equal | present
      · cases equal
        simp [lookupToken]
      · have lower := translated_name_lower (counter + 1) rest reference present
        have different : reference.name ≠ counter + 1 := by omega
        simp only [dictionary_cons, lookupToken, different, ↓reduceIte]
        exact ih (counter + 1) present

theorem dictionary_generated_lookup (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (token : Nat) :
    lookupName (generatedName scope token) (dictionary scope counter sources) =
      lookupToken token (dictionary scope counter sources) := by
  induction sources generalizing counter with
  | nil => rfl
  | cons source rest ih =>
      simp only [dictionary_cons, lookupName, lookupToken, generatedName_eq_iff, eq_comm]
      split <;> simp only [ih]

theorem prepared_name_lookup (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) :
    lookupName (generatedName scope reference.name) (dictionary scope counter sources) =
      some ⟨reference.name, generatedName scope reference.name,
        NominalCallables.canonical reference.name reference.source⟩ := by
  rw [dictionary_generated_lookup]
  exact prepared_token_lookup scope counter sources reference present

def serializeCallable (entries : List Entry) (closure : NominalCallables.Closure Atom) : Option ForeignTerm := do
  let token ← codeToken closure.code
  let entry ← lookupToken token entries
  match closure.captures with
  | [] => pure (.atom entry.name)
  | first :: rest => pure (.compound "partial" [.atom entry.name,
      .list (serializeData.serializeList (first :: rest))])

/-- Canonical translated callables have either a bare name or nonempty
captures. An arbitrary foreign partial(Base, []) is outside that distinction. -/
def decodeCallable (entries : List Entry) : ForeignTerm → Option (NominalCallables.Closure Atom)
  | .atom name => (lookupName name entries).map fun entry => ⟨entry.code, []⟩
  | .compound "partial" [.atom name, .list (first :: rest)] => do
      let entry ← lookupName name entries
      let captures ← decodeData.decodeList (first :: rest)
      pure ⟨entry.code, captures⟩
  | _ => none

inductive NativeValue where
  | data (value : Atom)
  | callable (value : NominalCallables.Closure Atom)
  | foreignData (value : ForeignTerm)

/-- Unknown pure foreign terms are retained as data. Losing an owner dictionary
therefore loses executable code, not the foreign atom or compound itself. -/
def decodePublic (entries : List Entry) (term : ForeignTerm) : NativeValue :=
  match decodeCallable entries term with
  | some closure => .callable closure
  | none =>
      match decodeData term with
      | some data => .data data
      | none => .foreignData term

def serializePublic (entries : List Entry) : NativeValue → Option ForeignTerm
  | .data value => some (serializeData value)
  | .callable value => serializeCallable entries value
  | .foreignData value => some value

theorem capture_images_correspond (captures : List Atom) :
    serializeData.serializeList captures = captures.map Reference.dataImage := by
  rw [serializeList_eq_map]
  apply List.map_congr_left
  intro capture _
  exact data_images_correspond capture

theorem decode_reference_captures (captures : List Atom) :
    decodeData.decodeList (captures.map Reference.dataImage) = some captures := by
  rw [← capture_images_correspond, serializeList_eq_map]
  exact decode_serialized_list captures

/-- Foreign serialization agrees with the reference image for each actual
prepared occurrence and every ordered capture environment. -/
theorem prepared_serialization_correspondence (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) (captures : List Atom) :
    serializeCallable (dictionary scope counter sources)
      (NominalCallables.close reference.name reference.source captures) =
      some (Reference.callableImage scope (NominalCallables.Reference.close reference.name captures)) := by
  have lookup := prepared_token_lookup scope counter sources reference present
  cases captures <;>
    simp [serializeCallable, NominalCallables.close, lookup,
      NominalCallables.Reference.close, Reference.callableImage, capture_images_correspond]

/-- The decoder retrieves the original executable code held by the owner
dictionary. The public name and partial payload alone do not carry that code. -/
theorem prepared_reference_decoding (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) (captures : List Atom) :
    decodeCallable (dictionary scope counter sources)
      (Reference.callableImage scope (NominalCallables.Reference.close reference.name captures)) =
      some (NominalCallables.close reference.name reference.source captures) := by
  have lookup := prepared_name_lookup scope counter sources reference present
  cases captures with
  | nil =>
      simp [NominalCallables.Reference.close, Reference.callableImage, decodeCallable, lookup,
        NominalCallables.close]
  | cons first rest =>
      have decoded := decode_reference_captures (first :: rest)
      simp only [List.map_cons] at decoded
      simp only [NominalCallables.Reference.close, Reference.callableImage, List.map_cons, decodeCallable]
      rw [lookup, decoded]
      rfl

theorem prepared_callable_roundtrip (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) (captures : List Atom) :
    (serializeCallable (dictionary scope counter sources)
      (NominalCallables.close reference.name reference.source captures)).bind
      (decodeCallable (dictionary scope counter sources)) =
      some (NominalCallables.close reference.name reference.source captures) := by
  rw [prepared_serialization_correspondence scope counter sources reference present captures]
  exact prepared_reference_decoding scope counter sources reference present captures

/-- Further partial application appends arguments in the declared order and
keeps the same retained code; it does not allocate a new source occurrence. -/
theorem prepared_partial_roundtrip (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources)
    (captures arguments : List Atom) :
    (serializeCallable (dictionary scope counter sources)
      (NominalCallables.bind (NominalCallables.close reference.name reference.source captures) arguments)).bind
      (decodeCallable (dictionary scope counter sources)) =
      some (NominalCallables.bind (NominalCallables.close reference.name reference.source captures) arguments) := by
  exact prepared_callable_roundtrip scope counter sources reference present (captures ++ arguments)

/-- Closing an actual corresponding prepared plan, including its capture-slot
layout, is covered by the exact code/capture roundtrip. -/
theorem prepared_instantiation_roundtrip (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources)
    (plan : NominalCallables.Plan) (related : NominalCallables.RelatedPlan reference plan)
    (environment : Nat → Atom) :
    (serializeCallable (dictionary scope counter sources) (NominalCallables.instantiate environment plan)).bind
      (decodeCallable (dictionary scope counter sources)) = some (NominalCallables.instantiate environment plan) := by
  rcases related with ⟨code, slots⟩
  have instanceCode : NominalCallables.instantiate environment plan =
      NominalCallables.close reference.name reference.source (reference.source.captureSlots.map environment) := by
    simp [NominalCallables.instantiate, NominalCallables.close, code, slots, NominalCallables.gather_eq_map]
  rw [instanceCode]
  exact prepared_callable_roundtrip scope counter sources reference present _

theorem roundtrip_preserves_public_observation (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) (captures : List Atom)
    (observer : CallableObservationBoundary.Observer) :
    ((serializeCallable (dictionary scope counter sources)
      (NominalCallables.close reference.name reference.source captures)).bind
      (decodeCallable (dictionary scope counter sources))).map
      (CallableObservationBoundary.observeNative observer) =
      some (CallableObservationBoundary.observeReference observer
        (NominalCallables.Reference.close reference.name captures)) := by
  rw [prepared_callable_roundtrip scope counter sources reference present captures]
  simp only [Option.map_some]
  exact congrArg some (CallableObservationBoundary.close_observation_correspondence observer _ _ _)

theorem roundtrip_preserves_nominal_comparison (scope : String) (counter : Nat)
    (sources : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter sources) (captures : List Atom)
    (otherToken : Nat) (otherSource : NominalCallables.Declaration) (otherCaptures : List Atom) :
    ((serializeCallable (dictionary scope counter sources)
      (NominalCallables.close reference.name reference.source captures)).bind
      (decodeCallable (dictionary scope counter sources))).map
      (fun decoded => NominalCallables.same decoded (NominalCallables.close otherToken otherSource otherCaptures)) =
      some (NominalCallables.Reference.same (NominalCallables.Reference.close reference.name captures)
        (NominalCallables.Reference.close otherToken otherCaptures)) := by
  rw [prepared_callable_roundtrip scope counter sources reference present captures]
  simp only [Option.map_some]
  exact congrArg some (NominalCallables.closed_observer_correspondence ..)

theorem unknown_atom_remains_data (entries : List Entry) (name : String)
    (unknown : lookupName name entries = none) :
    decodePublic entries (.atom name) = .data (.symbol name) := by
  simp [decodePublic, decodeCallable, unknown, decodeData]

/-- Ordinary expression data is sent as a list, regardless of its head. The
callable decoder never treats Lam/partial list spellings as private values. -/
theorem source_expression_roundtrip (entries : List Entry) (elements : List Atom) :
    decodePublic entries (serializeData (.expression elements)) = .data (.expression elements) := by
  simp [serializeData, serializeList_eq_map, decodePublic, decodeCallable, decodeData, decode_serialized_list]

theorem unknown_partial_compound_remains_foreign_data (entries : List Entry) (name : String)
    (unknown : lookupName name entries = none) (first : ForeignTerm) (rest : List ForeignTerm) :
    decodePublic entries (.compound "partial" [.atom name, .list (first :: rest)]) =
      .foreignData (.compound "partial" [.atom name, .list (first :: rest)]) := by
  simp [decodePublic, decodeCallable, unknown, decodeData]

theorem empty_partial_is_outside_canonical_callable_image (entries : List Entry) (name : String) :
    decodePublic entries (.compound "partial" [.atom name, .list []]) =
      .foreignData (.compound "partial" [.atom name, .list []]) := by
  simp [decodePublic, decodeCallable, decodeData]

theorem translation_append (counter : Nat) (earlier later : List NominalCallables.Declaration) :
    NominalCallables.Reference.translate counter (earlier ++ later) =
      NominalCallables.Reference.translate counter earlier ++
        NominalCallables.Reference.translate (counter + earlier.length) later := by
  induction earlier generalizing counter with
  | nil => simp [NominalCallables.Reference.translate]
  | cons source rest ih =>
      simpa only [List.cons_append, translation_cons, List.length_cons,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (List.cons (⟨counter + 1, source⟩ : NominalCallables.Reference.Definition))
          (ih (counter + 1))

/-- Retaining additional prepared source occurrences preserves lookup of all
old code, not merely the nominal comparison of its public name. -/
theorem dictionary_extension_preserves_old_code (scope : String) (counter : Nat)
    (earlier later : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter earlier) :
    lookupName (generatedName scope reference.name) (dictionary scope counter (earlier ++ later)) =
      lookupName (generatedName scope reference.name) (dictionary scope counter earlier) := by
  have extended : reference ∈ NominalCallables.Reference.translate counter (earlier ++ later) := by
    rw [translation_append]
    exact List.mem_append_left _ present
  rw [prepared_name_lookup scope counter (earlier ++ later) reference extended,
    prepared_name_lookup scope counter earlier reference present]

theorem extended_owner_roundtrip (scope : String) (counter : Nat)
    (earlier later : List NominalCallables.Declaration) (reference : NominalCallables.Reference.Definition)
    (present : reference ∈ NominalCallables.Reference.translate counter earlier) (captures : List Atom) :
    (serializeCallable (dictionary scope counter (earlier ++ later))
      (NominalCallables.close reference.name reference.source captures)).bind
      (decodeCallable (dictionary scope counter (earlier ++ later))) =
      some (NominalCallables.close reference.name reference.source captures) := by
  apply prepared_callable_roundtrip
  rw [translation_append]
  exact List.mem_append_left _ present

namespace Controls

def source : NominalCallables.Declaration := ⟨["x"], .bvar 0, []⟩
def reference : NominalCallables.Reference.Definition := ⟨1, source⟩
def entries : List Entry := dictionary "runtime" 0 [source]
def captures : List Atom := [.var "shared", .grounded (.int 42), .var "shared"]

theorem reference_present : reference ∈ NominalCallables.Reference.translate 0 [source] := by
  simp [NominalCallables.Reference.translate, reference]

theorem closed_value_has_registered_atom_image :
    serializeCallable entries (NominalCallables.close 1 source []) =
      some (.atom (generatedName "runtime" 1)) := by
  simpa [entries, reference, Reference.callableImage, NominalCallables.Reference.close] using
    prepared_serialization_correspondence "runtime" 0 [source] reference reference_present []

theorem captured_value_has_compound_image :
    serializeCallable entries (NominalCallables.close 1 source captures) =
      some (.compound "partial" [.atom (generatedName "runtime" 1),
        .list [.var "shared", .grounded (.int 42), .var "shared"]]) := by
  simpa [entries, reference, captures, Reference.callableImage, NominalCallables.Reference.close,
    Reference.dataImage] using
    prepared_serialization_correspondence "runtime" 0 [source] reference reference_present captures

theorem closed_code_roundtrip :
    (serializeCallable entries (NominalCallables.close 1 source [])).bind
      (decodeCallable entries) = some (NominalCallables.close 1 source []) :=
  prepared_callable_roundtrip "runtime" 0 [source] reference reference_present []

theorem variable_and_duplicate_capture_roundtrip :
    (serializeCallable entries (NominalCallables.close 1 source captures)).bind
      (decodeCallable entries) = some (NominalCallables.close 1 source captures) :=
  prepared_callable_roundtrip "runtime" 0 [source] reference reference_present captures

theorem further_partial_application_roundtrip :
    (serializeCallable entries (NominalCallables.bind
      (NominalCallables.close 1 source [.grounded (.int 42)]) [.var "shared", .var "shared"])).bind
      (decodeCallable entries) = some (NominalCallables.close 1 source
        [.grounded (.int 42), .var "shared", .var "shared"]) :=
  prepared_partial_roundtrip "runtime" 0 [source] reference reference_present
    [.grounded (.int 42)] [.var "shared", .var "shared"]

theorem recovered_code_is_original_prepared_code :
    ((serializeCallable entries (NominalCallables.close 1 source captures)).bind
      (decodeCallable entries)).map NominalCallables.Closure.code =
      some (NominalCallables.canonical 1 source) := by
  rw [variable_and_duplicate_capture_roundtrip]
  rfl

theorem retained_owner_extension_keeps_old_code :
    lookupName (generatedName "runtime" 1) (dictionary "runtime" 0 [source, source]) =
      lookupName (generatedName "runtime" 1) entries :=
  dictionary_extension_preserves_old_code "runtime" 0 [source] [source] reference reference_present

theorem lost_dictionary_preserves_atom_but_loses_code :
    serializeCallable [] (NominalCallables.close 1 source []) = none ∧
    decodePublic [] (.atom (generatedName "runtime" 1)) = .data (.symbol (generatedName "runtime" 1)) ∧
    ∀ closure, decodePublic [] (.atom (generatedName "runtime" 1)) ≠ .callable closure := by
  simp [serializeCallable, NominalCallables.close, lookupToken, decodePublic, decodeCallable, lookupName, decodeData]

theorem lost_dictionary_keeps_partial_as_foreign_data :
    decodePublic [] (.compound "partial" [.atom (generatedName "runtime" 1), .list [.var "shared"]]) =
      .foreignData (.compound "partial" [.atom (generatedName "runtime" 1), .list [.var "shared"]]) :=
  unknown_partial_compound_remains_foreign_data [] _ rfl _ []

/-- Encoding a callable as an authored list loses its callable classification
even when the dictionary still owns its executable code. -/
theorem list_encoded_callable_is_not_a_partial_compound :
    decodeCallable entries
      (.list [.atom "partial", .atom (generatedName "runtime" 1), .list [.var "shared"]]) = none ∧
    decodePublic entries
      (.list [.atom "partial", .atom (generatedName "runtime" 1), .list [.var "shared"]]) =
      .data (.expression [.symbol "partial", .symbol (generatedName "runtime" 1),
        .expression [.var "shared"]]) := by
  simp [decodePublic, decodeCallable, decodeData, decodeData.decodeList]

theorem quoted_lam_data_roundtrip :
    decodePublic entries (serializeData (.expression [.symbol "Lam", .expression [.symbol "Type"],
      .expression [.symbol "body", .var "x"]])) =
      .data (.expression [.symbol "Lam", .expression [.symbol "Type"], .expression [.symbol "body", .var "x"]]) :=
  source_expression_roundtrip entries _

theorem quoted_partial_data_roundtrip :
    decodePublic entries (serializeData (.expression [.symbol "partial", .symbol (generatedName "runtime" 1),
      .expression [.var "shared"]])) =
      .data (.expression [.symbol "partial", .symbol (generatedName "runtime" 1), .expression [.var "shared"]]) :=
  source_expression_roundtrip entries _

theorem unknown_name_is_ordinary :
    decodePublic entries (.atom "ordinary") = .data (.symbol "ordinary") := by
  apply unknown_atom_remains_data
  decide

theorem empty_foreign_partial_is_not_collapsed_to_bare_name :
    decodePublic entries (.compound "partial" [.atom (generatedName "runtime" 1), .list []]) =
      .foreignData (.compound "partial" [.atom (generatedName "runtime" 1), .list []]) :=
  empty_partial_is_outside_canonical_callable_image entries _

end Controls

end Mettapedia.Machines.IncrementalConformance.CallableForeignBoundary
