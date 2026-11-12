import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.HEFootprints

/-!
# Declared service footprints, with a frame obligation

`HEFootprints` let every move through HE's cast lookup or argument admission read the whole space,
since those services are parameters of the machine. Here a service may **declare** a footprint: a
region of rows, together with a proof that its answers do not change when the space changes
outside the region (`Frames`, the frame rule of separation logic, stated for a relation that reads
a space). A service that declares nothing reads the whole space, and that default always meets the
obligation (`frames_whole`).

## Results

* `storage_frames`, `occurrences_frames`: HE's type queries (the list-storage profile
  `StorageTypesRel`, and the source collection `TypeOccurrencesRel`) meet the obligation for
  `typeRegion subject`: the rows `(: subject T)` when the subject is a symbol or a non-empty
  expression, and no row otherwise (variables, grounded values and `()` have intrinsic types).
* `rawDeclared`, `scopedDeclared`: HE's two specified cast lookups (`Completed.rawLookup`, the
  historical list storage, and `Completed.scopedLookup`, the same with fresh variants) declare
  `typeRegion`. `wholeDeclared` declares any lookup with the whole space.
* `historical_frames`: HE's historical argument admission (`ArgumentService.historical`) meets the
  obligation for `admissionRegion`: the lookup's region of the operator and of each argument. The
  application checks read the space only through the lookup, at the arguments.
* `localStep_transfer_declared`, `he_worldLocal_declared`, `he_rows_on_the_step_declared`: with a
  declared lookup, HE's machine is world-local for the **declared footprint** `heFootD`, which
  replaces the whole space at the type-directed entry by the declared regions: a cast reads the
  lookup's region of its value, an interpretation reads the declarations of its operator and the
  admission's region. The strong bisimulation of `HEFootprints` holds for this smaller footprint.

## Controls

* `Controls.peeking_fails` (negative): a type lookup that answers `Number` when `(p a)` is present
  fails the obligation for `typeRegion`, though it meets it for the whole space; no declared lookup
  with region `typeRegion` is that lookup.
* `Controls.entry_reads_no_row` (positive): at the entry of `(double 4)` on
  `{(p a), (= (double 4) 8)}`, the declared footprint of the interpretation holds no row of the
  program, where `HEFootprints` read both rows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace ServiceFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultSet ResultPair)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (annotationType? annotationOccurrences
  AnnotationTypesRel StorageTypesRel TypeOccurrencesRel TypeCastBatchRel TypeLookupRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup ArgumentService
  InvocationSelection InvocationScanRel ApplicationChecksRel ApplicabilityArgumentsRel
  ArgumentChecksRel CastResultRel Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation Task)
open HEOnTheStep (heMachine he_local toConfig HEConfig Store Cell)
open FragmentsOfTheStep.TransitionMaps

/-! ## Rows of a region, in order -/

section Lists

variable {X : Type}

/-- The rows of a region, in order, are the first components of its positioned rows. -/
theorem map_fst_regionRows (ρ : X → Bool) (rows : List X) :
    (regionRows ρ rows).map Prod.fst = rows.filter ρ := by
  unfold regionRows
  suffices shifted : ∀ k : ℕ, ((rows.zipIdx k).filter fun p => ρ p.1).map Prod.fst = rows.filter ρ from
    shifted 0
  induction rows with
  | nil => intro k; rfl
  | cons x rows ih =>
      intro k
      rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
      by_cases inside : ρ x = true
      · simp [inside, ih (k + 1)]
      · simp [inside, ih (k + 1)]

/-- Two worlds with the same positioned rows of a region hold the same rows of it, in order. -/
theorem filter_eq_of_regionRows_eq {ρ : X → Bool} {rows rows₀ : List X}
    (same : regionRows ρ rows = regionRows ρ rows₀) : rows.filter ρ = rows₀.filter ρ := by
  rw [← map_fst_regionRows, ← map_fst_regionRows, same]

/-- Rows that agree on a region agree on every smaller region. -/
theorem filter_eq_of_sub {ρ σ : X → Bool} {rows rows₀ : List X}
    (sub : ∀ x, σ x = true → ρ x = true) (same : rows.filter ρ = rows₀.filter ρ) :
    rows.filter σ = rows₀.filter σ := by
  have shrink : ∀ l : List X, l.filter σ = (l.filter ρ).filter σ := by
    intro l
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases inside : σ x = true
    · simp [inside, sub x inside]
    · simp [inside]
  rw [shrink rows, shrink rows₀, same]

/-- Only the rows a partial map keeps contribute to it. -/
theorem filterMap_filter_isSome {Y : Type} (f : X → Option Y) :
    ∀ l : List X, (l.filter fun x => (f x).isSome).filterMap f = l.filterMap f
  | [] => rfl
  | x :: l => by
      cases found : f x with
      | none => simp [found, filterMap_filter_isSome f l]
      | some y => simp [found, filterMap_filter_isSome f l]

end Lists

/-! ## The frame obligation -/

section Frames

/-- **The frame obligation** of a service reading a space: when two spaces hold the same rows of
the declared region, in the same order, every answer the service gives on the first it gives on the
second. Changes outside the region are not observed. -/
def Frames {I O : Type} (service : Space → I → O → Prop) (region : I → Atom → Bool) : Prop :=
  ∀ {space space₀ : Space} {input : I},
    space.atoms.filter (region input) = space₀.atoms.filter (region input) →
      ∀ output, service space input output → service space₀ input output

/-- The obligation holds both ways. -/
theorem Frames.iff {I O : Type} {service : Space → I → O → Prop} {region : I → Atom → Bool}
    (frames : Frames service region) {space space₀ : Space} {input : I}
    (same : space.atoms.filter (region input) = space₀.atoms.filter (region input)) (output : O) :
    service space input output ↔ service space₀ input output :=
  ⟨frames same output, frames same.symm output⟩

/-- The whole space, the footprint of a service that declares nothing. -/
def whole {I : Type} : I → Atom → Bool := fun _ _ => true

theorem space_eq_of_filter_whole {space space₀ : Space}
    (same : space.atoms.filter (fun _ => true) = space₀.atoms.filter (fun _ => true)) :
    space = space₀ := by
  obtain ⟨atoms⟩ := space
  obtain ⟨atoms₀⟩ := space₀
  simp only [List.filter_true] at same
  subst same
  rfl

/-- **The sound default: every service meets the frame obligation for the whole space.** -/
theorem frames_whole {I O : Type} (service : Space → I → O → Prop) :
    Frames service (whole (I := I)) := by
  intro space space₀ input same output holds
  rw [← space_eq_of_filter_whole same]
  exact holds

end Frames

/-! ## HE's type queries -/

section TypeQueries

/-- **The footprint of a type query**: the declaration rows `(: subject T)` of a symbol or a
non-empty expression. A variable, a grounded value or `()` has an intrinsic type and reads no row. -/
def typeRegion : Atom → Atom → Bool
  | .symbol name, row => (annotationType? (.symbol name) row).isSome
  | .expression (head :: tail), row => (annotationType? (.expression (head :: tail)) row).isSome
  | _, _ => false

theorem annotations_of_filter {target : Atom} {l l₀ : List Atom}
    (same : l.filter (fun row => (annotationType? target row).isSome) =
      l₀.filter (fun row => (annotationType? target row).isSome)) :
    l.filterMap (annotationType? target) = l₀.filterMap (annotationType? target) := by
  rw [← filterMap_filter_isSome, same, filterMap_filter_isSome]

theorem annotation_transport {target : Atom} {l l₀ types : List Atom}
    (same : l.filterMap (annotationType? target) = l₀.filterMap (annotationType? target))
    (extracted : AnnotationTypesRel target l types) : AnnotationTypesRel target l₀ types := by
  have listed : types = l.filterMap (annotationType? target) :=
    ((AnnotationTypesRel.complete target l).unique extracted).symm
  rw [listed, same]
  exact AnnotationTypesRel.complete target l₀

/-- A row that is no declaration is outside every type region. -/
theorem typeRegion_not_declaration {row : Atom}
    (notDeclaration : ∀ subject type, row ≠ .expression [.symbol ":", subject, type])
    (subject : Atom) : typeRegion subject row = false := by
  have none : ∀ target, annotationType? target row = none := by
    intro target
    cases found : annotationType? target row with
    | none => rfl
    | some type =>
        exact absurd (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType?_eq_some_iff.mp found)
          (notDeclaration target type)
  cases subject with
  | symbol name => simp [typeRegion, none]
  | var name => rfl
  | grounded value => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head tail => simp [typeRegion, none]

/-- **HE's list-storage type query meets the frame obligation for `typeRegion`.** -/
theorem storage_frames :
    Frames (fun space (subject : Atom) types => StorageTypesRel space subject types) typeRegion := by
  intro space space₀ subject same types queried
  cases queried with
  | «variable» => exact .variable _ _
  | groundedKnown intrinsic ordinary => exact .groundedKnown intrinsic ordinary
  | groundedUndefined intrinsic => exact .groundedUndefined intrinsic
  | @symbolKnown name _ annotations nonempty =>
      exact .symbolKnown (annotation_transport
        (annotations_of_filter (target := .symbol name) same) annotations) nonempty
  | @symbolUndefined name annotations =>
      exact .symbolUndefined (annotation_transport
        (annotations_of_filter (target := .symbol name) same) annotations)
  | unit => exact .unit _
  | @expressionKnown head tail _ annotations nonempty =>
      exact .expressionKnown (annotation_transport
        (annotations_of_filter (target := .expression (head :: tail)) same) annotations) nonempty
  | @expressionUndefined head tail annotations =>
      exact .expressionUndefined (annotation_transport
        (annotations_of_filter (target := .expression (head :: tail)) same) annotations)

theorem occurrences_of_filter {target : Atom} {l l₀ : List Atom}
    (same : l.filter (fun row => (annotationType? target row).isSome) =
      l₀.filter (fun row => (annotationType? target row).isSome)) :
    annotationOccurrences (l : Multiset Atom) target = annotationOccurrences (l₀ : Multiset Atom) target := by
  unfold annotationOccurrences
  rw [Multiset.filterMap_coe, Multiset.filterMap_coe, annotations_of_filter same]

/-- **HE's source type collection meets the frame obligation for `typeRegion`.** -/
theorem occurrences_frames :
    Frames (fun space (subject : Atom) types =>
      TypeOccurrencesRel (space.atoms : Multiset Atom) subject types) typeRegion := by
  intro space space₀ subject same types collected
  cases collected with
  | «variable» name => exact .variable name
  | grounded intrinsic => exact .grounded intrinsic
  | symbol name =>
      rw [occurrences_of_filter (target := .symbol name) same]
      exact .symbol name
  | unit => exact .unit
  | expression head tail =>
      rw [occurrences_of_filter (target := .expression (head :: tail)) same]
      exact .expression head tail

end TypeQueries

/-! ## Declared cast lookups -/

section Lookups

/-- **A declared cast lookup**: a lookup of the machine, the region each subject's query reads, and
the frame obligation for it, at every protected scope, binding state and demand. -/
structure DeclaredLookup where
  lookup : CastLookup
  region : Atom → Atom → Bool
  frames : ∀ {scope : List String} {space space₀ : Space} {bindings : Bindings}
    {subject expected : Atom} {types : List Atom},
    space.atoms.filter (region subject) = space₀.atoms.filter (region subject) →
      lookup scope space bindings subject expected types →
        lookup scope space₀ bindings subject expected types

/-- **HE's historical list-storage lookup declares `typeRegion`.** -/
def rawDeclared : DeclaredLookup where
  lookup := Completed.rawLookup
  region := typeRegion
  frames := fun same queried => storage_frames same _ queried

/-- **HE's scoped lookup (fresh variants of the stored declarations) declares `typeRegion`.** -/
def scopedDeclared : DeclaredLookup where
  lookup := Completed.scopedLookup
  region := typeRegion
  frames := by
    intro scope space space₀ bindings subject expected types same queried
    obtain ⟨raw, stored, variants⟩ := queried
    exact Exists.intro raw ⟨storage_frames same raw stored, variants⟩

/-- **The default: any lookup, declared with the whole space.** -/
def wholeDeclared (lookup : CastLookup) : DeclaredLookup where
  lookup := lookup
  region := whole
  frames := by
    intro scope space space₀ bindings subject expected types same queried
    rw [← space_eq_of_filter_whole same]
    exact queried

end Lookups

/-! ## HE's argument admission -/

section Admission

variable {space space₀ : Space} {L L₀ : TypeLookupRel} {policy : Policy}

theorem argumentChecks_transport {expression argument expected : Atom} {position : ℕ}
    {frames outputs : List Frame} {errors : List Atom}
    (agree : ∀ bindings demand types, L bindings argument demand types →
      L₀ bindings argument demand types)
    (checked : ArgumentChecksRel space L policy expression argument expected position frames outputs
      errors) :
    ArgumentChecksRel space₀ L₀ policy expression argument expected position frames outputs errors := by
  induction checked with
  | nil => exact .nil
  | cons queried paired _ ih => exact .cons (agree _ _ _ queried) paired ih

theorem applicability_transport {expression : Atom} {position : ℕ} {arguments types : List Atom}
    {before after : List Frame} {errors : List Atom}
    (checked : ApplicabilityArgumentsRel space L policy expression position arguments types before
      after errors) :
    (∀ argument ∈ arguments, ∀ bindings demand types, L bindings argument demand types →
      L₀ bindings argument demand types) →
    ApplicabilityArgumentsRel space₀ L₀ policy expression position arguments types before after
      errors := by
  induction checked with
  | nil => intro _; exact .nil
  | cons head _ ih =>
      intro agree
      exact .cons (argumentChecks_transport (agree _ List.mem_cons_self) head)
        (ih fun argument member => agree argument (List.mem_cons_of_mem _ member))

/-- The arguments of an application. -/
def argumentsOf : Atom → List Atom
  | .expression (_ :: arguments) => arguments
  | _ => []

theorem applicationChecks_transport {expression expected : Atom}
    {selected : SelectedTypePolicy} {before : Frame} {frames : List Frame}
    {errors : List Atom}
    (agree : ∀ argument ∈ argumentsOf expression, ∀ bindings demand types,
      L bindings argument demand types → L₀ bindings argument demand types)
    (checked : ApplicationChecksRel space L policy expression expected selected before frames errors) :
    ApplicationChecksRel space₀ L₀ policy expression expected selected before frames errors := by
  cases checked with
  | wrongArity shape arity => exact .wrongArity shape arity
  | checked shape arguments returned =>
      subst shape
      exact .checked rfl (applicability_transport arguments agree) returned

theorem invocationScan_transport {expression expected : Atom} {before : Frame}
    {candidates : List Atom} {outcome : InvocationSelection}
    (agree : ∀ argument ∈ argumentsOf expression, ∀ bindings demand types,
      L bindings argument demand types → L₀ bindings argument demand types)
    (scanned : InvocationScanRel space L policy expression expected before candidates outcome) :
    InvocationScanRel space₀ L₀ policy expression expected before candidates outcome := by
  induction scanned with
  | nil => exact .nil
  | nonFunction notArrow _ ih => exact .nonFunction notArrow ih
  | selected checked nonempty => exact .selected (applicationChecks_transport agree checked) nonempty
  | rejected checked _ ih => exact .rejected (applicationChecks_transport agree checked) ih

/-- **The declared footprint of argument admission**: the lookup's region of the operator and of
each argument of the expression. -/
def admissionRegion (region : Atom → Atom → Bool) (expression operator : Atom) : Atom → Bool :=
  fun row => region operator row || (argumentsOf expression).any fun argument => region argument row

/-- **HE's historical argument admission meets the frame obligation for `admissionRegion`.** -/
theorem historical_frames (D : DeclaredLookup) {live : List Atom} {scope : List String}
    {expression operator expected : Atom} {before : Frame} {outcome : InvocationSelection}
    (same : space.atoms.filter (admissionRegion D.region expression operator) =
      space₀.atoms.filter (admissionRegion D.region expression operator))
    (selected : ArgumentService.historical.selection space D.lookup policy live scope expression
      operator expected before outcome) :
    ArgumentService.historical.selection space₀ D.lookup policy live scope expression operator
      expected before outcome := by
  obtain ⟨candidates, queried, scanned⟩ := selected
  have operatorSame : space.atoms.filter (D.region operator) =
      space₀.atoms.filter (D.region operator) :=
    filter_eq_of_sub (fun row inside => by simp [admissionRegion, inside]) same
  have argumentSame : ∀ argument ∈ argumentsOf expression,
      space.atoms.filter (D.region argument) = space₀.atoms.filter (D.region argument) := by
    intro argument member
    apply filter_eq_of_sub _ same
    intro row inside
    simp only [admissionRegion, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨argument, member, inside⟩
  exact Exists.intro candidates ⟨D.frames operatorSame queried,
    invocationScan_transport (fun argument member _ _ _ holds =>
      D.frames (argumentSame argument member) holds) scanned⟩

end Admission

/-! ## HE's machine with declared footprints -/

section Machine

/-- The region an interpretation of an application reads: the declarations of its operator (the
type-directed entry decides between tuple evaluation and admission) and the admission's region. -/
def interpretRegion (D : DeclaredLookup) (expression : Atom) : Atom → Bool :=
  match expression with
  | .expression (operator :: _) => fun row =>
      typeRegion operator row || admissionRegion D.region expression operator row
  | _ => fun _ => false

open Classical in
/-- The declared region of an atom's pending work: delivering reads nothing; a cast reads the
lookup's region of its value; an interpretation reads `interpretRegion`. -/
def atomRegionD (D : DeclaredLookup) (policy : Policy) (value : Entry.Value) (expected : Atom)
    (activation : Frame) : Atom → Bool :=
  if Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .deliver then fun _ => false
  else if Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .cast then
    D.region (activation.read policy value).erase
  else interpretRegion D (activation.read policy value).erase

/-- **HE's declared region of a move**: an atom's pending work reads its declared region; every other
move reads what `HEFootprints.heRegion` reads. -/
def heRegionD (D : DeclaredLookup) (policy : Policy) (before after : Control) : Atom → Bool :=
  match before with
  | .work (.atom _ _ value expected activation) => atomRegionD D policy value expected activation
  | _ => heRegion policy before after

/-- **HE's declared footprint.** -/
def heFootD (D : DeclaredLookup) (policy : Policy) : Footprint Control Continuation Atom :=
  fun before _ after _ => heRegionD D policy before after

theorem heRegionD_of_not_atom {D : DeclaredLookup} {policy : Policy} {before after : Control}
    (notAtom : ¬ ∃ live scope value expected activation,
      before = .work (.atom live scope value expected activation)) :
    heRegionD D policy before after = heRegion policy before after := by
  unfold heRegionD
  split
  · exact absurd ⟨_, _, _, _, _, rfl⟩ notAtom
  · rfl

theorem heRegionD_cast {D : DeclaredLookup} {policy : Policy} {live : List Atom}
    {scope : List String} {value : Entry.Value} {expected : Atom} {activation : Frame}
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .cast) (after : Control) :
    heRegionD D policy (.work (.atom live scope value expected activation)) after =
      D.region (activation.read policy value).erase := by
  have notDeliver : ¬ Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .deliver := fun deliver =>
    absurd (Entry.functional entry deliver) (by decide)
  show atomRegionD D policy value expected activation = _
  simp [atomRegionD, notDeliver, entry]

theorem heRegionD_interpret {D : DeclaredLookup} {policy : Policy} {live : List Atom}
    {scope : List String} {value : Entry.Value} {expected : Atom} {activation : Frame}
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .interpret) (after : Control) :
    heRegionD D policy (.work (.atom live scope value expected activation)) after =
      interpretRegion D (activation.read policy value).erase := by
  have notDeliver : ¬ Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .deliver := fun deliver =>
    absurd (Entry.functional entry deliver) (by decide)
  have notCast : ¬ Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .cast := fun cast =>
    absurd (Entry.functional entry cast) (by decide)
  show atomRegionD D policy value expected activation = _
  simp [atomRegionD, notDeliver, notCast]

theorem erase_shape {value : Entry.Value} {readiness : Entry.Status}
    {operator : Entry.Value} {arguments : List Entry.Value}
    (shape : value = .expression readiness (operator :: arguments)) :
    value.erase = .expression (operator.erase :: arguments.map Entry.Value.erase) := by
  subst shape
  simp [Entry.Value.erase]

/-- The type region of the operator lies in the interpretation's region. -/
theorem typeRegion_sub_interpret (D : DeclaredLookup) {value : Entry.Value}
    {readiness : Entry.Status} {operator : Entry.Value} {arguments : List Entry.Value}
    (shape : value = .expression readiness (operator :: arguments)) (row : Atom)
    (inside : typeRegion operator.erase row = true) : interpretRegion D value.erase row = true := by
  rw [erase_shape shape]
  simp [interpretRegion, inside]

/-- The admission's region lies in the interpretation's region. -/
theorem admission_sub_interpret (D : DeclaredLookup) {value : Entry.Value}
    {readiness : Entry.Status} {operator : Entry.Value} {arguments : List Entry.Value}
    (shape : value = .expression readiness (operator :: arguments)) (row : Atom)
    (inside : admissionRegion D.region value.erase operator.erase row = true) :
    interpretRegion D value.erase row = true := by
  rw [erase_shape shape] at inside ⊢
  simp only [interpretRegion, Bool.or_eq_true]
  exact Or.inr inside

theorem castBatch_transport {space space₀ : Space} {atom expected : Atom} {bindings : Bindings}
    {results : ResultSet} {L L₀ : TypeLookupRel}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (agree : ∀ types, L bindings atom expected types → L₀ bindings atom expected types)
    (source : TypeCastBatchRel space atom expected bindings results (lookup := L)
      (matching := matching)) :
    TypeCastBatchRel space₀ atom expected bindings results (lookup := L₀) (matching := matching) := by
  cases source with
  | success queried selected rejected matched =>
      exact .success (agree _ queried) selected rejected matched
  | failure queried rejected => exact .failure (agree _ queried) rejected

theorem castRenew_transport {policy : Policy} {L L₀ : TypeLookupRel} {original expected : Atom}
    {before after : Frame}
    (agree : ∀ types, L before.bindings original expected types →
      L₀ before.bindings original expected types)
    (renewed : Frame.CastRenewRel policy L original expected before after) :
    Frame.CastRenewRel policy L₀ original expected before after := by
  cases renewed with
  | same => exact .same _
  | matched queried selected rejected matched unified =>
      exact .matched (agree _ queried) selected rejected matched unified

theorem castResult_transport {policy : Policy} {L L₀ : TypeLookupRel} {before : Frame}
    {original : Entry.Value} {expected : Atom} {raw : ResultPair} {result : Result}
    (agree : ∀ types, L before.bindings original.erase expected types →
      L₀ before.bindings original.erase expected types)
    (related : CastResultRel policy L before original expected raw result) :
    CastResultRel policy L₀ before original expected raw result :=
  ⟨related.readout, castRenew_transport agree related.renewed, related.payload⟩

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **Every transition of HE's machine depends on the space only through its declared footprint.**
The five moves of the type-directed entry use the frame obligations of the declared lookup, of
HE's type collection and of HE's historical admission; every other move is `localStep_transfer`. -/
theorem localStep_transfer_declared (D : DeclaredLookup) {space space₀ : Space}
    {c c' : Control} {s s' : List Continuation}
    (step : LocalStepWith .historical space dispatch D.lookup policy (c, s) (c', s'))
    (same : regionRows (heRegionD D policy c c') space.atoms =
      regionRows (heRegionD D policy c c') space₀.atoms) :
    LocalStepWith .historical space₀ dispatch D.lookup policy (c, s) (c', s') := by
  by_cases atomWork : ∃ live scope value expected activation,
      c = .work (.atom live scope value expected activation)
  · obtain ⟨live, scope, value, expected, activation, rfl⟩ := atomWork
    cases step
    case delivered => apply LocalStepWith.delivered; assumption
    case cast =>
      rename_i entry source paired
      rw [heRegionD_cast entry] at same
      have filtered := filter_eq_of_regionRows_eq same
      have agree : ∀ {scope' : List String} {bindings : Bindings} {demand : Atom}
          (types : List Atom),
          D.lookup scope' space bindings (activation.read policy value).erase demand types →
            D.lookup scope' space₀ bindings (activation.read policy value).erase demand types :=
        fun _ queried => D.frames filtered queried
      exact .cast entry (castBatch_transport (agree ·) source)
        (paired.imp fun _ _ related => castResult_transport (agree ·) related)
    case atomTuple =>
      have entry := ‹Entry.Rel _ _ _ _ .interpret›
      have shape := ‹_ = Entry.Value.expression _ (_ :: _)›
      rw [heRegionD_interpret entry] at same
      have filtered := filter_eq_of_regionRows_eq same
      have operatorSame := filter_eq_of_sub (typeRegion_sub_interpret D shape) filtered
      exact .atomTuple entry shape (occurrences_frames operatorSame _ ‹_›)
    case atomFunction =>
      have entry := ‹Entry.Rel _ _ _ _ .interpret›
      have shape := ‹_ = Entry.Value.expression _ (_ :: _)›
      rw [heRegionD_interpret entry] at same
      have filtered := filter_eq_of_regionRows_eq same
      have admissionSame := filter_eq_of_sub (admission_sub_interpret D shape) filtered
      exact .atomFunction entry shape (historical_frames D admissionSame ‹_›)
    case atomFallback =>
      have entry := ‹Entry.Rel _ _ _ _ .interpret›
      have shape := ‹_ = Entry.Value.expression _ (_ :: _)›
      rw [heRegionD_interpret entry] at same
      have filtered := filter_eq_of_regionRows_eq same
      have admissionSame := filter_eq_of_sub (admission_sub_interpret D shape) filtered
      exact .atomFallback entry shape (historical_frames D admissionSame ‹_›)
    case atomSelectionFailed =>
      have entry := ‹Entry.Rel _ _ _ _ .interpret›
      have shape := ‹_ = Entry.Value.expression _ (_ :: _)›
      rw [heRegionD_interpret entry] at same
      have filtered := filter_eq_of_regionRows_eq same
      have admissionSame := filter_eq_of_sub (admission_sub_interpret D shape) filtered
      exact .atomSelectionFailed entry shape (historical_frames D admissionSame ‹_›)
  · rw [heRegionD_of_not_atom atomWork] at same
    exact localStep_transfer step same

/-- **HE's machine is world-local for its declared footprint.** -/
theorem he_worldLocal_declared (D : DeclaredLookup) :
    WorldLocal (heMachine dispatch D.lookup policy) Space.atoms (heFootD D policy) := by
  intro space space₀ c c' pop push same framed base
  obtain ⟨_, step⟩ := framed base
  exact ⟨rfl, localStep_transfer_declared D step same⟩

/-- **HE on the step with declared footprints.** With a declared lookup, the step under HE's rules
with the declared footprint is strongly bisimilar to HE's machine: one transition is one firing,
which reads exactly the rows of its declared region and observes that the region holds nothing
else. -/
theorem he_rows_on_the_step_declared (D : DeclaredLookup) :
    IsBisimulation (RowStep (heMachine dispatch D.lookup policy) Space.atoms (heFootD D policy))
      (heMachine dispatch D.lookup policy).Step (RowRepresents Space.atoms) :=
  row_bisimulation he_local he_readOnly (he_worldLocal_declared D)

/-- **What a firing reads under the declared footprint**: the rows of its region, which is the
declared region of a move from the store's control, or the empty region of publication. -/
theorem he_reads_exact_declared (D : DeclaredLookup)
    {S S' : Store (Atom × ℕ) Control Continuation Result} {x : HEConfig}
    (represented : RowRepresents Space.atoms S (toConfig x))
    (step : RowStep (heMachine dispatch D.lookup policy) Space.atoms (heFootD D policy) S S') :
    ∃ (rule : RuleInstance (RowCell Atom Control Continuation Result)) (ρ : Atom → Bool),
      rule.read = (regionRows ρ x.space.atoms).map Cell.world ∧
      ((∃ c', ρ = heRegionD D policy x.control c') ∨ ρ = fun _ => false) := by
  obtain ⟨rule, ρ, _, reads, region⟩ := row_firing_region represented step
  refine ⟨rule, ρ, reads, ?_⟩
  rcases region with ⟨_, c', _, rfl⟩ | rfl
  · exact Or.inl ⟨c', rfl⟩
  · exact Or.inr rfl

end Machine

/-! ## Controls -/

namespace Controls

/-- `(p a)`. -/
def pa : Atom := .expression [.symbol "p", .symbol "a"]

/-- **A lookup that looks outside its declaration rows**: it answers `Number` for every subject when
`(p a)` is stored, and `%Undefined%` otherwise. -/
def peeking : Space → Atom → List Atom → Prop :=
  fun space _ types => types = if pa ∈ space.atoms then [.symbol "Number"] else [Atom.undefinedType]

theorem pa_not_declaration (subject : Atom) : typeRegion subject pa = false :=
  typeRegion_not_declaration (fun _ _ same => by simp [pa] at same) subject

/-- **Negative control: a service whose answer depends on a row outside its declared region fails
the obligation.** The peeking lookup fails it for `typeRegion` (the spaces `{}` and `{(p a)}` hold
the same declaration rows, and it answers differently), meets it for the whole space, and no
declared lookup with region `typeRegion` is that lookup. -/
theorem peeking_fails :
    ¬ Frames peeking typeRegion ∧ Frames peeking (whole (I := Atom)) ∧
      ¬ ∃ D : DeclaredLookup, D.region = typeRegion ∧
        ∀ space subject types, D.lookup [] space Bindings.empty subject Atom.undefinedType types ↔
          peeking space subject types := by
  have agree : (Space.ofList []).atoms.filter (typeRegion (.symbol "f")) =
      (Space.ofList [pa]).atoms.filter (typeRegion (.symbol "f")) := by
    simp [Space.ofList, pa_not_declaration]
  have before : peeking (Space.ofList []) (.symbol "f") [Atom.undefinedType] := by
    simp [peeking, Space.ofList]
  have after : ¬ peeking (Space.ofList [pa]) (.symbol "f") [Atom.undefinedType] := by
    simp [peeking, Space.ofList, Atom.undefinedType]
  refine ⟨fun frames => after (frames agree _ before), frames_whole peeking, ?_⟩
  rintro ⟨D, region, same⟩
  have agree' : (Space.ofList []).atoms.filter (D.region (.symbol "f")) =
      (Space.ofList [pa]).atoms.filter (D.region (.symbol "f")) := by
    rw [region]
    exact agree
  exact after ((same _ _ _).mp (D.frames agree' ((same _ _ _).mpr before)))

/-- `(double 4)`, `(= (double 4) 8)`, the program `{(p a), (= (double 4) 8)}`, and the declaration
`(: double Number)`. -/
def doubleFour : Atom := .expression [.symbol "double", .grounded (.int 4)]
def doubleEight : Atom := .expression [.symbol "=", doubleFour, .grounded (.int 8)]
def program : List Atom := [pa, doubleEight]
def declareDouble : Atom := .expression [.symbol ":", .symbol "double", .symbol "Number"]

/-- **Positive control: the entry of `(double 4)` reads no row of `{(p a), (= (double 4) 8)}`** under
the declared footprint of HE's raw lookup, where the whole-space footprint of `HEFootprints` reads
both rows. The region is not empty: it holds every declaration of `double`, such as
`(: double Number)`, so the entry's observation is an absence guard over them. -/
theorem entry_reads_no_row :
    regionRows (interpretRegion rawDeclared doubleFour) program = [] ∧
      regionRows (fun _ : Atom => true) program = [(pa, 0), (doubleEight, 1)] ∧
      interpretRegion rawDeclared doubleFour declareDouble = true ∧
      interpretRegion rawDeclared doubleFour pa = false := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;> decide +kernel

end Controls

#print axioms map_fst_regionRows
#print axioms filter_eq_of_sub
#print axioms frames_whole
#print axioms storage_frames
#print axioms occurrences_frames
#print axioms historical_frames
#print axioms localStep_transfer_declared
#print axioms he_worldLocal_declared
#print axioms he_rows_on_the_step_declared
#print axioms he_reads_exact_declared
#print axioms Controls.peeking_fails
#print axioms Controls.entry_reads_no_row

end ServiceFootprints

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
