import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericAgreement

/-!
# Schematic rows activated over intrinsic contextual binding terms

A stored schema keeps its code and captured arguments. Each activation extends
the declaration frame by the schema's own metavariables. The existing coproduct
opening supplies freshness, while the actual firing information retains the
capture equations. A compatible closure reading derives admission of an actual
held-rule firing; it is not an assumed operational correspondence.

This is a persistent, premiseless row-materialization discipline. It does not
identify fresh schema variables with object-bound variables or rigid names, and
does not assert that arbitrary higher-order equations are decidable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Rows

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open Interface.Frames (Frame)
open RuleOccurrences SchematicRows
open SchematicRows.HeldReadGenericSources

variable {S : Signature} {O R : Type}

/-- A held schema is opened at its own new contextual declarations. -/
def activation (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :=
  HeldReadGenericFirings.datum (E := Contextual.declarations S) ordinary rows closures selected
    (closures selected).schema.locals
    (Contextual.canonicalOpening S ordinary.frame (closures selected).schema.locals) output

/-- Freshness holds on all old terms and captured arguments, not merely a
chosen output. Object-variable scopes are intrinsic to these terms. -/
theorem activation_fresh (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :
    (activation ordinary rows closures selected output).Fresh (Frames.contextual S) := by
  intro target caller localAssignment
  refine ⟨Contextual.copair S caller localAssignment, ?_, ?_⟩
  · intro term _
    exact Contextual.copair_weaken S caller localAssignment term
  · intro term _
    exact Contextual.copair_opening S caller localAssignment term

theorem activation_rowClosure (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :
    SchematicRows.Opening.rowClosure (activation ordinary rows closures selected output)
      (closures selected).schema.value = closures selected := by
  rfl

variable [DecidableEq O] [DecidableEq R]

omit [DecidableEq R] in
/-- A source model and a compatible reading supply the actual firing model.
Physical allocation, presence and the capture-interface length are checked. -/
theorem activation_admitted_of_reading
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O)
    (present : selected ∈ rows) (fresh : output ∉ ordinary.present)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (caller : Assignment ordinary.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller ordinary.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures selected).ReadsAt (Frames.contextual S) caller value) :
    (activation ordinary rows closures selected output).Admits (Frames.contextual S) ∅ := by
  have shapes := HeldReadGenericFirings.datum_shapes (E := Contextual.declarations S)
    (Frames.contextual S) ordinary rows closures selected (closures selected).schema.locals
    (Contextual.canonicalOpening S ordinary.frame (closures selected).schema.locals) output ∅ present
    (activation_fresh ordinary rows closures selected output) wellFormed
  have enabled := HeldReadGenericFirings.datum_enabled (E := Contextual.declarations S)
    ordinary rows closures selected (closures selected).schema.locals
    (Contextual.canonicalOpening S ordinary.frame (closures selected).schema.locals) output fresh
  refine SchematicRows.Materialization.admits_of_reading (Frames.contextual S)
    (activation ordinary rows closures selected output) ∅ shapes enabled
    rfl rfl rfl rfl rfl rfl rfl rfl (closures selected).schema.value
    (List.mem_singleton_self _) caller known value ?_
  rwa [activation_rowClosure]

/-- At every solution, a captured parameter is the original ambient argument.
Neither copy is silently generalized to a fresh independent value. -/
theorem activation_captures
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (point : Assignment
      (Contextual.extend S ordinary.frame (closures selected).schema.locals).arity target.arity)
    (model : (Frames.contextual S).Models point
      ((activation ordinary rows closures selected output).result (Frames.contextual S)).knowledge) :
    List.Forall₂ (fun parameter argument =>
      instantiateObservation point
          (instantiateObservation
            (Contextual.canonicalOpening S ordinary.frame (closures selected).schema.locals) parameter) =
        instantiateObservation point
          (instantiateObservation
            (Contextual.weakenNames S ordinary.frame (closures selected).schema.locals) argument))
      (closures selected).schema.params (closures selected).args := by
  exact ((SchematicRows.Opening.models_information_iff (Frames.contextual S)
    (activation ordinary rows closures selected output) rfl rfl point wellFormed).mp model).2.2

theorem activation_retains_schema
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :
    ((activation ordinary rows closures selected output).result (Frames.contextual S)).rules = rows ∧
      (((activation ordinary rows closures selected output).result (Frames.contextual S)).held selected).args =
        (closures selected).args.map
          (instantiateObservation (Contextual.weakenNames S ordinary.frame (closures selected).schema.locals)) := by
  obtain ⟨kept, held⟩ := SchematicRows.Materialization.persistent_source_retained
    (Frames.contextual S) (activation ordinary rows closures selected output) selected rfl rfl rfl rfl
  refine ⟨kept, ?_⟩
  exact congrArg (fun item => item.args) held

theorem activation_present
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :
    ((activation ordinary rows closures selected output).result (Frames.contextual S)).present =
      ordinary.present ∪ {output} :=
  SchematicRows.Materialization.result_present_single (Frames.contextual S)
    (activation ordinary rows closures selected output) output rfl rfl

theorem activation_output
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :
    ((activation ordinary rows closures selected output).result (Frames.contextual S)).label output =
      instantiateObservation
        (Contextual.canonicalOpening S ordinary.frame (closures selected).schema.locals)
        (closures selected).schema.value :=
  SchematicRows.Materialization.result_label_single (Frames.contextual S)
    (activation ordinary rows closures selected output) output (closures selected).schema.value rfl rfl

/-- A canonical activation projects exactly onto the original frame
assignment. Its local declarations witness only the closure's own reading. -/
theorem activation_models_iff
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (caller : Assignment ordinary.frame.arity target.arity) (value : Contextual.Terms S target) :
    let N := (closures selected).schema.locals
    let result := (activation ordinary rows closures selected output).result (Frames.contextual S)
    ((Frames.contextual S).Models caller ordinary.knowledge ∧
      (closures selected).ReadsAt (Frames.contextual S) caller value) ↔
    ∃ point : Assignment (Contextual.extend S ordinary.frame N).arity target.arity,
      Assignment.compose point (Contextual.weakenNames S ordinary.frame N) = caller ∧
      (Frames.contextual S).Models point result.knowledge ∧
      instantiateObservation point (result.label output) = value := by
  dsimp only
  let N := (closures selected).schema.locals
  let f := activation ordinary rows closures selected output
  let X := Frames.contextual S
  have information (point : Assignment (Contextual.extend S ordinary.frame N).arity target.arity) :=
    SchematicRows.Opening.models_information_iff X f rfl rfl point wellFormed
  constructor
  · rintro ⟨old, localImage, known, captured, result⟩
    let point := Contextual.copair S caller localImage
    have ambient : Assignment.compose point (Contextual.weakenNames S ordinary.frame N) = caller := by
      funext name
      exact instantiate_generator point (.inl name)
    have local' : Assignment.compose point (Contextual.canonicalOpening S ordinary.frame N) = localImage := by
      funext name
      exact instantiate_generator point (.inr name)
    refine ⟨point, ambient, (information point).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · change X.Models (Assignment.compose point (Contextual.weakenNames S ordinary.frame N)) ordinary.knowledge
      rwa [ambient]
    · change X.Models (Assignment.compose point (Contextual.canonicalOpening S ordinary.frame N))
        (closures selected).schema.knowledge
      rwa [local']
    · apply captured.imp
      intro parameter argument same
      change instantiateObservation point
        (instantiateObservation (Contextual.canonicalOpening S ordinary.frame N) parameter) =
        instantiateObservation point (instantiateObservation (Contextual.weakenNames S ordinary.frame N) argument)
      rw [Contextual.copair_opening, Contextual.copair_weaken]
      exact same
    · rw [activation_output, Contextual.copair_opening]
      exact result
  · rintro ⟨point, ambient, model, outputModel⟩
    obtain ⟨old, known, captured⟩ := (information point).mp model
    rw [activation_output, instantiateObservation_comp] at outputModel
    refine ⟨?_, Assignment.compose point (Contextual.canonicalOpening S ordinary.frame N), known, ?_, outputModel⟩
    · change X.Models (Assignment.compose point (Contextual.weakenNames S ordinary.frame N)) ordinary.knowledge at old
      rwa [ambient] at old
    · rw [← ambient]
      apply captured.imp
      intro parameter argument same
      change instantiateObservation point
        (instantiateObservation (Contextual.canonicalOpening S ordinary.frame N) parameter) =
        instantiateObservation point (instantiateObservation (Contextual.weakenNames S ordinary.frame N) argument) at same
      exact (instantiateObservation_comp _ _ _).symm.trans (same.trans (instantiateObservation_comp _ _ _))

/-- Admission and the observed output are obtained from the same closure
reading. The witness also preserves the caller on every mentioned source term. -/
theorem activation_realizes_reading
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O)
    (present : selected ∈ rows) (fresh : output ∉ ordinary.present)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (caller : Assignment ordinary.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller ordinary.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures selected).ReadsAt (Frames.contextual S) caller value) :
    (activation ordinary rows closures selected output).Admits (Frames.contextual S) ∅ ∧
      ∃ point : Assignment
          (Contextual.extend S ordinary.frame (closures selected).schema.locals).arity target.arity,
        (Frames.contextual S).Models point
          ((activation ordinary rows closures selected output).result (Frames.contextual S)).knowledge ∧
        (∀ term, (hosted ordinary rows closures).Mentions term →
          instantiateObservation point
            (instantiateObservation (Contextual.weakenNames S ordinary.frame (closures selected).schema.locals) term) =
              instantiateObservation caller term) ∧
        instantiateObservation point
          (((activation ordinary rows closures selected output).result (Frames.contextual S)).label output) = value := by
  refine ⟨activation_admitted_of_reading ordinary rows closures selected output present fresh wellFormed
    caller known value reading, ?_⟩
  obtain ⟨point, projects, models, outputValue⟩ :=
    (activation_models_iff ordinary rows closures selected output wellFormed caller value).mp ⟨known, reading⟩
  refine ⟨point, models, fun term _ => ?_, outputValue⟩
  let old : Observation S ordinary.frame.arity := term
  exact (instantiateObservation_comp _ _ old).trans (congrArg (instantiateObservation · old) projects)

theorem activation_label_other
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output other : O)
    (different : other ≠ output) :
    ((activation ordinary rows closures selected output).result (Frames.contextual S)).label other =
      instantiateObservation
        (Contextual.weakenNames S ordinary.frame (closures selected).schema.locals) (ordinary.label other) := by
  exact (activation ordinary rows closures selected output).base.result_label_other
    (X := Frames.contextual S) (s := ordinary) (by change other ∉ [output]; simpa only [List.mem_singleton] using different)

theorem activation_held_other
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) (other : R) :
    ((activation ordinary rows closures selected output).result (Frames.contextual S)).held other =
      ((hosted ordinary rows closures).held other).act (Frames.contextual S)
        (Contextual.weakenNames S ordinary.frame (closures selected).schema.locals) :=
  (activation ordinary rows closures selected output).result_held_other (X := Frames.contextual S) (by simp [activation, HeldReadGenericFirings.datum])

/-- The consumer rule and datum each receive their own local declarations. -/
abbrev readLocals (S : Signature) (locals : Frame S) : Frame S :=
  Contextual.extend S locals locals

def readRuleOpening (ambient locals : Frame S) :
    Assignment locals.arity (Contextual.extend S ambient (readLocals S locals)).arity :=
  fun name => generator (Contextual.extend S ambient (readLocals S locals)).arity (Sum.inr (Sum.inl name))

def readDatumOpening (ambient locals : Frame S) :
    Assignment locals.arity (Contextual.extend S ambient (readLocals S locals)).arity :=
  fun name => generator (Contextual.extend S ambient (readLocals S locals)).arity (Sum.inr (Sum.inr name))

def readCopair {ambient locals target : Frame S}
    (caller : Assignment ambient.arity target.arity)
    (consumer datum : Assignment locals.arity target.arity) :
    Assignment (Contextual.extend S ambient (readLocals S locals)).arity target.arity
  | .inl name => caller name
  | .inr (.inl name) => consumer name
  | .inr (.inr name) => datum name

omit [DecidableEq O] [DecidableEq R] in
theorem readCopair_weaken {ambient locals target : Frame S}
    (caller : Assignment ambient.arity target.arity)
    (consumer datum : Assignment locals.arity target.arity) (term : Contextual.Terms S ambient) :
    instantiateObservation (readCopair caller consumer datum)
      (instantiateObservation (Contextual.weakenNames S ambient (readLocals S locals)) term) =
      instantiateObservation caller term := by
  rw [instantiateObservation_comp]
  congr 1
  funext name
  exact instantiate_generator (readCopair caller consumer datum) (.inl name)

omit [DecidableEq O] [DecidableEq R] in
theorem readCopair_rule {ambient locals target : Frame S}
    (caller : Assignment ambient.arity target.arity)
    (consumer datum : Assignment locals.arity target.arity) (term : Contextual.Terms S locals) :
    instantiateObservation (readCopair caller consumer datum)
      (instantiateObservation (readRuleOpening ambient locals) term) =
      instantiateObservation consumer term := by
  rw [instantiateObservation_comp]
  congr 1
  funext name
  exact instantiate_generator (readCopair caller consumer datum) (.inr (.inl name))

omit [DecidableEq O] [DecidableEq R] in
theorem readCopair_datum {ambient locals target : Frame S}
    (caller : Assignment ambient.arity target.arity)
    (consumer datum : Assignment locals.arity target.arity) (term : Contextual.Terms S locals) :
    instantiateObservation (readCopair caller consumer datum)
      (instantiateObservation (readDatumOpening ambient locals) term) =
      instantiateObservation datum term := by
  rw [instantiateObservation_comp]
  congr 1
  funext name
  exact instantiate_generator (readCopair caller consumer datum) (.inr (.inr name))

/-- The actual direct schematic read, with independently fresh rule and datum
openings. The rule pattern retains the datum's full binding structure. -/
def directRead (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O) :=
  HeldReadGenericFirings.direct (E := Contextual.declarations S) ordinary rows closures selected
    (readLocals S (closures selected).schema.locals)
    (readRuleOpening ordinary.frame (closures selected).schema.locals)
    (readDatumOpening ordinary.frame (closures selected).schema.locals) output

theorem directRead_fresh (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output temporary : O) :
    (directRead ordinary rows closures selected output).Fresh (Frames.contextual S) := by
  apply (HeldReadGenericFirings.direct_fresh_iff_joint (E := Contextual.declarations S)
    (Frames.contextual S) ordinary rows closures selected
    (readLocals S (closures selected).schema.locals)
    (readRuleOpening ordinary.frame (closures selected).schema.locals)
    (readDatumOpening ordinary.frame (closures selected).schema.locals) temporary output).mpr
  intro target caller consumer datum
  refine ⟨readCopair caller consumer datum, ⟨?_, ?_⟩, ?_⟩
  · intro term _
    exact readCopair_weaken caller consumer datum term
  · intro term _
    exact readCopair_rule caller consumer datum term
  · intro term _
    exact readCopair_datum caller consumer datum term

/-- A compatible closure witness constructs the direct read's actual model.
Both local copies are independent in freshness; matching relates their values
in the information, rather than conflating their declarations. -/
theorem directRead_admitted_of_reading
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (output : O)
    (present : selected ∈ rows) (fresh : output ∉ ordinary.present)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (caller : Assignment ordinary.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller ordinary.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures selected).ReadsAt (Frames.contextual S) caller value) :
    (directRead ordinary rows closures selected output).Admits (Frames.contextual S) := by
  obtain ⟨datum, localModel, captures, _⟩ := reading
  let point := readCopair caller datum datum
  have baseModel : (Frames.contextual S).Models point
      (HeldReadGenericFirings.datumInformation (E := Contextual.declarations S) ordinary closures selected
        (readLocals S (closures selected).schema.locals)
        (readDatumOpening ordinary.frame (closures selected).schema.locals) (Frames.contextual S)) := by
    dsimp only [HeldReadGenericFirings.datumInformation, Contextual.declarations]
    rw [Frames.models_append (X := Frames.contextual S), Frames.models_append (X := Frames.contextual S)]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro equation member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      change instantiateObservation point
          (instantiateObservation (Contextual.weakenNames S ordinary.frame (readLocals S (closures selected).schema.locals)) original.1) =
        instantiateObservation point
          (instantiateObservation (Contextual.weakenNames S ordinary.frame (readLocals S (closures selected).schema.locals)) original.2)
      rw [readCopair_weaken, readCopair_weaken]
      exact known original inside
    · intro equation member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      change instantiateObservation point
          (instantiateObservation (readDatumOpening ordinary.frame (closures selected).schema.locals) original.1) =
        instantiateObservation point
          (instantiateObservation (readDatumOpening ordinary.frame (closures selected).schema.locals) original.2)
      rw [readCopair_datum, readCopair_datum]
      exact localModel original inside
    · have matched : List.Forall₂ (fun left right =>
          instantiateObservation point left = instantiateObservation point right)
          ((closures selected).schema.params.map
            (instantiateObservation (readDatumOpening ordinary.frame (closures selected).schema.locals)))
          ((closures selected).args.map
            (instantiateObservation (Contextual.weakenNames S ordinary.frame (readLocals S (closures selected).schema.locals)))) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        apply captures.imp
        intro parameter argument equal
        change instantiateObservation datum parameter = instantiateObservation caller argument at equal
        exact (readCopair_datum caller datum datum parameter).trans
          (equal.trans (readCopair_weaken caller datum datum argument).symm)
      intro equation member
      exact List.forall₂_zip matched member
  have solved : (Frames.contextual S).Solvable
      ((directRead ordinary rows closures selected output).information (Frames.contextual S)) := by
    refine ⟨target, point, ?_⟩
    dsimp only [directRead]
    rw [HeldReadGenericFirings.direct_information (E := Contextual.declarations S)
      ordinary rows closures selected (readLocals S (closures selected).schema.locals)
      (readRuleOpening ordinary.frame (closures selected).schema.locals)
      (readDatumOpening ordinary.frame (closures selected).schema.locals) (Frames.contextual S) output]
    dsimp only [HeldReadGenericFirings.direct, HeldReadGenericFirings.datumInformation, Contextual.declarations, HeldReadGenericSources.mixed]
    intro equation member
    rcases List.mem_append.mp member with base | matching
    · exact baseModel equation base
    obtain rfl := List.mem_singleton.mp matching
    change instantiateObservation point
        (instantiateObservation (readRuleOpening ordinary.frame (closures selected).schema.locals) (closures selected).schema.value) =
      instantiateObservation point
        (instantiateObservation (readDatumOpening ordinary.frame (closures selected).schema.locals) (closures selected).schema.value)
    rw [readCopair_rule, readCopair_datum]
  refine ⟨HeldReadGenericFirings.direct_shapes (E := Contextual.declarations S) (Frames.contextual S) ordinary rows closures selected
      (readLocals S (closures selected).schema.locals)
      (readRuleOpening ordinary.frame (closures selected).schema.locals)
      (readDatumOpening ordinary.frame (closures selected).schema.locals) output
      (directRead_fresh ordinary rows closures selected output output) wellFormed,
    HeldReadGenericFirings.direct_enabled (E := Contextual.declarations S) ordinary rows closures selected
      (readLocals S (closures selected).schema.locals)
      (readRuleOpening ordinary.frame (closures selected).schema.locals)
      (readDatumOpening ordinary.frame (closures selected).schema.locals) output present fresh,
    solved, ?_⟩
  intro later assignment _
  exact HeldReadGenericFirings.direct_holds (E := Contextual.declarations S) (Frames.contextual S) ordinary rows closures selected
    (readLocals S (closures selected).schema.locals)
    (readRuleOpening ordinary.frame (closures selected).schema.locals)
    (readDatumOpening ordinary.frame (closures selected).schema.locals) output assignment

/-- The contextual direct read executes as the existing two-step held protocol.
Its decoded complete live view agrees, including retained closure captures. -/
theorem read_expansion_of_reading
    (ordinary : RuleSyntax.State (Contextual.Terms S) O) (rows : Finset R)
    (closures : R → Closure (Contextual.Terms S) ordinary.frame) (selected : R) (temporary output : O)
    (present : selected ∈ rows) (outputFresh : output ∉ ordinary.present)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (wellFormed : (closures selected).WellFormed) {target : Frame S}
    (caller : Assignment ordinary.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller ordinary.knowledge)
    (value : Contextual.Terms S target)
    (reading : (closures selected).ReadsAt (Frames.contextual S) caller value) :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := Contextual.declarations S)
        (O := O) (R := R) (Frames.contextual S)
        {Sum.inr (HeldReadGenericFirings.consumeRule (closures selected).schema)}).Run
          (hosted ordinary rows closures),
      run.word.length = 2 ∧ run.last.present = ordinary.present ∪ {output} ∧
        run.last.rules = rows ∧ temporary ∉ run.last.present ∧
        run.last = (HeldReadGenericFirings.consumer (E := Contextual.declarations S)
          ordinary rows closures selected (readLocals S (closures selected).schema.locals)
          (readRuleOpening ordinary.frame (closures selected).schema.locals)
          (readDatumOpening ordinary.frame (closures selected).schema.locals)
          (Frames.contextual S) temporary output).result (Frames.contextual S) ∧
        LiveObservations.observe (HeldReadGenericFirings.publicResult (E := Contextual.declarations S)
          (Frames.contextual S) ordinary rows closures selected
          (readLocals S (closures selected).schema.locals)
          (readRuleOpening ordinary.frame (closures selected).schema.locals)
          (readDatumOpening ordinary.frame (closures selected).schema.locals) temporary output) =
        LiveObservations.observe ((directRead ordinary rows closures selected output).result (Frames.contextual S)) := by
  obtain ⟨run, length, endpoint, presence, rules, absent⟩ :=
    HeldReadGenericFirings.execution_of_direct (E := Contextual.declarations S) (Frames.contextual S)
      ordinary rows closures selected (readLocals S (closures selected).schema.locals)
      (readRuleOpening ordinary.frame (closures selected).schema.locals)
      (readDatumOpening ordinary.frame (closures selected).schema.locals) temporary output
      {Sum.inr (HeldReadGenericFirings.consumeRule (closures selected).schema)} (Set.mem_singleton _)
      temporaryFresh different
      (directRead_admitted_of_reading ordinary rows closures selected output present outputFresh
        wellFormed caller known value reading)
  exact ⟨run, length, presence, rules, absent, endpoint,
    HeldReadGenericFirings.public_view_eq (E := Contextual.declarations S)
      (Frames.contextual S) ordinary rows closures selected
      (readLocals S (closures selected).schema.locals)
      (readRuleOpening ordinary.frame (closures selected).schema.locals)
      (readDatumOpening ordinary.frame (closures selected).schema.locals) temporary output temporaryFresh⟩

namespace Example

inductive Operator where
  | atom (value : Nat)
  | pair
  | lam
  deriving DecidableEq

def signature : Signature where
  Srt := Unit
  Op _ := Operator
  arity
    | .atom _ => []
    | .pair => [([], ()), ([], ())]
    | .lam => [([()], ())]

abbrev nullary (Names : Type) : Names → MetaArity signature := fun _ => ([], ())
abbrev ambient : Frame signature := ⟨Unit, nullary Unit⟩
abbrev locals : Frame signature := ⟨Bool, nullary Bool⟩
abbrev target : Frame signature := ⟨Empty, nullary Empty⟩

def atom {Names : Type} {context : Ctx signature} (n : Nat) :
    Term (ContextualFamily.signature signature (nullary Names)) context () :=
  .op (.inl (.atom n)) .nil

/-- Two actual object binders surround two independent contextual unknowns.
The bound occurrence is the outer lambda's variable, not a metavariable. -/
def body : Term (ContextualFamily.signature signature locals.arity) [] () :=
  .op (.inl .lam) (.cons
    (.op (.inl .lam) (.cons
      (.op (.inl .pair) (.cons (.var (.succ .zero))
        (.cons (.op (.inl .pair) (.cons (.op (.inr ⟨false⟩) .nil)
          (.cons (.op (.inr ⟨true⟩) .nil) .nil))) .nil))) .nil)) .nil)

def closedBody (captured localValue : Nat) :
    Term (ContextualFamily.signature signature target.arity) [] () :=
  .op (.inl .lam) (.cons
    (.op (.inl .lam) (.cons
      (.op (.inl .pair) (.cons (.var (.succ .zero))
        (.cons (.op (.inl .pair) (.cons (atom captured) (.cons (atom localValue) .nil))) .nil))) .nil)) .nil)

def schema : Schema (Contextual.Terms signature) :=
  ⟨locals, [], [observe (generator locals.arity false)], observe body⟩

def initial : RuleSyntax.State (Contextual.Terms signature) Nat :=
  ⟨ambient, [], {2}, fun _ => observe (generator ambient.arity ())⟩

def stored (_ : Bool) : Closure (Contextual.Terms signature) initial.frame :=
  ⟨schema, [initial.label 2]⟩

def caller : Assignment ambient.arity target.arity := fun _ => atom 7
def localPoint (n : Nat) : Assignment locals.arity target.arity
  | false => atom 7
  | true => atom n

theorem reading (n : Nat) :
    (stored false).ReadsAt (Frames.contextual signature) caller (observe (closedBody 7 n)) := by
  refine ⟨localPoint n, ?_, ?_, ?_⟩
  · intro equation absent
    cases absent
  · exact .cons rfl .nil
  · rfl

theorem initial_known : (Frames.contextual signature).Models caller initial.knowledge := by
  intro equation absent
  cases absent

def first := activation initial ({false, true} : Finset Bool) stored false 0
def firstResult := first.result (Frames.contextual signature)

theorem first_admitted : first.Admits (Frames.contextual signature) ∅ :=
  activation_admitted_of_reading initial {false, true} stored false 0 (by decide) (by decide) rfl
    caller initial_known (observe (closedBody 7 0)) (reading 0)

def laterStored (r : Bool) : Closure (Contextual.Terms signature) firstResult.frame :=
  ⟨schema, (firstResult.held r).args⟩

def second := activation firstResult.toState firstResult.rules laterStored false 1
def secondResult := second.result (Frames.contextual signature)

def secondCaller : Assignment firstResult.frame.arity target.arity :=
  Contextual.copair signature caller (localPoint 0)

theorem second_known : (Frames.contextual signature).Models secondCaller firstResult.knowledge := by
  intro equation member
  change equation ∈ [(observe (generator (Contextual.extend signature ambient locals).arity (.inr false)),
    observe (generator (Contextual.extend signature ambient locals).arity (.inl ())))] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem later_reading (n : Nat) :
    (laterStored false).ReadsAt (Frames.contextual signature) secondCaller (observe (closedBody 7 n)) := by
  refine ⟨localPoint n, ?_, ?_, ?_⟩
  · intro equation absent
    cases absent
  · exact .cons rfl .nil
  · rfl

theorem second_admitted : second.Admits (Frames.contextual signature) ∅ :=
  activation_admitted_of_reading firstResult.toState firstResult.rules laterStored false 1
    (by decide) (by decide) rfl secondCaller second_known (observe (closedBody 7 1)) (later_reading 1)

theorem rebuilt_source_is_actual :
    hosted firstResult.toState firstResult.rules laterStored = firstResult := by
  rfl

/-- The same stored binder-bearing schema executes twice. Its local
declarations are newly allocated at both steps, and its capture remains old. -/
def repeatedExecution :
    (rstep (Frames.contextual signature) Nat Bool (Contextual.declarations signature)
      HeldReadEncoding.codes ∅).toStep.Run (hosted initial {false, true} stored) :=
  .cons first first_admitted (.cons second second_admitted (.nil _))

theorem repeated_execution_length : repeatedExecution.word.length = 2 := rfl

theorem both_outputs_present : 0 ∈ secondResult.present ∧ 1 ∈ secondResult.present := by decide

theorem second_capture_is_original :
    (secondResult.held false).args =
      [observe (generator
        (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
        (.inl (.inl ())))] := rfl

def finalPoint : Assignment secondResult.frame.arity target.arity :=
  Contextual.copair signature secondCaller (localPoint 1)

theorem finalPoint_models : (Frames.contextual signature).Models finalPoint secondResult.knowledge := by
  intro equation member
  change equation ∈ [
    (observe (generator (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
      (.inl (.inr false))),
      observe (generator (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
        (.inl (.inl ())))),
    (observe (generator (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
      (.inr false)),
      observe (generator (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
        (.inl (.inl ()))))] at member
  rcases List.mem_cons.mp member with first | last
  · obtain rfl := first
    rfl
  · obtain rfl := List.mem_singleton.mp last
    rfl

/-- One model of the actual joint result distinguishes both local instances
while keeping their common capture equal to seven. -/
theorem actual_outputs_at_common_model :
    instantiateObservation finalPoint (secondResult.label 0) = observe (closedBody 7 0) ∧
      instantiateObservation finalPoint (secondResult.label 1) = observe (closedBody 7 1) :=
  ⟨rfl, rfl⟩

theorem actual_local_values_differ :
    finalPoint (.inl (.inr true)) ≠ finalPoint (.inr true) := by
  intro same
  change atom (Names := Empty) 0 = atom (Names := Empty) 1 at same
  have heads := (Term.op.inj same).1
  have impossible : (0 : Nat) = 1 := Operator.atom.inj (Sum.inl.inj heads)
  omega

/-- A source capture cannot be silently generalized at the second use. -/
theorem captured_value_cannot_change :
    ¬ ∃ point : Assignment secondResult.frame.arity target.arity,
      (Frames.contextual signature).Models point secondResult.knowledge ∧
        point (.inl (.inl ())) = atom 7 ∧ point (.inr false) = atom 8 := by
  rintro ⟨point, model, oldValue, newValue⟩
  have member :
      (observe (generator secondResult.frame.arity (.inr false)),
        observe (generator secondResult.frame.arity (.inl (.inl ())))) ∈ secondResult.knowledge := by
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have equal := model _ member
  change observe (instantiate point (generator secondResult.frame.arity (.inr false))) =
    observe (instantiate point (generator secondResult.frame.arity (.inl (.inl ())))) at equal
  have newEval := instantiate_generator (S := signature) point (.inr false)
  have oldEval := instantiate_generator (S := signature) point (.inl (.inl ()))
  have values := (congrArg observe newEval).symm.trans (equal.trans (congrArg observe oldEval))
  rw [newValue, oldValue] at values
  have heads := (Term.op.inj (observe_injective values)).1
  have impossible : (8 : Nat) = 7 := Operator.atom.inj (Sum.inl.inj heads)
  omega

theorem independently_opened_locals :
    (observe (generator
      (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
      (.inl (.inr true)))) ≠
    observe (generator
      (Contextual.extend signature (Contextual.extend signature ambient locals) locals).arity
      (.inr true)) := by
  intro same
  have termSame := observe_injective same
  have headSame := (Term.op.inj termSame).1
  cases headSame

theorem direct_read_executes :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := Contextual.declarations signature)
      (O := Nat) (R := Bool) (Frames.contextual signature)
      {Sum.inr (HeldReadGenericFirings.consumeRule schema)}).Run (hosted initial {false, true} stored),
      run.word.length = 2 ∧ run.last.present = initial.present ∪ {0} ∧
        run.last.rules = ({false, true} : Finset Bool) ∧ 3 ∉ run.last.present := by
  obtain ⟨run, length, present, rules, absent, _, _⟩ :=
    read_expansion_of_reading initial {false, true} stored false 3 0
      (by decide) (by decide) (by decide) (by decide) rfl
      caller initial_known (observe (closedBody 7 0)) (reading 0)
  exact ⟨run, length, present, rules, absent⟩

end Example

#print axioms activation_fresh
#print axioms activation_admitted_of_reading
#print axioms activation_captures
#print axioms activation_retains_schema
#print axioms activation_models_iff
#print axioms activation_realizes_reading
#print axioms directRead_fresh
#print axioms directRead_admitted_of_reading
#print axioms read_expansion_of_reading
#print axioms Example.repeatedExecution
#print axioms Example.direct_read_executes
#print axioms Example.independently_opened_locals
#print axioms Example.finalPoint_models
#print axioms Example.actual_outputs_at_common_model
#print axioms Example.captured_value_cannot_change

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Rows
