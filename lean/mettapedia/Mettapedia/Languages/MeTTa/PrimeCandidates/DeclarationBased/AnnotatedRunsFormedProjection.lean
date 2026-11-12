import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedCompiler
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveCompletedConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionSubstitution

/-!
# First consumer: the formed Sigma/wire projection, compiled and executed

The source is the Flower's mixed payload: a native List of abstract HOL sequences paired with
actual wire data, `pair holSequenceSingleton (encode wire)`, and its second projection. It is
admitted at the wire Data type in the shared HOL/List/J/relator/wire rules.

## The theory's values and substitution

* **Value discipline** (`holDiscipline`): the canonical constants are the wire data constructors
  and tagged literals, the native List constructors and type former, and the HOL sequence
  constants. Every root rule of the theory (List and identity elimination, List-relator
  elimination) is headed by an eliminator outside the table.
* **Root action** (`holRootAction`): the existing substitution of the native List, identity and
  relator root codes, with its decoder square and functor laws.

## The compiled program

* **The compiled Sigma beta rule** (`projectionRule`): take `evaluate (second (pair X Y)) R`, tell
  `R = Y`. Its certificate is the Flower's Sigma beta step, checked on the schema
  (`projectionRule_sound`).
* **The compilation of the source** (`compile_source`, for every wire): the compiler reads the
  projection of a pair of values.
* **The compiled run** (`projection_executes`, `projection_observes`): one firing, a compiled step
  (`projectionFiringAt_compiled`).

## The source side, for every wire

* **Source judgment** (`projectionSource`), and **source execution** (`projectionEvidence`): one
  Sigma beta step, accepted by the unchanged native checker, to `encode wire`; the target's own
  judgment is the Flower's checked preservation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
namespace Projection

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation (Tm)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (RootDecoder Certificate Code StepCode)
open AnnotatedRuns

/-- The shared HOL/List/J/relator/wire rules. -/
abbrev rules : Presentation.Rules Presentation.Tower.Head := HOLNativeRelatorCompatibility.rules

instance projectionHeadEq : DecidableRel rules.headEq :=
  fun h u => Presentation.LevelTower.instDecidableHeadEq h u

/-- The native relator's root decoder serves the opaque extension: its roots are exactly the
native roots (`OpaqueRelatorExtension.root_iff`). -/
def holDecoder : RootDecoder rules.computation where
  Code := NativeRelatorRootConversionCode.Code
  decode := NativeRelatorRootConversionCode.decode
  sound := by
    intro n code left right accepted
    exact (OpaqueRelatorExtension.root_iff HOLNativeRelatorCompatibility.opacity).mpr
      (NativeRelatorRootConversionCode.rootDecoder.sound code accepted)
  complete := fun step => NativeRelatorRootConversionCode.rootDecoder.complete
    ((OpaqueRelatorExtension.root_iff HOLNativeRelatorCompatibility.opacity).mp step)

/-- **The actual root action of the native decoder**: every List, identity and relator root field
is substituted as a scoped term. -/
def holRootAction : RootAction holDecoder where
  substitute := NativeRelatorRootConversionCode.substitute
  natural := NativeRelatorRootConversionCode.decode_substitute
  substitute_ids := NativeRelatorRootConversionCode.substitute_ids
  substitute_comp := NativeRelatorRootConversionCode.substitute_comp

/-! ## Values of the shared theory -/

/-- The untagged constructors of the shared theory. -/
def holConstructors : List Presentation.DeclName :=
  [NativeWireData.dataName, NativeWireData.applicationName, NativeWireData.consName,
    NativeWireData.nilName, NativeIndexedFamilies.Intrinsic.listName, NativeIndexedFamilies.Intrinsic.nilName,
    NativeIndexedFamilies.Intrinsic.consName, `HOLUniformList.sequence, `HOLUniformList.nil]

/-- **The canonical constants**: tagged wire literals, wire and List constructors, the List type
former and the HOL sequence constants. -/
def holCanonical : Presentation.DeclName → Bool
  | .str tag name =>
      decide (tag = NativeWireData.symbolPrefix) || decide (tag = NativeWireData.stringPrefix) ||
        holConstructors.any fun constructor => decide (Lean.Name.str tag name = constructor)
  | .num tag _ => decide (tag = NativeWireData.naturalPrefix)
  | .anonymous => false

/-- **The value discipline of the shared theory**: every root rule is headed by an eliminator,
which is not canonical. -/
def holDiscipline : ValueDiscipline rules where
  canonical := holCanonical
  root_head := by
    intro n left right step
    have inherited := (OpaqueRelatorExtension.root_iff HOLNativeRelatorCompatibility.opacity).mp step
    cases inherited with
    | inherited impossible => exact impossible.elim
    | delta lookup =>
        rw [NativeIndexedFamilies.IntrinsicRelator.rawSignature_valueOf_none] at lookup
        cases lookup
    | declared evidence =>
        obtain ⟨evidence⟩ := evidence
        cases evidence with
        | list evidence => cases evidence <;> exact ⟨_, rfl, by decide +kernel⟩
        | rel evidence => cases evidence <;> exact ⟨_, rfl, by decide +kernel⟩

/-! ## The source and its execution -/

/-- The wire Data type, formed at the lowest universe. -/
def dataTypeOver : TypeOver (empty rules) where
  code := NativeWireData.dataType
  level := .sort Presentation.Tower.zero
  universeWitness := .sort _
  formed := HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)

/-- **The source program**: the second projection of the mixed payload, typed by the Sigma
elimination of its formed payload. -/
def projectionTerm (wire : NativeWireData.Wire) : Term (empty rules) dataTypeOver :=
  ⟨.snd (HOLNativeRelatorCompatibility.mixedPayload wire),
    .sndElim (HOLNativeRelatorCompatibility.mixed_payload_typed .nil wire)⟩

def projectionSource (wire : NativeWireData.Wire) : TotalTerm (empty rules) :=
  ⟨dataTypeOver, projectionTerm wire⟩

/-- **The source value** with its own judgment, from the Flower's checked preservation. -/
def valueTerm (wire : NativeWireData.Wire) : Term (empty rules) dataTypeOver :=
  ⟨NativeWireData.encode wire, (HOLNativeRelatorCompatibility.mixed_projection_admitted wire).typing⟩

/-- The checked Sigma beta step from the source to its value. -/
def betaCertificate (wire : NativeWireData.Wire) :
    Certificate rules.headEq holDecoder.decode (projectionSource wire).2.code
      (NativeWireData.encode wire) :=
  ⟨.single (.betaSigmaSnd HOLNativeRelatorCompatibility.holSequenceSingleton
      (NativeWireData.encode wire)),
    HOLNativeRelatorCompatibility.mixed_projection_checked (n := 0) wire⟩

/-- **The source execution as formed evidence**, for every wire. -/
def projectionEvidence (wire : NativeWireData.Wire) :
    FormedEvidence holDecoder (empty rules) (projectionSource wire) (NativeWireData.encode wire) where
  targetType := dataTypeOver
  targetTerm := valueTerm wire
  target_code := rfl
  typeCertificate := Certificate.refl _
  termCertificate := betaCertificate wire

/-- **A second piece of evidence for the same endpoints**, with a detour: the step, back, and
the step again. Both are accepted by the same checker. -/
def projectionDetour (wire : NativeWireData.Wire) :
    FormedEvidence holDecoder (empty rules) (projectionSource wire) (NativeWireData.encode wire) where
  targetType := dataTypeOver
  targetTerm := valueTerm wire
  target_code := rfl
  typeCertificate := Certificate.refl _
  termCertificate := (betaCertificate wire).trans ((betaCertificate wire).symm.trans (betaCertificate wire))

theorem projectionEvidence_stepCount (wire : NativeWireData.Wire) :
    (projectionEvidence wire).stepCount = 1 := rfl

theorem projectionDetour_stepCount (wire : NativeWireData.Wire) :
    (projectionDetour wire).stepCount = 3 := rfl

/-- The Flower-side consequences: the source retyped at the value's formed type, the value's own
judgment, and one `QTerm` class. -/
theorem projection_source_side (wire : NativeWireData.Wire) :
    Presentation.FormationSensitive.Judgment rules .nil
        (.snd (HOLNativeRelatorCompatibility.mixedPayload wire)) NativeWireData.dataType ∧
      Presentation.FormationSensitive.Judgment rules .nil (NativeWireData.encode wire)
        NativeWireData.dataType ∧
      QTerm.mk (projectionTerm wire) = QTerm.mk (valueTerm wire) :=
  ⟨(projectionEvidence wire).retyped, (projectionEvidence wire).targetJudgment,
    (projectionEvidence wire).class_eq⟩

/-! ## Quotation of the payload -/

theorem holCanonical_symbol (name : String) :
    holCanonical (.str NativeWireData.symbolPrefix name) = true := by
  simp [holCanonical]

theorem holCanonical_string (value : String) :
    holCanonical (.str NativeWireData.stringPrefix value) = true := by
  simp [holCanonical]

theorem holCanonical_natural (value : Nat) :
    holCanonical (.num NativeWireData.naturalPrefix value) = true := by
  simp [holCanonical]

mutual

/-- Every wire encoding is a value, and is quoted. -/
theorem encode_quotes {n : Nat} : ∀ wire : NativeWireData.Wire,
    IsValue holCanonical (NativeWireData.encode (n := n) wire) ∧
      ∃ p, quoteValue holCanonical (NativeWireData.encode (n := n) wire) = some p
  | .symbol name => by
      simp only [NativeWireData.encode]
      exact ⟨holCanonical_symbol name, .const (.str NativeWireData.symbolPrefix name),
        by simp [quoteValue, holCanonical_symbol name]⟩
  | .string value => by
      simp only [NativeWireData.encode]
      exact ⟨holCanonical_string value, .const (.str NativeWireData.stringPrefix value),
        by simp [quoteValue, holCanonical_string value]⟩
  | .natural value => by
      simp only [NativeWireData.encode]
      exact ⟨holCanonical_natural value, .const (.num NativeWireData.naturalPrefix value),
        by simp [quoteValue, holCanonical_natural value]⟩
  | .application head arguments => by
      obtain ⟨value, p, quoted⟩ := encodeList_quotes (n := n) arguments
      have applicationCanonical : holCanonical NativeWireData.applicationName = true := by decide
      simp only [NativeWireData.encode]
      refine ⟨⟨⟨applicationCanonical, holCanonical_symbol head⟩, value⟩,
        ap (ap (.const NativeWireData.applicationName)
          (.const (.str NativeWireData.symbolPrefix head))) p, ?_⟩
      simp [quoteValue, quoted, applicationCanonical, holCanonical_symbol head]
termination_by wire => sizeOf wire

theorem encodeList_quotes {n : Nat} : ∀ wires : List NativeWireData.Wire,
    IsValue holCanonical (NativeWireData.encodeList (n := n) wires) ∧
      ∃ p, quoteValue holCanonical (NativeWireData.encodeList (n := n) wires) = some p
  | [] => by
      have nilCanonical : holCanonical NativeWireData.nilName = true := by decide
      simp only [NativeWireData.encodeList]
      exact ⟨nilCanonical, .const NativeWireData.nilName, by simp [quoteValue, nilCanonical]⟩
  | wire :: wires => by
      obtain ⟨firstValue, first, firstQuoted⟩ := encode_quotes (n := n) wire
      obtain ⟨restValue, rest, restQuoted⟩ := encodeList_quotes (n := n) wires
      have consCanonical : holCanonical NativeWireData.consName = true := by decide
      simp only [NativeWireData.encodeList]
      refine ⟨⟨⟨consCanonical, firstValue⟩, restValue⟩,
        ap (ap (.const NativeWireData.consName) first) rest, ?_⟩
      simp [quoteValue, firstQuoted, restQuoted, consCanonical]
termination_by wires => sizeOf wires

end

/-- The quoted wire data. -/
def payloadPattern (wire : NativeWireData.Wire) : Pattern :=
  (quoteValue holCanonical (NativeWireData.encode (n := 0) wire)).getD (.const .anonymous)

theorem quote_payload (wire : NativeWireData.Wire) :
    quoteValue holCanonical (NativeWireData.encode (n := 0) wire) = some (payloadPattern wire) := by
  obtain ⟨_, p, quoted⟩ := encode_quotes (n := 0) wire
  simp [payloadPattern, quoted]

/-- The quoted HOL sequence singleton. -/
def holPattern : Pattern :=
  (quoteValue holCanonical (HOLNativeRelatorCompatibility.holSequenceSingleton (n := 0))).getD
    (.const .anonymous)

theorem quote_hol :
    quoteValue holCanonical (HOLNativeRelatorCompatibility.holSequenceSingleton (n := 0)) =
      some holPattern := by
  decide +kernel

/-! ## The compiled program -/

/-- **The compiled Sigma beta rule**: take `evaluate (second (pair X Y)) R`, tell `R = Y`. Its
certificate is the Flower's Sigma beta step on the schema variables `X Y`. -/
def projectionRule : CompiledRule Presentation.Tower.Head holDecoder.Code where
  arity := 2
  left := secondP (pairP (.var 0) (.var 1))
  result := 2
  value := .var 1
  produce := []
  certificate := .single (.betaSigmaSnd (.var 0) (.var 1))

/-- **Per-rule soundness of the projection rule against the Flower's Sigma beta step.** -/
theorem projectionRule_sound :
    projectionRule.Sound rules.headEq holDecoder.decode (fun _ _ => none) := by
  unfold CompiledRule.Sound
  decide +kernel

/-- **The compiled projection program.** -/
def projectionProgram : CompiledProgram rules holDecoder where
  operations := fun _ _ => none
  callables := []
  rules := [projectionRule]
  callables_denoted := fun _ member => (List.not_mem_nil member).elim
  rules_sound := by
    intro rule member
    rw [List.mem_singleton] at member
    subst member
    exact projectionRule_sound

/-- **The compiled program of the source**: the projection of the quoted pair. -/
def program (wire : NativeWireData.Wire) : Pattern := secondP (pairP holPattern (payloadPattern wire))

/-- **The compiler reads the source**, for every wire. -/
theorem compile_source (wire : NativeWireData.Wire) :
    compile holCanonical projectionProgram.callables (projectionSource wire).2.code =
      some (program wire) := by
  change compile (n := 0) holCanonical [] (.snd (.pair (HOLNativeRelatorCompatibility.holSequenceSingleton (n := 0))
    (NativeWireData.encode (n := 0) wire))) = _
  simp only [compile, List.findSome?_nil, quote_hol, quote_payload, Option.bind_some,
    Option.map_some, program]

/-- The schema variables of the rule, renamed to `x y r`. -/
def projectionRename (x y r : Nat) : Nat → Nat := fun v => if v = 0 then x else if v = 1 then y else r

/-- **A compiled step of the projection rule** on occurrence `o`. -/
def projectionStep (x y r o : Nat) : CompiledStep projectionProgram :=
  ⟨projectionRule, List.mem_singleton_self _, projectionRename x y r, o, []⟩

/-- The rule instance with variables `x y r`. -/
def projectionInstance (x y r : Nat) : RuleInstance Pattern where
  take := [evaluate (secondP (pairP (.var x) (.var y))) (.var r)]
  read := []
  tell := [(.var r, .var y)]
  checks := []
  produce := []

/-- One firing of the compiled rule, on occurrence `o`. -/
def projectionFiringAt (x y r o : Nat) : Firing Pattern (Subst signature) Nat :=
  ⟨projectionInstance x y r, [], ⟨[o], [], []⟩⟩

/-- **The firing is the compiled step's firing.** -/
theorem projectionFiringAt_compiled (x y r o : Nat) :
    (projectionStep x y r o).firing = projectionFiringAt x y r o := by
  simp [CompiledStep.firing, projectionStep, projectionFiringAt, CompiledRule.instantiate,
    projectionRule, projectionInstance, projectionRename, varRenaming, Subst.applyTerm]

/-- The compiled start: one pending computation, occurrence `o`. -/
abbrev startAt (o : Nat) : Configuration Pattern Nat := compiledStart o

abbrev projectionFiring : Firing Pattern (Subst signature) Nat := projectionFiringAt 1 2 3 0
abbrev start : Configuration Pattern Nat := startAt 0

/-- The label of the stand-alone program: evaluated into the caller's result variable `0`. -/
def programLabel (p : Pattern) : Nat → Pattern := fun _ => evaluate p (.var 0)

theorem projection_store (label : Nat → Pattern) (x y r o : Nat) :
    (follow label (startAt o) [projectionFiringAt x y r o]).equations =
      [(evaluate (secondP (pairP (.var x) (.var y))) (.var r), label o), (.var r, .var y)] := rfl

/-! ## The transform execution -/

/-- A solution of the compiled store: `X ↦ a`, every other variable to `b`. -/
def projectionSolution (x : Nat) (a b : Pattern) : Subst signature :=
  fun v => if v = x then a else b

/-- The compiled firing scans its present occurrence and makes none. -/
theorem projection_enabled (label : Nat → Pattern) (x y r o : Nat) :
    MeTTaCalculus.OccurrenceCommits.Enabled label (startAt o).present
      ((projectionFiringAt x y r o).selection.commit (T := Pattern)) :=
  ⟨by simp [startAt, compiledStart, projectionFiringAt, Selection.commit],
    by simp [projectionFiringAt, Selection.commit],
    by simp [projectionFiringAt, Selection.commit],
    by simp [projectionFiringAt, Selection.commit],
    fun _ member => (List.not_mem_nil member).elim⟩

/-- **The compiled run is a run of the candidate step**, for every closed pair, under every label
that gives its occurrence the program. -/
theorem projection_executes (label : Nat → Pattern) {x y r o res : Nat} (a b : Pattern)
    (xy : x ≠ y) (xr : x ≠ r) (xres : x ≠ res)
    (labelled : label o = evaluate (secondP (pairP a b)) (.var res))
    (closedA : ∀ σ : Subst signature, σ.applyTerm a = a)
    (closedB : ∀ σ : Subst signature, σ.applyTerm b = b) :
    Executable action label (startAt o) [projectionFiringAt x y r o] := by
  have solved : action.Models (projectionSolution x a b)
      (follow label (startAt o) [projectionFiringAt x y r o]).equations := by
    rw [projection_store]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change (projectionSolution x a b).applyTerm _ = (projectionSolution x a b).applyTerm (label o)
      rw [labelled, applyTerm_evaluate, applyTerm_evaluate, applyTerm_secondP, applyTerm_secondP,
        applyTerm_pairP, applyTerm_pairP, closedA, closedB]
      simp [projectionSolution, Ne.symm xy, Ne.symm xr, Ne.symm xres]
    · change (projectionSolution x a b).applyTerm (.var r) =
        (projectionSolution x a b).applyTerm (.var y)
      simp [projectionSolution, Ne.symm xy, Ne.symm xr]
  exact ⟨⟨⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, projection_enabled label x y r o,
    ⟨projectionSolution x a b, solved⟩, by simp [projectionFiringAt, projectionInstance]⟩,
    by simp [projectionFiringAt]⟩, ⟨projectionSolution x a b, solved⟩⟩

/-- **The result**: every solution of the final store gives the result variable the payload. -/
theorem projection_observes (label : Nat → Pattern) {x y r o res : Nat} (a b : Pattern)
    (labelled : label o = evaluate (secondP (pairP a b)) (.var res))
    (closedA : ∀ σ : Subst signature, σ.applyTerm a = a)
    (closedB : ∀ σ : Subst signature, σ.applyTerm b = b) :
    Observes action (follow label (startAt o) [projectionFiringAt x y r o]).equations
      (.var res) b := by
  intro δ solved
  rw [projection_store] at solved
  have first := solved _ List.mem_cons_self
  have second := solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
  change δ.applyTerm _ = δ.applyTerm (label o) at first
  rw [labelled] at first
  simp only [applyTerm_evaluate, applyTerm_secondP, applyTerm_pairP, closedA, closedB] at first
  obtain ⟨inner, results⟩ := evaluate_injective first
  obtain ⟨_, payloads⟩ := pairP_injective (secondP_injective inner)
  change δ.applyTerm (.var r) = δ.applyTerm (.var y) at second
  change δ.applyTerm (.var res) = δ.applyTerm b
  rw [closedB, ← results, second, payloads]

/-- A quoted closed value is fixed by every substitution. -/
theorem closed_of_quote {t : Tm Presentation.Tower.Head 0} {p : Pattern}
    (quoted : quoteValue holCanonical t = some p) (σ : Subst signature) : σ.applyTerm p = p :=
  applyTerm_quoteValue holCanonical t quoted σ (fun i => i.elim0)

theorem hol_closed (σ : Subst signature) : σ.applyTerm holPattern = holPattern :=
  closed_of_quote quote_hol σ

theorem payload_closed (wire : NativeWireData.Wire) (σ : Subst signature) :
    σ.applyTerm (payloadPattern wire) = payloadPattern wire :=
  closed_of_quote (quote_payload wire) σ

theorem payload_readback (wire : NativeWireData.Wire) :
    (readback holCanonical (payloadPattern wire) : Option (Tm Presentation.Tower.Head 0)) =
      some (NativeWireData.encode wire) :=
  readback_quoteValue holCanonical _ (quote_payload wire)

/-- **The compiled run of the projection, for every wire.** The compiler reads the source; the
compiled run executes as a compiled step; its final store observes the quoted wire data, whose
readback is the source's value. -/
theorem projection_square (wire : NativeWireData.Wire) :
    compile holCanonical projectionProgram.callables (projectionSource wire).2.code =
        some (program wire) ∧
      Executable action (programLabel (program wire)) start [(projectionStep 1 2 3 0).firing] ∧
      Observes action (follow (programLabel (program wire)) start [projectionFiring]).equations
        (.var 0) (payloadPattern wire) ∧
      readback holCanonical (payloadPattern wire) = some (NativeWireData.encode (n := 0) wire) ∧
      QTerm.mk (projectionTerm wire) = QTerm.mk (valueTerm wire) := by
  rw [projectionFiringAt_compiled]
  exact ⟨compile_source wire,
    projection_executes _ _ _ (by decide) (by decide) (by decide) rfl hol_closed (payload_closed wire),
    projection_observes _ _ _ rfl hol_closed (payload_closed wire),
    payload_readback wire,
    (projectionEvidence wire).class_eq⟩

/-! ## A concrete wire and its checked result -/

/-- A wire application with a symbol and a natural argument. -/
def exampleWire : NativeWireData.Wire := .application "pair" [.symbol "x", .natural 3]

/-- **The result check**, by computation: the unifier solves the final store, and the readback of
the result variable is the source's value. -/
theorem example_certified :
    checkResult holCanonical 16
      (follow (programLabel (program exampleWire)) start [projectionFiring]).equations 0
      (NativeWireData.encode (n := 0) exampleWire) = true := by
  decide +kernel

#print axioms holRootAction
#print axioms holDiscipline
#print axioms projectionEvidence
#print axioms projection_source_side
#print axioms encode_quotes
#print axioms quote_hol
#print axioms projectionRule_sound
#print axioms projectionProgram
#print axioms compile_source
#print axioms projectionFiringAt_compiled
#print axioms projection_executes
#print axioms projection_observes
#print axioms projection_square
#print axioms example_certified

end Projection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
