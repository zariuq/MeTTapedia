import Mettapedia.Languages.VibeITP.Presentation.SimultaneousTraversal
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofs
import Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls

/-! Positive and separating controls for the authored simultaneous operation.
Native expectations come from the independent source operation, not from the
authored evaluator. Logical witnesses additionally exercise exact supplied
definitions and the new proof constructor. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous.Controls

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def F : Spec.SymId := .fresh 0
def G : Spec.SymId := .fresh 1
def D : Spec.SymId := .fresh 2
def H : Spec.SymId := .fresh 3
def K : Spec.SymId := .fresh 4
def L : Spec.SymId := .fresh 5
def f : Spec.Term := .app F []
def g : Spec.Term := .app G []
def pair : Spec.Term := .eq f g

def table : SignatureTable :=
  [(.builtin .eq, ⟨.constant, [0, 0]⟩), (F, Spec.SymInfo.fvarOf 0), (G, Spec.SymInfo.fvarOf 0),
    (D, ⟨.constant, [0, 0]⟩), (H, Spec.SymInfo.fvarOf 2), (K, ⟨.constant, [1]⟩),
    (L, ⟨.constant, [Spec.wordBound - 1]⟩)]

def largeClosed : Spec.Term := .app L [.app K [f]]
def unknown : Spec.Term := .app (.fresh 99) []

theorem crossing :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, g), (G, .natLit 7)], encode pair]
      (encodeResult (some (.eq g (.natLit 7)))) :=
  statement_computes table [(F, g), (G, .natLit 7)] pair

theorem repeated_target :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, .natLit 8), (F, .natLit 9)], encode f]
      (encodeResult (some (.natLit 8))) :=
  statement_computes table [(F, .natLit 8), (F, .natLit 9)] f

theorem shadowed_open_value_refused :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, .natLit 8), (F, .bvar 0)], encode f]
      (encodeResult none) :=
  statement_computes table [(F, .natLit 8), (F, .bvar 0)] f

theorem guarded_shadowed_formation_refused :
    Applies simultaneousProgram computationalHost "vibe:thm-instantiate-many"
      [encodeTable table, encodeReplacements [(F, .natLit 8), (F, unknown)], encode f]
      (encodeResult none) :=
  theorem_computes table [(F, .natLit 8), (F, unknown)] f

theorem depth_only_shadow_is_separate :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, .natLit 8), (F, unknown)], encode f]
      (encodeResult (some (.natLit 8))) :=
  statement_computes table [(F, .natLit 8), (F, unknown)] f

theorem binding_preserved :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(H, .eq (.bvar 1) (.bvar 0))],
        encode (.app K [.app H [.bvar 0, .natLit 4]])]
      (encodeResult (some (.app K [.eq (.bvar 0) (.natLit 4)]))) :=
  statement_computes table [(H, .eq (.bvar 1) (.bvar 0))] (.app K [.app H [.bvar 0, .natLit 4]])

theorem replacement_not_revisited :
    ¬ Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, g), (G, .natLit 7)], encode pair]
      (encodeResult (some (.eq (.natLit 7) (.natLit 7)))) := by
  rw [statement_accepts_iff]
  decide +kernel

theorem zero_entries_skip_traversal :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [], encode largeClosed]
      (encodeResult (some largeClosed)) := statement_computes table [] largeClosed

theorem visited_binder_overflow_refuses :
    Applies simultaneousProgram computationalHost "vibe:instantiate-many"
      [encodeTable table, encodeReplacements [(F, .natLit 8)], encode largeClosed]
      (encodeResult none) := statement_computes table [(F, .natLit 8)] largeClosed

theorem prior_single_instantiation_unchanged :
    apply simultaneousProgram computationalHost 256 "vibe:instantiate"
      [encodeTable table, encodeSymbol F, encode g, encode pair] =
    apply ComputationalInference.inferenceProgram computationalHost 256 "vibe:instantiate"
      [encodeTable table, encodeSymbol F, encode g, encode pair] :=
  old_inference_execution 256 "vibe:instantiate" (by decide +kernel) _

def theory : Spec.Theory :=
  ⟨signatureOf table, [], [⟨D, [F, G], pair⟩]⟩

def sourceDefinition : Spec.Term := Spec.definitionStatement theory.sig D [F, G] pair
def expectedDefinition : Spec.Term :=
  .eq (.app D [g, .natLit 7]) (.eq g (.natLit 7))

def definitionWitness : SimultaneousProofs.Witness := .base (.definition 0 [0, 1])
def crossingWitness : SimultaneousProofs.Witness :=
  .instantiateMany [(F, g), (G, .natLit 7)] definitionWitness

theorem supplied_definition_checked :
    SimultaneousProofs.Witness.check theory definitionWitness sourceDefinition = true := by decide +kernel

theorem supplied_crossing_checked :
    SimultaneousProofs.Witness.check theory crossingWitness expectedDefinition = true := by decide +kernel

theorem supplied_crossing_derives : Spec.DerivesV2 theory expectedDefinition :=
  SimultaneousProofs.Witness.check_sound (theory := theory) (witness := crossingWitness)
    supplied_crossing_checked

theorem authored_crossing_derives : Spec.DerivesV2 theory expectedDefinition :=
  theorem_derives table rfl [(F, g), (G, .natLit 7)]
    (SimultaneousProofs.Witness.check_sound (theory := theory) (witness := definitionWitness)
      supplied_definition_checked)
    (theorem_computes table [(F, g), (G, .natLit 7)] sourceDefinition)

theorem wrong_definition_hint_refused :
    SimultaneousProofs.Witness.result theory (.base (.definition 0 [1, 0])) = none := by decide +kernel

theorem missing_source_proof_refused :
    SimultaneousProofs.Witness.result theory (.instantiateMany [(F, .natLit 7)] (.base (.axiom 0))) = none := by
  decide +kernel

theorem supplied_shadowed_unknown_refused :
    SimultaneousProofs.Witness.result theory
      (.instantiateMany [(F, g), (F, unknown)] definitionWitness) = none := by decide +kernel

/-- Existential coverage at the actual admitted byte-run theory. This does not
extract a certificate-producing algorithm from a proof of derivability. -/
private theorem state_certificate (state : Spec.State)
    (invariant : Spec.ProtocolV2Invariant.Invariant state []) (goal : Spec.Term)
    (derived : Spec.DerivesV2 state.theory goal) :
    ∃ witness, SimultaneousProofs.Witness.check state.theory witness goal = true :=
  (SimultaneousProofs.derives_iff_checked invariant.theory goal).mp derived

private theorem state_checked_certificate (state : Spec.State)
    (invariant : Spec.ProtocolV2Invariant.Invariant state []) (goal : Spec.Term)
    (derived : Spec.DerivesV2 state.theory goal) :
    ∃ witness, SimultaneousProofs.Witness.Checks state.theory witness goal :=
  SimultaneousProofs.certificate_exists invariant.theory derived

open Native.ProtocolV2LogicalControls in
theorem byte_run_has_checked_certificate :
    ∃ witness, SimultaneousProofs.Witness.Checks finalState.theory witness
      Spec.ProtocolV2.Controls.crossingResult :=
  state_checked_certificate finalState final_invariant Spec.ProtocolV2.Controls.crossingResult registered_goal_derived

open Native.ProtocolV2LogicalControls in
theorem byte_run_has_finite_certificate :
    ∃ witness, SimultaneousProofs.Witness.check finalState.theory witness
      Spec.ProtocolV2.Controls.crossingResult = true :=
  state_certificate finalState final_invariant Spec.ProtocolV2.Controls.crossingResult registered_goal_derived

structure Request where
  name : String
  head : String
  arguments : List Term
  expected : Outcome
  fuel : Nat := 256

def statementRequest (name : String) (signature : SignatureTable)
    (replacements : List (Spec.SymId × Spec.Term)) (source : Spec.Term) : Request :=
  ⟨name, "vibe:instantiate-many", [encodeTable signature, encodeReplacements replacements, encode source],
    .value (encodeResult (Spec.SimultaneousInstantiation.statement (signatureOf signature) replacements source)), 256⟩

def theoremRequest (name : String) (signature : SignatureTable)
    (replacements : List (Spec.SymId × Spec.Term)) (source : Spec.Term) : Request :=
  ⟨name, "vibe:thm-instantiate-many", [encodeTable signature, encodeReplacements replacements, encode source],
    .value (encodeResult (if replacements.all (fun pair => Spec.WellFormed (signatureOf signature) pair.2) then
      Spec.SimultaneousInstantiation.statement (signatureOf signature) replacements source else none)), 256⟩

def rawRequest (name : String) (signature : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (source : Spec.Term) : Request :=
  ⟨name, "vibe:many-go", [encodeTable signature, encodeEntries entries, natural offset, encode source],
    .value (encodeResult (Spec.SimultaneousInstantiation.go (signatureOf signature) entries offset source)), 256⟩

def primitiveRequest (name head : String) (arguments : List Term) : Request :=
  ⟨name, head, arguments,
    (match computationalHost.primitive head arguments with
      | .value result => .value result
      | .fault => .failure
      | .unhandled => .value (.expr (.sym head :: arguments))), 0⟩

def requests : List Request := [
  statementRequest "crossing" table [(F, g), (G, .natLit 7)] pair,
  statementRequest "swap" table [(F, g), (G, f)] pair,
  statementRequest "first-duplicate" table [(F, .natLit 8), (F, .natLit 9)] f,
  statementRequest "invalid-shadow" table [(F, .natLit 8), (F, .bvar 0)] f,
  statementRequest "unused-invalid" table [(G, .bvar 0)] (.natLit 3),
  statementRequest "constant-target" table [(K, .natLit 8)] f,
  statementRequest "unknown-target" table [(.fresh 99, .natLit 8)] f,
  statementRequest "under-binder" table [(H, .eq (.bvar 1) (.bvar 0))] (.app K [.app H [.bvar 0, .natLit 4]]),
  statementRequest "two-arguments" table [(H, .eq (.bvar 1) (.bvar 0))] (.app H [.natLit 3, .natLit 4]),
  statementRequest "open-result" table [] (.bvar 0),
  statementRequest "zero-copy" table [] largeClosed,
  statementRequest "visited-overflow" table [(F, .natLit 8)] largeClosed,
  statementRequest "depth-only-shadow" table [(F, .natLit 8), (F, unknown)] f,
  theoremRequest "guarded-shadow" table [(F, .natLit 8), (F, unknown)] f,
  theoremRequest "unused-unknown-value" table [(G, unknown)] f,
  theoremRequest "definition-instance" table [(F, g), (G, .natLit 7)] sourceDefinition,
  theoremRequest "definition-swap" table [(F, g), (G, f)] sourceDefinition,
  rawRequest "raw-open-shift" table [⟨F, 0, .bvar 0⟩] 0 (.app K [f]),
  rawRequest "raw-literal-large-offset" table [⟨F, 0, .bvar 0⟩] Spec.wordBound (.lit [0, 255, 42]),
  rawRequest "raw-bound-large-offset" table [] Spec.wordBound (.bvar Spec.wordBound),
  rawRequest "shift-overflow" table [⟨F, 0, .bvar (Spec.wordBound - 2)⟩] 1 f,
  statementRequest "large-symbol-id" [(.fresh (Spec.wordBound + 13), Spec.SymInfo.fvarOf 0)]
    [(.fresh (Spec.wordBound + 13), .natLit 8)] (.app (.fresh (Spec.wordBound + 13)) []),
  ⟨"exhaustion-is-not-refusal", "vibe:instantiate-many",
    [encodeTable table, encodeReplacements [(F, g)], encode f], .exhausted, 0⟩,
  primitiveRequest "scalar-add" "nik:nat-add" [natural 17, natural 5],
  primitiveRequest "scalar-large-add" "nik:nat-add" [natural (Spec.wordBound + 13), natural 7],
  primitiveRequest "scalar-bad-decimal" "nik:nat-add" [.lit "12x", natural 1],
  primitiveRequest "scalar-negative" "nik:nat-add" [.lit "-1", natural 1],
  primitiveRequest "scalar-empty" "nik:nat-add" [.lit "", natural 1],
  primitiveRequest "scalar-leading-zeros" "nik:nat-add" [.lit "004", natural 1],
  primitiveRequest "scalar-word-bound" "nik:nat-lt" [natural Spec.wordBound, natural Spec.wordBound],
  primitiveRequest "list-view-wrong-kind" "nik:list-view" [.expr []],
  primitiveRequest "list-retains-code-looking-data" "nik:list-cons"
    [.expr [.sym "eval", .sym "side-effect"], .list []]]

#print axioms authored_crossing_derives
#print axioms supplied_crossing_derives
#print axioms binding_preserved

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous.Controls
