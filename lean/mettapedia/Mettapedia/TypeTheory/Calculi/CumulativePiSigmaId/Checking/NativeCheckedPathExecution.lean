import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeContextualComputationCompleteness
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionPaths
import Mettapedia.Logic.Relation.DecodedPath
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Functorial execution of checked native computation paths

Every decoded directed step acts on accepted finite typing certificates at a
fixed context and displayed type. Mathlib's free path-category lift extends
that actual executor to finite paths: identity keeps the original certificate,
and concatenation computes exactly sequential certificate execution.

The input is a supplied path, not a strategy or a termination argument. Its
edges retain the actual selected occurrence codes, including repeated steps.
The conversion-class observation is preserved; certificate trees need not be.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedPathExecution

open Presentation NativeIndexedFamilies NativeJudgmentReplay Quiver
open _root_.CategoryTheory

abbrev Certificate (context : NativeCheckedSubstitution.Context)
    (displayed subject : Tower.Tm context.arity) :=
  {code : Code context.arity // check context.raw subject displayed context.code code = true}

/-- Extract the actual computed output, using completeness only to exclude
failure. No certificate is selected from an existential proposition. -/
def step (context : NativeCheckedSubstitution.Context) (displayed : Tower.Tm context.arity)
    {source target : NativeConversionPaths.Vertex context.arity} (edge : source ⟶ target)
    (input : Certificate context displayed source) : Certificate context displayed target :=
  match computed : ContextualComputation.execute edge.val context.code displayed input.val with
  | none => False.elim (by
      obtain ⟨output, accepted, _⟩ := ContextualComputation.execute_complete
        edge.val edge.property input.property
      rw [computed] at accepted
      cases accepted)
  | some output => ⟨output, by
      obtain ⟨result, accepted, checked⟩ := ContextualComputation.execute_complete
        edge.val edge.property input.property
      rw [computed] at accepted
      cases accepted
      exact checked⟩

theorem step_computes (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity)
    {source target : NativeConversionPaths.Vertex context.arity} (edge : source ⟶ target)
    (input : Certificate context displayed source) :
    ContextualComputation.execute edge.val context.code displayed input.val =
      some (step context displayed edge input).val := by
  unfold step
  split
  · rename_i computed
    obtain ⟨output, accepted, _⟩ := ContextualComputation.execute_complete
      edge.val edge.property input.property
    rw [computed] at accepted
    cases accepted
  · assumption

def edgeAction (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity) : NativeConversionPaths.Vertex context.arity ⥤q Type where
  obj subject := Certificate context displayed subject
  map edge := TypeCat.ofHom (step context displayed edge)

/-- The existing free path-category construction supplies composition. -/
def execution (context : NativeCheckedSubstitution.Context) (displayed : Tower.Tm context.arity) :
    Paths (NativeConversionPaths.Vertex context.arity) ⥤ Type :=
  Paths.lift (edgeAction context displayed)

def run (context : NativeCheckedSubstitution.Context) (displayed : Tower.Tm context.arity)
    {source target : NativeConversionPaths.Vertex context.arity} (path : Path source target)
    (input : Certificate context displayed source) : Certificate context displayed target :=
  (execution context displayed).map path input

@[simp] theorem run_nil (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity) (subject : NativeConversionPaths.Vertex context.arity)
    (input : Certificate context displayed subject) :
    run context displayed (.nil : Path subject subject) input = input := rfl

@[simp] theorem run_cons (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity)
    {source middle target : NativeConversionPaths.Vertex context.arity}
    (path : Path source middle) (edge : middle ⟶ target)
    (input : Certificate context displayed source) :
    run context displayed (path.cons edge) input =
      step context displayed edge (run context displayed path input) := rfl

theorem run_comp (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity)
    {source middle target : NativeConversionPaths.Vertex context.arity}
    (first : Path source middle) (second : Path middle target)
    (input : Certificate context displayed source) :
    run context displayed (first.comp second) input =
      run context displayed second (run context displayed first input) := by
  exact congrArg (fun f => f input) ((execution context displayed).map_comp first second)

def receipt {context : NativeCheckedSubstitution.Context}
    {displayed subject : Tower.Tm context.arity} (certificate : Certificate context displayed subject) :
    NativeCheckedSubstitution.JudgmentReceipt context :=
  ⟨subject, displayed, certificate.val, certificate.property⟩

theorem run_observation (context : NativeCheckedSubstitution.Context)
    (displayed : Tower.Tm context.arity)
    {source target : NativeConversionPaths.Vertex context.arity} (path : Path source target)
    (input : Certificate context displayed source) :
    (receipt (run context displayed path input)).observe = (receipt input).observe := by
  induction path with
  | nil => rfl
  | cons path edge ih =>
      rw [run_cons]
      apply Eq.trans _ ih
      exact (NativeCheckedSubstitution.JudgmentReceipt.observe_eq_of_checkedStep
        (receipt (run context displayed path input))
        (receipt (step context displayed edge (run context displayed path input))) rfl
        edge.val (decide_eq_true edge.property)).symm

def reindexGraph {n m : Nat} (substitution : Sub Tower.Head n m) :
    NativeConversionPaths.Vertex n ⥤q NativeConversionPaths.Vertex m where
  obj subject := subst substitution subject
  map edge := ⟨StructuralConversionCode.StepCode.substitute
    NativeRelatorRootConversionCode.substitute substitution edge.val, by
    rw [StructuralConversionCode.StepCode.decode_substitute
      NativeRelatorRootConversionCode.substitute Tower.HeadEq NativeRelatorRootConversionCode.decode
      NativeRelatorRootConversionCode.decode_substitute, edge.property]
    rfl⟩

def reindexCertificate {context destination : NativeCheckedSubstitution.Context}
    (morphism : NativeCheckedSubstitution.Hom destination context)
    {displayed subject : Tower.Tm context.arity} (input : Certificate context displayed subject) :
    Certificate destination (subst morphism.substitution displayed) (subst morphism.substitution subject) :=
  ⟨substitute morphism.substitution morphism.codes subject displayed input.val,
    check_substitute input.property destination.code destination.accepted
      morphism.substitution morphism.codes morphism.accepted⟩

theorem reindexGraph_length {n m : Nat} (substitution : Sub Tower.Head n m)
    {source target : NativeConversionPaths.Vertex n} (path : Path source target) :
    ((reindexGraph substitution).mapPath path).length = path.length :=
  Mettapedia.Logic.Relation.PathConfluence.mapPath_length _ path

/-- The two actual computed certificates have equal semantic observations.
The selected path and every one of its step occurrences are transported by
the existing code substitution; no equality of typing trees is inferred. -/
theorem run_reindex_observation {context destination : NativeCheckedSubstitution.Context}
    (morphism : NativeCheckedSubstitution.Hom destination context)
    {displayed : Tower.Tm context.arity}
    {source target : NativeConversionPaths.Vertex context.arity} (path : Path source target)
    (input : Certificate context displayed source) :
    (receipt (run destination (subst morphism.substitution displayed)
      ((reindexGraph morphism.substitution).mapPath path) (reindexCertificate morphism input))).observe =
    (receipt (reindexCertificate morphism (run context displayed path input))).observe := by
  refine (run_observation destination (subst morphism.substitution displayed)
    ((reindexGraph morphism.substitution).mapPath path) (reindexCertificate morphism input)).trans ?_
  change ((receipt input).reindex morphism).observe =
    ((receipt (run context displayed path input)).reindex morphism).observe
  have original := run_observation context displayed path input
  rw [NativeCheckedSubstitution.JudgmentReceipt.observe_reindex,
    NativeCheckedSubstitution.JudgmentReceipt.observe_reindex, original]

/-! ## Finite source-code boundary

Trace admission inspects terms and selected step codes, not typing trees.
Certificate replay is a separate operation on the admitted path. The endpoint
agreement below licenses this separation, not reconstruction of certificates
from erased results, automatic step selection, or a runtime complexity bound.
Proof-valued program terms remain present. This interface consumes a supplied
trace; it does not require ordinary runtime evaluation to record one.
-/

def decodeEdge {n : Nat} (code : NativeRelatorConversionChecking.StepCode n) :
    Option (Mettapedia.Logic.Relation.DecodedPath.Edge (NativeConversionPaths.Vertex n)) :=
  match decoded : ContextualComputation.decodeStep code with
  | none => none
  | some (source, target) => some ⟨source, target, ⟨code, decoded⟩⟩

def encodeEdge {n : Nat} {source target : NativeConversionPaths.Vertex n}
    (edge : source ⟶ target) : NativeRelatorConversionChecking.StepCode n := edge.val

theorem decodeEdge_roundTrip {n : Nat} {source target : NativeConversionPaths.Vertex n}
    (edge : source ⟶ target) : decodeEdge edge.val = some ⟨source, target, edge⟩ := by
  obtain ⟨code, decoded⟩ := edge
  change ContextualComputation.decodeStep code = some (source, target) at decoded
  unfold decodeEdge
  split <;> rename_i equation
  · rw [decoded] at equation
    cases equation
  · rw [decoded] at equation
    cases Option.some.inj equation
    rfl

theorem decodeEdge_retains {n : Nat} (code : NativeRelatorConversionChecking.StepCode n)
    (edge : Mettapedia.Logic.Relation.DecodedPath.Edge (NativeConversionPaths.Vertex n))
    (decoded : decodeEdge code = some edge) : edge.2.2.val = code := by
  unfold decodeEdge at decoded
  split at decoded
  · contradiction
  · cases Option.some.inj decoded
    rfl

def decodeSteps {n : Nat} (source : NativeConversionPaths.Vertex n)
    (codes : List (NativeRelatorConversionChecking.StepCode n)) :
    Option (Σ target : NativeConversionPaths.Vertex n, Path source target) :=
  Mettapedia.Logic.Relation.DecodedPath.decodeFrom decodeEdge source codes

theorem decodeSteps_encode {n : Nat} {source target : NativeConversionPaths.Vertex n}
    (path : Path source target) :
    decodeSteps source (Mettapedia.Logic.Relation.DecodedPath.encodePath encodeEdge path) =
      some ⟨target, path⟩ :=
  Mettapedia.Logic.Relation.DecodedPath.decodeFrom_encodePath decodeEdge encodeEdge
    decodeEdge_roundTrip path

theorem decodeSteps_retains {n : Nat} (source : NativeConversionPaths.Vertex n)
    (codes : List (NativeRelatorConversionChecking.StepCode n))
    (result : Σ target : NativeConversionPaths.Vertex n, Path source target)
    (decoded : decodeSteps source codes = some result) :
    Mettapedia.Logic.Relation.DecodedPath.encodePath
      encodeEdge result.2 = codes :=
  Mettapedia.Logic.Relation.DecodedPath.encodePath_decodeFrom
    decodeEdge encodeEdge
    decodeEdge_retains source codes result decoded

/-- A raw typing-certificate and step-list interface. The context has already
been checked. No reduction strategy or type-inference procedure is selected. -/
def runCodes (context : NativeCheckedSubstitution.Context)
    (source displayed : Tower.Tm context.arity) (input : Code context.arity)
    (codes : List (NativeRelatorConversionChecking.StepCode context.arity)) :
    Option (Tower.Tm context.arity × Code context.arity) :=
  if accepted : check context.raw source displayed context.code input = true then do
    let ⟨target, path⟩ ← decodeSteps source codes
    return (target, (run context displayed path ⟨input, accepted⟩).val)
  else none

theorem runCodes_complete (context : NativeCheckedSubstitution.Context)
    {source target : NativeConversionPaths.Vertex context.arity}
    {displayed : Tower.Tm context.arity} {input : Code context.arity}
    (accepted : check context.raw source displayed context.code input = true)
    (codes : List (NativeRelatorConversionChecking.StepCode context.arity))
    (path : Path source target) (decoded : decodeSteps source codes = some ⟨target, path⟩) :
    ∃ output, runCodes context source displayed input codes = some (target, output) ∧
      check context.raw target displayed context.code output = true := by
  refine ⟨(run context displayed path ⟨input, accepted⟩).val, ?_,
    (run context displayed path ⟨input, accepted⟩).property⟩
  simp only [runCodes, accepted, ↓reduceDIte, decoded, bind, Option.bind, pure]
  rfl

theorem runCodes_sound (context : NativeCheckedSubstitution.Context)
    {source displayed target : Tower.Tm context.arity} {input output : Code context.arity}
    {codes : List (NativeRelatorConversionChecking.StepCode context.arity)}
    (computed : runCodes context source displayed input codes = some (target, output)) :
    check context.raw target displayed context.code output = true := by
  unfold runCodes at computed
  split at computed
  · rename_i accepted
    cases decoded : decodeSteps source codes with
    | none => simp [decoded] at computed
    | some result =>
        obtain ⟨endpoint, path⟩ := result
        simp only [decoded, bind, Option.bind, pure, Option.some.injEq] at computed
        cases computed
        exact (run context displayed path ⟨input, accepted⟩).property
  · contradiction

/-- Term-only admission and certificate-producing execution return the same
endpoint on every accepted source. Admission needs no intermediate typing
certificates; this is not a certificate reconstruction theorem. -/
theorem runCodes_endpoint (context : NativeCheckedSubstitution.Context)
    {source displayed : Tower.Tm context.arity} {input : Code context.arity}
    (accepted : check context.raw source displayed context.code input = true)
    (codes : List (NativeRelatorConversionChecking.StepCode context.arity)) :
    (runCodes context source displayed input codes).map Prod.fst =
      (decodeSteps source codes).map Sigma.fst := by
  cases decoded : decodeSteps source codes <;>
    simp [runCodes, accepted, decoded] <;> rfl

theorem runCodes_domain (context : NativeCheckedSubstitution.Context)
    (source displayed : Tower.Tm context.arity) (input : Code context.arity)
    (codes : List (NativeRelatorConversionChecking.StepCode context.arity)) :
    (runCodes context source displayed input codes).isSome =
      (check context.raw source displayed context.code input && (decodeSteps source codes).isSome) := by
  unfold runCodes
  split
  · rename_i accepted
    cases decodeSteps source codes <;> simp [accepted]
  · rename_i rejected
    simp [rejected]

#print axioms step_computes
#print axioms run_comp
#print axioms run_observation
#print axioms run_reindex_observation
#print axioms runCodes_complete
#print axioms runCodes_sound
#print axioms runCodes_endpoint
#print axioms runCodes_domain
#print axioms decodeSteps_retains
#print axioms decodeSteps_encode

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedPathExecution
