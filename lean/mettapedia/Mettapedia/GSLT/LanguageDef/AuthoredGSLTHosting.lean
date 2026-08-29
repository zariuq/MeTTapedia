import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
import Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
import Mettapedia.GSLT.Parsing.BackendCorrespondence

/-!
# Authored GSLT hosting through explicit executable targets

A source hash, a rule table, a checker wrapper, and an operational compiler
answer different questions.  This module isolates the semantic core of the
strongest honest hosting claim.

An `ObservedRefinement` is the forward compiler square: every authored source
path maps to a finite target path with the same declared observation.  It
permits both fusion and lowering.  Forward simulation alone is insufficient,
because the target may have additional observable behavior from a compiled
state.  `BehavioralHosting` adds the missing no-invention direction.

The observation is explicit.  Answer bags, faults, completion status, proof
identity, and cost are not silently interchangeable observations.  When exact
execution witnesses matter, `ProofRelevantHosting` additionally requires the
forward map on observation fibres to be an equivalence.  This is intentionally
stronger than behavior-set agreement: a valid fusion may erase administrative
paths while preserving all public results.

For textual languages, `ExactLexicalRealization` first relates the authored
lexical GSLT to its runtime recognizer in both directions.
`WholeTextSurfaceHosting` then composes that layer with the existing
scannerless syntax-GSLT, complete packed forests, authored elaboration, and
operational hosting.  Its surface result pairs retain lexical and syntactic
ambiguity.  `MaySetSurfaceHosting` is the useful fixed-codepoint specialization.
These are explicitly may-set theorems; proof multiplicity is supplied only by
the proof-relevant strengthenings of the individual stages.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.Parsing.CompilerCorrespondence
open Mettapedia.GSLT.Parsing.GuardCorrespondence
open Mettapedia.GSLT.Parsing.PackedForest

universe uValue uIndex uCapability uRaw

/-! ## Observation fibres and two-sided hosting -/

/-- Complete execution witnesses from one initial state that produce one
declared observation.  Retaining this sigma type distinguishes proof-relevant
paths even when their public values coincide. -/
def ObservationFibre {Value : Type uValue}
    (object : ObservedOperationalObject Value)
    (initial : object.operational.theory.Term) (value : Value) :=
  Σ final, { path : ExecutionPath object.operational.theory initial final //
    object.observe path = some value }

/-- The may-observation relation obtained by merely asking whether the exact
execution fibre is inhabited. -/
def ProducesObservation {Value : Type uValue}
    (object : ObservedOperationalObject Value)
    (initial : object.operational.theory.Term) (value : Value) : Prop :=
  Nonempty (ObservationFibre object initial value)

/-- Forward transport of one proof-relevant observed execution along the
existing compiler square. -/
def mapObservationFibre {Value : Type uValue}
    {source target : ObservedOperationalObject Value}
    (refinement : ObservedRefinement source target)
    {initial : source.operational.theory.Term} {value : Value} :
    ObservationFibre source initial value →
      ObservationFibre target
        (refinement.refinement.realization.mapTerm initial) value
  | ⟨final, ⟨path, observed⟩⟩ =>
      ⟨refinement.refinement.realization.mapTerm final,
        ⟨refinement.refinement.realization.mapRoute path,
          (refinement.commutes path).trans observed⟩⟩

/-- A GSLT is hosted by an explicit executable target at one declared
observation when source behavior is realized and target behavior from compiled
states is not invented.  Internal paths may differ. -/
structure BehavioralHosting {Value : Type uValue}
    (source target : ObservedOperationalObject Value) where
  forward : ObservedRefinement source target
  noInvention : ∀ (initial : source.operational.theory.Term) (value : Value),
    ProducesObservation target
        (forward.refinement.realization.mapTerm initial) value →
      ProducesObservation source initial value

namespace BehavioralHosting

variable {Value : Type uValue}
variable {source target middle : ObservedOperationalObject Value}

/-- The executable representation selected by this hosting proof. -/
def compile (hosting : BehavioralHosting source target) :
    source.operational.theory.Term → target.operational.theory.Term :=
  hosting.forward.refinement.realization.mapTerm

/-- Forward simulation preserves every source may-observation. -/
theorem preservesObservation (hosting : BehavioralHosting source target)
    {initial : source.operational.theory.Term} {value : Value}
    (produces : ProducesObservation source initial value) :
    ProducesObservation target (hosting.compile initial) value := by
  obtain ⟨witness⟩ := produces
  exact ⟨mapObservationFibre hosting.forward witness⟩

/-- Hosting is exact on the selected observation may-set. -/
theorem produces_iff (hosting : BehavioralHosting source target)
    (initial : source.operational.theory.Term) (value : Value) :
    ProducesObservation target (hosting.compile initial) value ↔
      ProducesObservation source initial value := by
  constructor
  · exact hosting.noInvention initial value
  · exact hosting.preservesObservation

/-- Identity hosting changes neither paths nor observations. -/
def id (object : ObservedOperationalObject Value) :
    BehavioralHosting object object where
  forward := ObservedRefinement.id object
  noInvention := by
    intro initial value targetProduces
    change ProducesObservation object initial value at targetProduces
    exact targetProduces

/-- Two-sided hosting composes.  The no-invention proof runs backward through
the target chain while forward execution runs in compilation order. -/
def comp (earlier : BehavioralHosting source middle)
    (later : BehavioralHosting middle target) :
    BehavioralHosting source target where
  forward := ObservedRefinement.comp earlier.forward later.forward
  noInvention := by
    intro initial value targetProduces
    exact earlier.noInvention initial value
      (later.noInvention (earlier.compile initial) value targetProduces)

@[simp] theorem comp_compile
    (earlier : BehavioralHosting source middle)
    (later : BehavioralHosting middle target) :
    (earlier.comp later).compile = later.compile ∘ earlier.compile :=
  rfl

/-- Forget no-invention only after obtaining the ordinary operational
refinement used by NIK admission. -/
def toRefinement (hosting : BehavioralHosting source target) :
    Refinement source.operational target.operational :=
  hosting.forward.refinement

/-- Forget all operational and observational structure only at the common
admission-arrow boundary. -/
def toAdmissionHom (hosting : BehavioralHosting source target) :
    source.operational.toAdmissionObject ⟶
      target.operational.toAdmissionObject :=
  hosting.toRefinement.toAdmissionHom

end BehavioralHosting

/-! ## Exact proof-fibre strengthening -/

/-- Strong proof-relevant hosting requires the actual forward execution map
to be an equivalence on every observed fibre.  This is not a prerequisite for
semantic fusion; it is an additional capability when proof/path identity is
part of the hosted contract. -/
structure ProofRelevantHosting {Value : Type uValue}
    (source target : ObservedOperationalObject Value)
    extends BehavioralHosting source target where
  fibreEquiv : ∀ (initial : source.operational.theory.Term) (value : Value),
    ObservationFibre source initial value ≃
      ObservationFibre target
        (toBehavioralHosting.compile initial) value
  fibreEquiv_agrees : ∀ (initial : source.operational.theory.Term)
      (value : Value) (witness : ObservationFibre source initial value),
    fibreEquiv initial value witness =
      mapObservationFibre toBehavioralHosting.forward witness

namespace ProofRelevantHosting

variable {Value : Type uValue}

/-- Proof-relevant hosting projects to exact public behavior hosting. -/
def behavioral {source target : ObservedOperationalObject Value}
    (hosting : ProofRelevantHosting source target) :
    BehavioralHosting source target :=
  hosting.toBehavioralHosting

end ProofRelevantHosting

/-! ## Maximal selection among already-hosting realizations -/

/-- A recognized implementation family whose every member already carries
the two-sided hosting theorem.  Capabilities are evidence-bearing types;
their mere inhabitation is exposed to the existing finite maximal selector.

This ordering is deliberate: recognition and selection may choose among
correct hosted realizations, but they cannot turn a one-way compiler or a
checker wrapper into hosting evidence. -/
structure HostedRecognizedFamily
    (Index : Type uIndex) [PartialOrder Index] [DecidableEq Index]
    {Value : Type uValue}
    (source target : ObservedOperationalObject Value) where
  hosting : Index → BehavioralHosting source target
  Capability : Type uCapability
  Evidence : Index → Capability → Type
  evidence_mono : ∀ {weaker stronger}, weaker ≤ stronger →
    ∀ {capability}, Evidence weaker capability →
      Evidence stronger capability
  strict_evidence_gain : ∀ {weaker stronger}, weaker < stronger →
    ∃ capability, Nonempty (Evidence stronger capability) ∧
      IsEmpty (Evidence weaker capability)
  recognized : Finset Index
  licensed : Finset Index
  licensed_subset_recognized : licensed ⊆ recognized
  licensed_nonempty : licensed.Nonempty

namespace HostedRecognizedFamily

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {Value : Type uValue}
variable {source target : ObservedOperationalObject Value}

/-- Forget the stronger hosting/evidence package only at the existing finite
selection boundary. -/
def toRecognizedFamily
    (family : HostedRecognizedFamily Index source target) :
    RecognizedFamily Index source.operational.toAdmissionObject
      target.operational.toAdmissionObject where
  package := fun index => (family.hosting index).toAdmissionHom
  Capability := family.Capability
  supports := fun index capability =>
    Nonempty (family.Evidence index capability)
  supports_mono := by
    intro weaker stronger related capability supported
    obtain ⟨evidence⟩ := supported
    exact ⟨family.evidence_mono related evidence⟩
  strict_support_gain := by
    intro weaker stronger strict
    obtain ⟨capability, strongerEvidence, weakerEmpty⟩ :=
      family.strict_evidence_gain strict
    exact ⟨capability, strongerEvidence, fun weakerEvidence =>
      weakerEmpty.false weakerEvidence.some⟩
  recognized := family.recognized
  licensed := family.licensed
  licensed_subset_recognized := family.licensed_subset_recognized
  licensed_nonempty := family.licensed_nonempty

/-- A maximal selector returns the original two-sided hosting proof, not only
its erased admission arrow. -/
def selectedHosting (family : HostedRecognizedFamily Index source target)
    (selection :
      family.toRecognizedFamily.MaximalNativeCalculusPrinciple) :
    BehavioralHosting source target :=
  family.hosting selection.1

/-- Maximal selection preserves and reflects every declared observation
because eligibility was already restricted to hosting realizations. -/
theorem selected_produces_iff
    (family : HostedRecognizedFamily Index source target)
    (selection :
      family.toRecognizedFamily.MaximalNativeCalculusPrinciple)
    (initial : source.operational.theory.Term) (value : Value) :
    ProducesObservation target
        ((family.selectedHosting selection).compile initial) value ↔
      ProducesObservation source initial value :=
  (family.selectedHosting selection).produces_iff initial value

/-- Request-local strongest selection likewise returns an already-hosting
realization.  Directedness is needed only to prove that a greatest eligible
member exists, never to establish semantic correctness. -/
def strongestHosting
    (family : HostedRecognizedFamily Index source target)
    (request : family.toRecognizedFamily.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple) :
    BehavioralHosting source target :=
  family.hosting selection.1

theorem strongest_produces_iff
    (family : HostedRecognizedFamily Index source target)
    (request : family.toRecognizedFamily.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (initial : source.operational.theory.Term) (value : Value) :
    ProducesObservation target
        ((family.strongestHosting request selection).compile initial) value ↔
      ProducesObservation source initial value :=
  (family.strongestHosting request selection).produces_iff initial value

end HostedRecognizedFamily

/-! ## Positive: fusion is legitimate behavioral hosting -/

namespace FusionCanary

open NIKObservedRefinement.FusionCanary

private theorem discretePath_final_eq_initial
    {initial final : targetTheory.Term}
    (path : ExecutionPath targetTheory initial final) : final = initial := by
  cases path with
  | refl => rfl
  | cons step rest =>
      exact (show False from by
        simpa [targetTheory, GSLT.discrete, GSLT.Step] using step.down).elim

/-- The existing fused compiler is a genuine hosting realization for its
declared semantic-result observation. -/
def hosting : BehavioralHosting sourceObserved targetObserved where
  forward := observedFusion
  noInvention := by
    intro initial value targetProduces
    obtain ⟨⟨final, path, observed⟩⟩ := targetProduces
    have finalEq : final = initial.2 :=
      (discretePath_final_eq_initial path).trans rfl
    subst final
    have valueEq : initial.2 = value := by
      exact Option.some.inj observed
    subst value
    exact ⟨⟨initial, ⟨.refl initial, rfl⟩⟩⟩

theorem hosting_preserves_result_and_shortens_path :
    (ProducesObservation targetObserved
      (hosting.compile (false, true)) true ↔
        ProducesObservation sourceObserved (false, true) true) ∧
      (fusionRealization.mapRoute sourcePath).length < sourcePath.length :=
  ⟨hosting.produces_iff (false, true) true, fused_path_is_shorter⟩

/-- The source reflexive path and its administrative step are distinct
proof-relevant witnesses of the same public result. -/
def sourceReflWitness :
    ObservationFibre sourceObserved (false, true) true :=
  ⟨(false, true), ⟨.refl (false, true), rfl⟩⟩

def sourceStepWitness :
    ObservationFibre sourceObserved (false, true) true :=
  ⟨(true, true), ⟨sourcePath, rfl⟩⟩

theorem sourceWitnesses_distinct :
    sourceReflWitness ≠ sourceStepWitness := by
  intro equal
  have finalEqual := congrArg Sigma.fst equal
  have firstEqual := congrArg Prod.fst finalEqual
  exact Bool.false_ne_true firstEqual

private theorem discreteLoop_eq_refl
    {initial : targetTheory.Term}
    (path : ExecutionPath targetTheory initial initial) :
    path = .refl initial := by
  cases path with
  | refl => rfl
  | cons step rest =>
      exact (show False from by
        simpa [targetTheory, GSLT.discrete, GSLT.Step] using step.down).elim

private theorem targetObservationWitness_unique
    (left right : ObservationFibre targetObserved true true) :
    left = right := by
  obtain ⟨leftFinal, leftPath, leftObserved⟩ := left
  obtain ⟨rightFinal, rightPath, rightObserved⟩ := right
  have leftFinalEq : leftFinal = true := Option.some.inj leftObserved
  have rightFinalEq : rightFinal = true := Option.some.inj rightObserved
  subst leftFinal
  subst rightFinal
  have leftPathEq : leftPath = .refl true :=
    discreteLoop_eq_refl leftPath
  have rightPathEq : rightPath = .refl true :=
    discreteLoop_eq_refl rightPath
  cases leftPathEq
  cases rightPathEq
  rfl

/-- Fusion maps those two distinct administrative histories to the same
target history.  It therefore earns behavioral hosting but not exact
proof-fibre preservation for this forward realization. -/
theorem forward_fibre_not_injective :
    ¬ Function.Injective
      (mapObservationFibre observedFusion
        (initial := (false, true)) (value := true)) := by
  intro injective
  apply sourceWitnesses_distinct
  apply injective
  exact targetObservationWitness_unique _ _

/-- A nonempty recognized family exercises maximal selection on a genuine
two-sided hosting realization. -/
def hostedFamily :
    HostedRecognizedFamily (Fin 1) sourceObserved targetObserved where
  hosting := fun _ => hosting
  Capability := Unit
  Evidence := fun _ _ => Unit
  evidence_mono := fun _ => id
  strict_evidence_gain := by
    intro weaker stronger strict
    have impossible : False := by
      fin_cases weaker
      fin_cases stronger
      exact (lt_irrefl (0 : Fin 1)) strict
    exact impossible.elim
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

theorem selected_fusion_is_exact_on_results :
    ∃ selection :
        hostedFamily.toRecognizedFamily.MaximalNativeCalculusPrinciple,
      ProducesObservation targetObserved
          ((hostedFamily.selectedHosting selection).compile
            (false, true)) true ↔
        ProducesObservation sourceObserved (false, true) true := by
  obtain ⟨selection⟩ := hostedFamily.toRecognizedFamily.principle_inhabited
  exact ⟨selection,
    hostedFamily.selected_produces_iff selection (false, true) true⟩

end FusionCanary

/-! ## Negative: forward simulation and checker authority do not imply hosting -/

namespace ExtraBehaviorCanary

@[reducible] def sourceTheory : GSLT := GSLT.discrete Unit

@[reducible] def targetTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first last => first = false ∧ last = true
  rewrites_resp_left := by
    rintro first first' last firstEq ⟨sourceEq, targetEq⟩
    subst first'
    exact ⟨last, ⟨sourceEq, targetEq⟩, rfl⟩
  rewrites_resp_right := by
    rintro first last last' ⟨sourceEq, targetEq⟩ lastEq
    subst last'
    exact ⟨sourceEq, targetEq⟩

@[reducible] def sourceOperational : OperationalObject where
  theory := sourceTheory
  Meaning := fun value => value = ()

@[reducible] def targetOperational : OperationalObject where
  theory := targetTheory
  Meaning := fun _ => True

@[reducible] def sourceObserved : ObservedOperationalObject Bool where
  operational := sourceOperational
  observe := fun _ => some false

@[reducible] def targetObserved : ObservedOperationalObject Bool where
  operational := targetOperational
  observe := fun {_ final} _ => some final

def forwardRealization : OperationalRealization sourceTheory targetTheory where
  mapTerm := fun _ => false
  mapEquiv := fun _ => rfl
  mapStep := by
    intro first last step
    exact (show False from by
      simp [sourceTheory, GSLT.discrete, GSLT.Step] at step).elim

def forwardRefinement : Refinement sourceOperational targetOperational where
  realization := forwardRealization
  preservesMeaning := fun _ _ => trivial

/-- Every source path is preserved; there are simply no source steps to map. -/
def forward : ObservedRefinement sourceObserved targetObserved where
  refinement := forwardRefinement
  commutes := by
    intro first last path
    cases path with
    | refl => rfl
    | cons step rest =>
        exact (show False from by
          simpa [sourceTheory, GSLT.discrete, GSLT.Step] using step.down).elim

def extraStep : targetTheory.Step false true :=
  ⟨rfl, rfl⟩

def extraPath : ExecutionPath targetTheory false true :=
  .cons ⟨extraStep⟩ (.refl true)

theorem target_produces_extra_true :
    ProducesObservation targetObserved false true :=
  ⟨⟨true, ⟨extraPath, rfl⟩⟩⟩

theorem source_never_produces_true :
    ¬ ProducesObservation sourceObserved () true := by
  rintro ⟨⟨final, path, observed⟩⟩
  have impossible : false = true := Option.some.inj observed
  exact Bool.false_ne_true impossible

/-- Forward observation agreement is strictly weaker than hosting. -/
theorem forward_refinement_does_not_host :
    Nonempty (ObservedRefinement sourceObserved targetObserved) ∧
      ¬ Nonempty (BehavioralHosting sourceObserved targetObserved) := by
  constructor
  · exact ⟨forward⟩
  · rintro ⟨hosting⟩
    have compiledFalse : hosting.compile () = false := by
      have observed := hosting.forward.commutes (.refl ())
      exact Option.some.inj observed
    have targetProduces :
        ProducesObservation targetObserved (hosting.compile ()) true := by
      rw [compiledFalse]
      exact target_produces_extra_true
    exact source_never_produces_true
      (hosting.noInvention () true targetProduces)

def boundaryChecker :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker Unit Unit where
  check := fun _ _ => true

def BoundaryMeaning (claim : Unit) : Prop := claim = ()

theorem boundaryChecker_authority :
    boundaryChecker.Authority BoundaryMeaning where
  sound := by
    intro claim certificate accepted
    cases claim
    rfl
  complete := by
    intro claim meaningful
    exact ⟨(), rfl⟩

/-- Even an exact, sound, certificate-complete boundary checker beside a
forward compiler square cannot manufacture the missing no-invention law. -/
theorem checker_and_forward_still_do_not_host :
    boundaryChecker.Authority BoundaryMeaning ∧
      Nonempty (ObservedRefinement sourceObserved targetObserved) ∧
      ¬ Nonempty (BehavioralHosting sourceObserved targetObserved) :=
  ⟨boundaryChecker_authority, forward_refinement_does_not_host⟩

/-- Consequently no nonempty licensed implementation family can be formed
for this source/target pair.  The selector has no constructor with which to
mint the missing backward law. -/
theorem no_hosted_recognized_family
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index] :
    ¬ Nonempty
      (HostedRecognizedFamily Index sourceObserved targetObserved) := by
  rintro ⟨family⟩
  obtain ⟨index, _⟩ := family.licensed_nonempty
  exact forward_refinement_does_not_host.2 ⟨family.hosting index⟩

end ExtraBehaviorCanary

/-! ## Raw-source lexical realization -/

/-- A runtime scanner realizes an authored lexical GSLT exactly when it
recognizes every authored stream and invents none.  `Raw` may be bytes, a
rope, or an incrementally supplied source object.  The intermediate stream is
codepoints because the current packed GLL/GLR correspondence is scannerless;
a separately tokenizing lexer can instead encode its token classes as the
lexical productions of that scannerless presentation. -/
structure ExactLexicalRealization
    {Raw : Type uRaw}
    (authored runtime : Raw → List Codepoint → Prop) : Prop where
  runtime_iff_authored : ∀ raw codepoints,
    runtime raw codepoints ↔ authored raw codepoints

namespace ExactLexicalRealization

variable {Raw : Type uRaw}
variable {authored middle runtime : Raw → List Codepoint → Prop}

def id (relation : Raw → List Codepoint → Prop) :
    ExactLexicalRealization relation relation where
  runtime_iff_authored := fun _ _ => Iff.rfl

def comp (earlier : ExactLexicalRealization authored middle)
    (later : ExactLexicalRealization middle runtime) :
    ExactLexicalRealization authored runtime where
  runtime_iff_authored := fun raw codepoints =>
    (later.runtime_iff_authored raw codepoints).trans
      (earlier.runtime_iff_authored raw codepoints)

end ExactLexicalRealization

namespace LexicalAlternativeCanary

def authored (_ : Unit) (codepoints : List Codepoint) : Prop :=
  codepoints = [] ∨ codepoints = [0]

def incompleteRuntime (_ : Unit) (codepoints : List Codepoint) : Prop :=
  codepoints = []

theorem authored_has_second_alternative : authored () [0] :=
  Or.inr rfl

theorem runtime_misses_second_alternative :
    ¬ incompleteRuntime () [0] := by
  simp [incompleteRuntime]

/-- A scanner that drops one lexical alternative cannot be admitted as an
exact realization, even if all of its returned streams are authored. -/
theorem no_exact_realization :
    ¬ Nonempty (ExactLexicalRealization authored incompleteRuntime) := by
  rintro ⟨realization⟩
  exact runtime_misses_second_alternative
    ((realization.runtime_iff_authored () [0]).mpr
      authored_has_second_alternative)

end LexicalAlternativeCanary

/-! ## Whole raw-source to execution composition -/

/-- One complete textual hosting package.  A language may supply UTF decoding
as one exact lexical realization and lexical classification as another, then
compose them before this boundary.  A scannerless grammar simply treats those
classes as ordinary authored grammar definitions. -/
structure WholeTextSurfaceHosting
    {Raw : Type uRaw}
    (authoredLex runtimeLex : Raw → List Codepoint → Prop)
    (presentation :
      Mettapedia.GSLT.Parsing.GuardCorrespondence.SourceDefinition)
    {Value : Type uValue}
    (source target : ObservedOperationalObject Value) where
  lexical : ExactLexicalRealization authoredLex runtimeLex
  forest : List Codepoint → Forest
  complete : ∀ codepoints, Complete (forest codepoints) presentation codepoints
  Elaborates : ParseTree → source.operational.theory.Term → Prop
  operational : BehavioralHosting source target

namespace WholeTextSurfaceHosting

variable {Raw : Type uRaw}
variable {authoredLex runtimeLex : Raw → List Codepoint → Prop}
variable {presentation :
  Mettapedia.GSLT.Parsing.GuardCorrespondence.SourceDefinition}
variable {Value : Type uValue}
variable {source target : ObservedOperationalObject Value}

/-- Authored surface alternatives retain both the admitted lexical stream and
the parse tree.  This prevents two lexings with equal ASTs from being silently
identified at the source boundary. -/
def AuthoredSurfaceResults
    (_pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) : Set (List Codepoint × ParseTree) :=
  fun result => authoredLex raw result.1 ∧
    result.2 ∈
      Mettapedia.GSLT.Parsing.GuardCorrespondence.sourceResults
        presentation result.1

/-- Runtime surface alternatives use the concrete scanner relation and its
complete packed forest. -/
def RuntimeSurfaceResults
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) : Set (List Codepoint × ParseTree) :=
  fun result => runtimeLex raw result.1 ∧
    result.2 ∈
      Mettapedia.GSLT.Parsing.PackedForest.packedResults
        (pipeline.forest result.1) presentation result.1

/-- Lexical exactness and packed-parser completeness compose without choosing
one lexical or syntactic alternative. -/
theorem surfaceResults_exact
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) :
    pipeline.RuntimeSurfaceResults raw = pipeline.AuthoredSurfaceResults raw := by
  ext result
  constructor
  · rintro ⟨runtimeLexes, packedTree⟩
    exact ⟨(pipeline.lexical.runtime_iff_authored raw result.1).mp
        runtimeLexes,
      (Mettapedia.GSLT.Parsing.PackedForest.packedResults_subset_sourceResults
          (pipeline.forest result.1) presentation result.1) packedTree⟩
  · rintro ⟨authoredLexes, sourceTree⟩
    refine ⟨(pipeline.lexical.runtime_iff_authored raw result.1).mpr
        authoredLexes, ?_⟩
    rw [Mettapedia.GSLT.Parsing.PackedForest.complete_result_set_agreement
      (pipeline.complete result.1)]
    exact sourceTree

def SurfaceAmbiguous
    (results : Set (List Codepoint × ParseTree)) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem surface_ambiguity_preserved
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) :
    SurfaceAmbiguous (pipeline.RuntimeSurfaceResults raw) ↔
      SurfaceAmbiguous (pipeline.AuthoredSurfaceResults raw) := by
  rw [pipeline.surfaceResults_exact raw]

def SourceProduces
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) (value : Value) : Prop :=
  ∃ codepoints tree,
    authoredLex raw codepoints ∧
      tree ∈ Mettapedia.GSLT.Parsing.GuardCorrespondence.sourceResults
        presentation codepoints ∧
      ∃ term, pipeline.Elaborates tree term ∧
        ProducesObservation source term value

def TargetProduces
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) (value : Value) : Prop :=
  ∃ codepoints tree,
    runtimeLex raw codepoints ∧
      tree ∈ Mettapedia.GSLT.Parsing.PackedForest.packedResults
        (pipeline.forest codepoints) presentation codepoints ∧
      ∃ term, pipeline.Elaborates tree term ∧
        ProducesObservation target (pipeline.operational.compile term) value

/-- The complete end-to-end may-observation theorem begins at the raw source,
not at a hand-supplied AST or token ledger. -/
theorem targetProduces_iff_sourceProduces
    (pipeline : WholeTextSurfaceHosting authoredLex runtimeLex presentation
      source target)
    (raw : Raw) (value : Value) :
    pipeline.TargetProduces raw value ↔ pipeline.SourceProduces raw value := by
  constructor
  · rintro ⟨codepoints, tree, runtimeLexes, packedTree, term,
      elaborates, targetProduces⟩
    refine ⟨codepoints, tree,
      (pipeline.lexical.runtime_iff_authored raw codepoints).mp runtimeLexes,
      ?_, term, elaborates, ?_⟩
    · exact
        (Mettapedia.GSLT.Parsing.PackedForest.packedResults_subset_sourceResults
            (pipeline.forest codepoints) presentation codepoints) packedTree
    · exact pipeline.operational.noInvention term value targetProduces
  · rintro ⟨codepoints, tree, authoredLexes, sourceTree, term,
      elaborates, sourceProduces⟩
    refine ⟨codepoints, tree,
      (pipeline.lexical.runtime_iff_authored raw codepoints).mpr authoredLexes,
      ?_, term, elaborates, ?_⟩
    · rw [Mettapedia.GSLT.Parsing.PackedForest.complete_result_set_agreement
        (pipeline.complete codepoints)]
      exact sourceTree
    · exact pipeline.operational.preservesObservation sourceProduces

end WholeTextSurfaceHosting

/-! ## Codepoint-to-execution may-set composition -/

/-- A complete packed parser, an authored elaboration relation, and one
two-sided operational hosting proof.  `Elaborates` is a relation rather than a
function so authored ambiguity may remain explicit. -/
structure MaySetSurfaceHosting {Value : Type uValue}
    (presentation :
      Mettapedia.GSLT.Parsing.GuardCorrespondence.SourceDefinition)
    (input : List Codepoint)
    (source target : ObservedOperationalObject Value) where
  forest : Forest
  complete : Complete forest presentation input
  Elaborates : ParseTree → source.operational.theory.Term → Prop
  operational : BehavioralHosting source target

namespace MaySetSurfaceHosting

variable {Value : Type uValue}
variable {presentation :
  Mettapedia.GSLT.Parsing.GuardCorrespondence.SourceDefinition}
variable {input : List Codepoint}
variable {source target : ObservedOperationalObject Value}

/-- Semantics from authored parse trees through authored elaboration and
source execution. -/
def SourceProduces (pipeline :
    MaySetSurfaceHosting presentation input source target) (value : Value) : Prop :=
  ∃ tree, tree ∈
      Mettapedia.GSLT.Parsing.GuardCorrespondence.sourceResults
        presentation input ∧
    ∃ term, pipeline.Elaborates tree term ∧
      ProducesObservation source term value

/-- Semantics obtained from the complete packed forest and compiled target
execution. -/
def TargetProduces (pipeline :
    MaySetSurfaceHosting presentation input source target) (value : Value) : Prop :=
  ∃ tree, tree ∈
      Mettapedia.GSLT.Parsing.PackedForest.packedResults
        pipeline.forest presentation input ∧
    ∃ term, pipeline.Elaborates tree term ∧
      ProducesObservation target (pipeline.operational.compile term) value

/-- Parser completeness/reflection and operational hosting compose into an
end-to-end codepoint-to-target may-observation theorem. -/
theorem targetProduces_iff_sourceProduces
    (pipeline : MaySetSurfaceHosting presentation input source target)
    (value : Value) :
    pipeline.TargetProduces value ↔ pipeline.SourceProduces value := by
  constructor
  · rintro ⟨tree, packedTree, term, elaborates, targetProduces⟩
    refine ⟨tree, ?_, term, elaborates, ?_⟩
    · exact
        (Mettapedia.GSLT.Parsing.PackedForest.packedResults_subset_sourceResults
          pipeline.forest presentation input) packedTree
    · exact pipeline.operational.noInvention term value targetProduces
  · rintro ⟨tree, sourceTree, term, elaborates, sourceProduces⟩
    refine ⟨tree, ?_, term, elaborates, ?_⟩
    · rw [Mettapedia.GSLT.Parsing.PackedForest.complete_result_set_agreement
        pipeline.complete]
      exact sourceTree
    · exact pipeline.operational.preservesObservation sourceProduces

/-- All authored syntactic alternatives remain represented before the
authored elaboration relation is consulted. -/
theorem ambiguity_preserved
    (pipeline : MaySetSurfaceHosting presentation input source target) :
    Mettapedia.GSLT.Parsing.PackedForest.Ambiguous
        (Mettapedia.GSLT.Parsing.PackedForest.packedResults
          pipeline.forest presentation input) ↔
      Mettapedia.GSLT.Parsing.PackedForest.Ambiguous
        (Mettapedia.GSLT.Parsing.GuardCorrespondence.sourceResults
          presentation input) :=
  Mettapedia.GSLT.Parsing.PackedForest.complete_ambiguity_agreement
    pipeline.complete

end MaySetSurfaceHosting

/-! ## Concrete parser-boundary controls inherited by the composition -/

theorem missing_parse_alternative_is_rejected :
    Mettapedia.GSLT.Parsing.BackendCorrespondence.validateForestCovers
      Mettapedia.GSLT.Parsing.BackendCorrespondence.controlReference
      Mettapedia.GSLT.Parsing.BackendCorrespondence.missingAlternativeBackend =
        false :=
  Mettapedia.GSLT.Parsing.BackendCorrespondence.missing_alternative_rejected

theorem spurious_terminal_alternative_is_rejected :
    validateTerminalCompaction
      (Mettapedia.GSLT.Parsing.CompilerCorrespondence.compile
        terminalFamilyPresentation) terminalFamilyOverbroad = false :=
  terminalFamily_validator_rejects_overbroad

#print axioms BehavioralHosting.preservesObservation
#print axioms BehavioralHosting.produces_iff
#print axioms BehavioralHosting.comp
#print axioms FusionCanary.hosting_preserves_result_and_shortens_path
#print axioms FusionCanary.forward_fibre_not_injective
#print axioms FusionCanary.selected_fusion_is_exact_on_results
#print axioms ExtraBehaviorCanary.forward_refinement_does_not_host
#print axioms ExtraBehaviorCanary.checker_and_forward_still_do_not_host
#print axioms ExtraBehaviorCanary.no_hosted_recognized_family
#print axioms LexicalAlternativeCanary.no_exact_realization
#print axioms WholeTextSurfaceHosting.surfaceResults_exact
#print axioms WholeTextSurfaceHosting.surface_ambiguity_preserved
#print axioms WholeTextSurfaceHosting.targetProduces_iff_sourceProduces
#print axioms MaySetSurfaceHosting.targetProduces_iff_sourceProduces
#print axioms MaySetSurfaceHosting.ambiguity_preserved
#print axioms missing_parse_alternative_is_rejected
#print axioms spurious_terminal_alternative_is_rejected

end Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
