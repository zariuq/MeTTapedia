import Mathlib.Data.List.Basic
import Mettapedia.GSLT.Core.Composition

/-!
# Certified compilation of ordered first-order frames

This module isolates a reusable optimization boundary for proof-rule
presentations whose native type information identifies two hypothesis roles:

* binders, which extend a substitution environment from a typed stack entry;
* matches, which check a template under the environment already constructed.

The source interpreter materializes every instantiated match template before
comparing it with the corresponding stack entry.  The compiled interpreter
instead consumes the template and the stack entry together.  The main theorem
proves that the fused flat-sequence pass has exactly the source meaning.

The admission procedure is language-neutral.  It accepts precisely the
syntactic scheduling fragment in which all binders precede all matches.  A
presentation-specific OSLF/NTT projection can classify hypotheses into these
two roles; no token name or guest-language operation occurs here.
-/

namespace Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

universe u v

/-! ## Flat formulas and first-order templates -/

/-- One cell of a flat first-order template. -/
inductive TemplateAtom (Token : Type u) (Var : Type v) where
  | literal (token : Token)
  | hole (holeId : Var)
deriving DecidableEq, Repr

abbrev Template (Token : Type u) (Var : Type v) :=
  List (TemplateAtom Token Var)

abbrev Formula (Token : Type u) := List Token

abbrev Substitution (Var : Type v) (Token : Type u) :=
  Var → Option (Formula Token)

def emptySubstitution : Substitution Var Token := fun _ => none

def insertSubstitution [DecidableEq Var]
    (σ : Substitution Var Token) (holeId : Var) (image : Formula Token) :
    Substitution Var Token :=
  fun candidate => if candidate = holeId then some image else σ candidate

/-- Declarative template instantiation.  This deliberately constructs the
whole result and is the simple source specification for the fused pass. -/
def instantiate (σ : Substitution Var Token) :
    Template Token Var → Option (Formula Token)
  | [] => some []
  | .literal token :: rest => do
      let tail ← instantiate σ rest
      pure (token :: tail)
  | .hole holeId :: rest => do
      let image ← σ holeId
      let tail ← instantiate σ rest
      pure (image ++ tail)

/-! ## A fused prefix consumer -/

/-- Consume a known literal prefix without constructing a concatenation. -/
def consumeLiteralPrefix [DecidableEq Token] :
    Formula Token → Formula Token → Option (Formula Token)
  | [], input => some input
  | _ :: _, [] => none
  | expected :: expectedRest, actual :: actualRest =>
      if expected = actual then
        consumeLiteralPrefix expectedRest actualRest
      else
        none

/-- The literal consumer succeeds with `rest` exactly when its input is the
prefix followed by `rest`. -/
theorem consumeLiteralPrefix_eq_some_iff [DecidableEq Token]
    (needle input rest : Formula Token) :
    consumeLiteralPrefix needle input = some rest ↔
      input = needle ++ rest := by
  induction needle generalizing input rest with
  | nil => simp [consumeLiteralPrefix]
  | cons expected expectedRest ih =>
      cases input with
      | nil => simp [consumeLiteralPrefix]
      | cons actual actualRest =>
          by_cases equal : expected = actual
          · subst actual
            simp [consumeLiteralPrefix, ih]
          · have reverse : actual ≠ expected := Ne.symm equal
            simp [consumeLiteralPrefix, equal, reverse]

/-- Consume a template and an input together.  Hole images are traversed
directly; no instantiated template is allocated. -/
def consumeTemplate [DecidableEq Token]
    (σ : Substitution Var Token) :
    Template Token Var → Formula Token → Option (Formula Token)
  | [], input => some input
  | .literal expected :: rest, input =>
      match input with
      | [] => none
      | actual :: actualRest =>
          if expected = actual then
            consumeTemplate σ rest actualRest
          else
            none
  | .hole holeId :: rest, input =>
      match σ holeId with
      | none => none
      | some image =>
          match consumeLiteralPrefix image input with
          | none => none
          | some remaining => consumeTemplate σ rest remaining

/-- Soundness of the fused traversal with respect to materialized
instantiation. -/
theorem consumeTemplate_sound [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input rest : Formula Token)
    (accepted : consumeTemplate σ template input = some rest) :
    ∃ instantiated,
      instantiate σ template = some instantiated ∧
      input = instantiated ++ rest := by
  induction template generalizing input rest with
  | nil =>
      simp [consumeTemplate, instantiate] at accepted ⊢
      exact accepted
  | cons atom template ih =>
      cases atom with
      | literal expected =>
          cases input with
          | nil => simp [consumeTemplate] at accepted
          | cons actual actualRest =>
              by_cases equal : expected = actual
              · subst actual
                simp only [consumeTemplate] at accepted
                obtain ⟨tail, instantiated, inputEq⟩ :=
                  ih actualRest rest accepted
                refine ⟨expected :: tail, ?_, ?_⟩
                · simp [instantiate, instantiated]
                · simp [inputEq]
              · simp [consumeTemplate, equal] at accepted
      | hole holeId =>
          cases imageEq : σ holeId with
          | none => simp [consumeTemplate, imageEq] at accepted
          | some image =>
              cases prefixEq : consumeLiteralPrefix image input with
              | none => simp [consumeTemplate, imageEq, prefixEq] at accepted
              | some remaining =>
                  simp only [consumeTemplate, imageEq, prefixEq] at accepted
                  obtain ⟨tail, instantiated, remainingEq⟩ :=
                    ih remaining rest accepted
                  have inputEq : input = image ++ remaining :=
                    (consumeLiteralPrefix_eq_some_iff image input remaining).mp
                      prefixEq
                  refine ⟨image ++ tail, ?_, ?_⟩
                  · simp [instantiate, imageEq, instantiated]
                  · rw [inputEq, remainingEq, List.append_assoc]

/-- Completeness of the fused traversal with respect to materialized
instantiation. -/
theorem consumeTemplate_complete [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input rest instantiated : Formula Token)
    (instantiatedEq : instantiate σ template = some instantiated)
    (inputEq : input = instantiated ++ rest) :
    consumeTemplate σ template input = some rest := by
  induction template generalizing input rest instantiated with
  | nil =>
      simp [instantiate] at instantiatedEq
      subst instantiated
      simpa [consumeTemplate] using inputEq
  | cons atom template ih =>
      cases atom with
      | literal expected =>
          simp only [instantiate, Option.bind_eq_bind] at instantiatedEq
          cases tailEq : instantiate σ template with
          | none => simp [tailEq] at instantiatedEq
          | some tail =>
              simp [tailEq] at instantiatedEq
              subst instantiated
              subst input
              simpa [consumeTemplate] using
                (ih (tail ++ rest) rest tail tailEq rfl)
      | hole holeId =>
          cases imageEq : σ holeId with
          | none => simp [instantiate, imageEq] at instantiatedEq
          | some image =>
              cases tailEq : instantiate σ template with
              | none => simp [instantiate, imageEq, tailEq] at instantiatedEq
              | some tail =>
                  simp [instantiate, imageEq, tailEq] at instantiatedEq
                  subst instantiated
                  subst input
                  have prefixAccepted :
                      consumeLiteralPrefix image (image ++ tail ++ rest) =
                        some (tail ++ rest) :=
                    (consumeLiteralPrefix_eq_some_iff
                      image (image ++ tail ++ rest) (tail ++ rest)).mpr
                        (by simp [List.append_assoc])
                  simp only [consumeTemplate, imageEq, prefixAccepted]
                  exact ih (tail ++ rest) rest tail tailEq rfl

/-- Complete characterization of the fused traversal. -/
theorem consumeTemplate_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input rest : Formula Token) :
    consumeTemplate σ template input = some rest ↔
      ∃ instantiated,
        instantiate σ template = some instantiated ∧
        input = instantiated ++ rest := by
  constructor
  · exact consumeTemplate_sound σ template input rest
  · rintro ⟨instantiated, instantiatedEq, inputEq⟩
    exact consumeTemplate_complete
      σ template input rest instantiated instantiatedEq inputEq

/-! ## Exact matching: source and optimized realizations -/

/-- Source matcher: instantiate first, then compare. -/
def materializedMatch [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) : Option Unit :=
  match instantiate σ template with
  | none => none
  | some expected => if expected = input then some () else none

/-- Compiled matcher: consume template and input in one pass. -/
def fusedMatch [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) : Option Unit :=
  match consumeTemplate σ template input with
  | some [] => some ()
  | _ => none

theorem materializedMatch_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    materializedMatch σ template input = some () ↔
      instantiate σ template = some input := by
  unfold materializedMatch
  cases instantiatedEq : instantiate σ template with
  | none => simp
  | some expected =>
      by_cases equal : expected = input
      · subst input
        simp
      · simp [equal]

theorem fusedMatch_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    fusedMatch σ template input = some () ↔
      instantiate σ template = some input := by
  constructor
  · intro accepted
    unfold fusedMatch at accepted
    cases consumedEq : consumeTemplate σ template input with
    | none => simp [consumedEq] at accepted
    | some remaining =>
        cases remaining with
        | nil =>
            have characterized :=
              (consumeTemplate_eq_some_iff σ template input []).mp consumedEq
            obtain ⟨instantiated, instantiatedEq, inputEq⟩ := characterized
            have equal : input = instantiated := by simpa using inputEq
            rw [equal]
            exact instantiatedEq
        | cons token tail => simp [consumedEq] at accepted
  · intro instantiatedEq
    have consumedEq : consumeTemplate σ template input = some [] :=
      consumeTemplate_complete σ template input [] input
        instantiatedEq (by simp)
    simp [fusedMatch, consumedEq]

/-- The allocation-free match is observationally identical to the source
instantiate-then-compare implementation. -/
theorem fusedMatch_eq_materializedMatch [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    fusedMatch σ template input = materializedMatch σ template input := by
  cases sourceEq : materializedMatch σ template input with
  | none =>
      cases compiledEq : fusedMatch σ template input with
      | none => rfl
      | some value =>
          cases value
          have sourceAccepted : materializedMatch σ template input = some () :=
            (materializedMatch_eq_some_iff σ template input).mpr
              ((fusedMatch_eq_some_iff σ template input).mp compiledEq)
          rw [sourceEq] at sourceAccepted
          contradiction
  | some value =>
      cases value
      have compiledAccepted : fusedMatch σ template input = some () :=
        (fusedMatch_eq_some_iff σ template input).mpr
          ((materializedMatch_eq_some_iff σ template input).mp sourceEq)
      exact compiledAccepted

/-! ## Ordered frames and their admission procedure -/

/-- A binder hypothesis is recognized by native-type information as a typed
hole.  The runtime uses only these two generated fields. -/
structure Binder (Token : Type u) (Var : Type v) where
  head : Token
  holeId : Var
deriving DecidableEq, Repr

/-- The two hypothesis roles needed by the first-order frame machine. -/
inductive Hypothesis (Token : Type u) (Var : Type v) where
  | binder (specification : Binder Token Var)
  | matching (template : Template Token Var)
deriving DecidableEq, Repr

/-- Authored source frame. -/
structure SourceFrame (Token : Type u) (Var : Type v) where
  hypotheses : List (Hypothesis Token Var)
  conclusion : Template Token Var
deriving DecidableEq, Repr

/-- Admitted machine frame.  Its layout makes the scheduling fact explicit:
the binder prefix is executed first and the remaining hypotheses are exact
matches. -/
structure CompiledFrame (Token : Type u) (Var : Type v) where
  binders : List (Binder Token Var)
  patterns : List (Template Token Var)
  conclusion : Template Token Var
deriving DecidableEq, Repr

/-- Once the first matching hypothesis is seen, only matches may follow. -/
def collectMatches :
    List (Hypothesis Token Var) → Option (List (Template Token Var))
  | [] => some []
  | .matching template :: rest => do
      let tail ← collectMatches rest
      pure (template :: tail)
  | .binder _ :: _ => none

/-- Decide the sufficient one-pass scheduling criterion.  Acceptance means
that the source frame has a binder prefix followed by a matching suffix. -/
def compileHypotheses :
    List (Hypothesis Token Var) →
      Option (List (Binder Token Var) × List (Template Token Var))
  | [] => some ([], [])
  | .binder specification :: rest => do
      let (binders, patterns) ← compileHypotheses rest
      pure (specification :: binders, patterns)
  | .matching template :: rest => do
      let patterns ← collectMatches rest
      pure ([], template :: patterns)

def compileFrame (source : SourceFrame Token Var) :
    Option (CompiledFrame Token Var) := do
  let (binders, patterns) ← compileHypotheses source.hypotheses
  pure { binders, patterns, conclusion := source.conclusion }

/-- Successful suffix collection exactly reconstructs the source suffix. -/
theorem collectMatches_sound
    (hypotheses : List (Hypothesis Token Var))
    (patterns : List (Template Token Var))
    (accepted : collectMatches hypotheses = some patterns) :
    hypotheses = patterns.map Hypothesis.matching := by
  induction hypotheses generalizing patterns with
  | nil =>
      simp [collectMatches] at accepted
      subst patterns
      rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | binder specification => simp [collectMatches] at accepted
      | matching template =>
          simp only [collectMatches] at accepted
          cases tailEq : collectMatches hypotheses with
          | none => simp [tailEq] at accepted
          | some tail =>
              simp [tailEq] at accepted
              subst patterns
              simp [ih tail tailEq]

/-- Every all-matching suffix is accepted and returned without reordering. -/
theorem collectMatches_complete
    (patterns : List (Template Token Var)) :
    collectMatches (patterns.map Hypothesis.matching) = some patterns := by
  induction patterns with
  | nil => rfl
  | cons template patterns ih =>
      simp [collectMatches, ih]

/-- Successful admission produces an exact binder-prefix/matching-suffix
decomposition of the authored hypotheses. -/
theorem compileHypotheses_sound
    (hypotheses : List (Hypothesis Token Var))
    (binders : List (Binder Token Var))
    (patterns : List (Template Token Var))
    (accepted : compileHypotheses hypotheses = some (binders, patterns)) :
    hypotheses =
      binders.map Hypothesis.binder ++ patterns.map Hypothesis.matching := by
  induction hypotheses generalizing binders patterns with
  | nil =>
      simp [compileHypotheses] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | binder specification =>
          simp only [compileHypotheses] at accepted
          cases tailEq : compileHypotheses hypotheses with
          | none => simp [tailEq] at accepted
          | some tail =>
              obtain ⟨tailBinders, tailMatches⟩ := tail
              simp [tailEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              simp [ih tailBinders tailMatches tailEq]
      | matching template =>
          simp only [compileHypotheses] at accepted
          cases suffixEq : collectMatches hypotheses with
          | none => simp [suffixEq] at accepted
          | some suffix =>
              simp [suffixEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              simp [collectMatches_sound hypotheses suffix suffixEq]

/-- Every binder-prefix/matching-suffix schedule is accepted and compiled to
that exact layout. -/
theorem compileHypotheses_complete
    (binders : List (Binder Token Var))
    (patterns : List (Template Token Var)) :
    compileHypotheses
        (binders.map Hypothesis.binder ++
          patterns.map Hypothesis.matching) =
      some (binders, patterns) := by
  induction binders with
  | nil =>
      cases patterns with
      | nil => rfl
      | cons template patterns =>
          simp [compileHypotheses, collectMatches_complete]
  | cons specification binders ih =>
      simp [compileHypotheses, ih]

/-- Exact characterization of the decidable one-pass scheduling fragment. -/
theorem compileHypotheses_accepts_iff
    (hypotheses : List (Hypothesis Token Var)) :
    (∃ (binders : List (Binder Token Var))
        (patterns : List (Template Token Var)),
        compileHypotheses hypotheses = some (binders, patterns)) ↔
      ∃ (binders : List (Binder Token Var))
          (patterns : List (Template Token Var)),
        hypotheses =
          binders.map Hypothesis.binder ++
            patterns.map Hypothesis.matching := by
  constructor
  · rintro ⟨binders, patterns, accepted⟩
    exact ⟨binders, patterns,
      compileHypotheses_sound hypotheses binders patterns accepted⟩
  · rintro ⟨binders, patterns, rfl⟩
    exact ⟨binders, patterns,
      compileHypotheses_complete binders patterns⟩

theorem compileFrame_sound
    (source : SourceFrame Token Var) (compiled : CompiledFrame Token Var)
    (accepted : compileFrame source = some compiled) :
    source.hypotheses =
        compiled.binders.map Hypothesis.binder ++
          compiled.patterns.map Hypothesis.matching ∧
      compiled.conclusion = source.conclusion := by
  unfold compileFrame at accepted
  cases splitEq : compileHypotheses source.hypotheses with
  | none => simp [splitEq] at accepted
  | some split =>
      obtain ⟨binders, patterns⟩ := split
      simp [splitEq] at accepted
      subst compiled
      exact ⟨compileHypotheses_sound
        source.hypotheses binders patterns splitEq, rfl⟩

/-- A frame is admitted exactly when its generated hypothesis roles form a
binder prefix followed by a matching suffix. -/
theorem compileFrame_accepts_iff (source : SourceFrame Token Var) :
    (∃ compiled, compileFrame source = some compiled) ↔
      ∃ (binders : List (Binder Token Var))
          (patterns : List (Template Token Var)),
        source.hypotheses =
          binders.map Hypothesis.binder ++
            patterns.map Hypothesis.matching := by
  rw [← compileHypotheses_accepts_iff source.hypotheses]
  constructor
  · rintro ⟨compiled, accepted⟩
    unfold compileFrame at accepted
    cases splitEq : compileHypotheses source.hypotheses with
    | none => simp [splitEq] at accepted
    | some split =>
        obtain ⟨binders, patterns⟩ := split
        exact ⟨binders, patterns, rfl⟩
  · rintro ⟨binders, patterns, accepted⟩
    refine ⟨
      { binders := binders
        patterns := patterns
        conclusion := source.conclusion }, ?_⟩
    simp [compileFrame, accepted]

/-! ## Source and compiled frame interpreters -/

/-- Extend an environment from one typed stack entry.  Repeated binders are
accepted only when they induce the same image, so this operation is useful
even before a stronger unique-binder layout certificate is available. -/
def bindOne [DecidableEq Token] [DecidableEq Var]
    (σ : Substitution Var Token) (specification : Binder Token Var)
    (input : Formula Token) : Option (Substitution Var Token) :=
  match input with
  | [] => none
  | head :: image =>
      if head = specification.head then
        match σ specification.holeId with
        | none => some (insertSubstitution σ specification.holeId image)
        | some previous => if previous = image then some σ else none
      else
        none

/-- Execute the binder prefix, returning the unconsumed stack suffix. -/
def runBinders [DecidableEq Token] [DecidableEq Var] :
    List (Binder Token Var) → List (Formula Token) →
      Substitution Var Token →
      Option (List (Formula Token) × Substitution Var Token)
  | [], stack, σ => some (stack, σ)
  | _ :: _, [], _ => none
  | specification :: binders, input :: stack, σ => do
      let next ← bindOne σ specification input
      runBinders binders stack next

def runMaterializedMatches [DecidableEq Token]
    (σ : Substitution Var Token) :
    List (Template Token Var) → List (Formula Token) → Option Unit
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | template :: templates, input :: stack => do
      let _ ← materializedMatch σ template input
      runMaterializedMatches σ templates stack

def runFusedMatches [DecidableEq Token]
    (σ : Substitution Var Token) :
    List (Template Token Var) → List (Formula Token) → Option Unit
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | template :: templates, input :: stack => do
      let _ ← fusedMatch σ template input
      runFusedMatches σ templates stack

/-- Fusing every match in a frame preserves the whole suffix-check result. -/
theorem runFusedMatches_eq_runMaterializedMatches [DecidableEq Token]
    (σ : Substitution Var Token) (templates : List (Template Token Var))
    (stack : List (Formula Token)) :
    runFusedMatches σ templates stack =
      runMaterializedMatches σ templates stack := by
  induction templates generalizing stack with
  | nil => cases stack <;> rfl
  | cons template templates ih =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          simp only [runFusedMatches, runMaterializedMatches]
          rw [fusedMatch_eq_materializedMatch]
          cases materializedMatch σ template input <;> simp [ih]

/-- Independent source interpreter over the authored hypothesis sequence. -/
def runSourceHypotheses [DecidableEq Token] [DecidableEq Var] :
    List (Hypothesis Token Var) → List (Formula Token) →
      Substitution Var Token → Option (Substitution Var Token)
  | [], [], σ => some σ
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | .binder specification :: hypotheses, input :: stack, σ => do
      let next ← bindOne σ specification input
      runSourceHypotheses hypotheses stack next
  | .matching template :: hypotheses, input :: stack, σ => do
      let _ ← materializedMatch σ template input
      runSourceHypotheses hypotheses stack σ

def runSourceFrame [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var) (stack : List (Formula Token)) :
    Option (Formula Token) := do
  let σ ← runSourceHypotheses
    source.hypotheses stack emptySubstitution
  instantiate σ source.conclusion

def runCompiledFrame [DecidableEq Token] [DecidableEq Var]
    (compiled : CompiledFrame Token Var) (stack : List (Formula Token)) :
    Option (Formula Token) := do
  let (remaining, σ) ← runBinders
    compiled.binders stack emptySubstitution
  let _ ← runFusedMatches σ compiled.patterns remaining
  instantiate σ compiled.conclusion

theorem runSourceHypotheses_binders_append
    [DecidableEq Token] [DecidableEq Var]
    (binders : List (Binder Token Var))
    (tail : List (Hypothesis Token Var))
    (stack : List (Formula Token)) (σ : Substitution Var Token) :
    runSourceHypotheses
        (binders.map Hypothesis.binder ++ tail) stack σ =
      (do
        let (remaining, next) ← runBinders binders stack σ
        runSourceHypotheses tail remaining next) := by
  induction binders generalizing stack σ with
  | nil => simp [runBinders]
  | cons specification binders ih =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          simp only [List.map_cons, List.cons_append,
            runSourceHypotheses, runBinders]
          cases bindOne σ specification input <;> simp [ih]

theorem runSourceHypotheses_matches
    [DecidableEq Token] [DecidableEq Var]
    (templates : List (Template Token Var))
    (stack : List (Formula Token)) (σ : Substitution Var Token) :
    runSourceHypotheses (templates.map Hypothesis.matching) stack σ =
      (do
        let _ ← runMaterializedMatches σ templates stack
        pure σ) := by
  induction templates generalizing stack with
  | nil => cases stack <;> rfl
  | cons template templates ih =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          simp only [List.map_cons, runSourceHypotheses,
            runMaterializedMatches]
          cases materializedMatch σ template input <;> simp [ih]

/-- Main refinement theorem.  Whenever the generic admission procedure
accepts a frame, the ordered one-pass machine has exactly the independent
source interpreter's result for every stack. -/
theorem runCompiledFrame_eq_runSourceFrame
    [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var) (compiled : CompiledFrame Token Var)
    (accepted : compileFrame source = some compiled)
    (stack : List (Formula Token)) :
    runCompiledFrame compiled stack = runSourceFrame source stack := by
  obtain ⟨hypothesesEq, conclusionEq⟩ :=
    compileFrame_sound source compiled accepted
  unfold runCompiledFrame runSourceFrame
  rw [hypothesesEq, runSourceHypotheses_binders_append]
  cases bindersEq : runBinders
      compiled.binders stack emptySubstitution with
  | none => simp
  | some result =>
      obtain ⟨remaining, σ⟩ := result
      simp
      rw [runSourceHypotheses_matches, conclusionEq,
        runFusedMatches_eq_runMaterializedMatches]
      cases runMaterializedMatches σ compiled.patterns remaining <;> rfl

/-! ## Certified-realization packaging -/

/-- An admitted frame carries the exact output of the decidable scheduling
compiler together with its acceptance equation. -/
structure AdmittedFrame (Token : Type u) (Var : Type v) where
  source : SourceFrame Token Var
  compiled : CompiledFrame Token Var
  certificate : compileFrame source = some compiled

/-- Turn the partial admission decision into an explicit certified source
object. -/
def admitFrame (source : SourceFrame Token Var) :
    Option (AdmittedFrame Token Var) :=
  match accepted : compileFrame source with
  | none => none
  | some compiled => some { source, compiled, certificate := accepted }

/-- The ordered-frame compiler is a certified realization whose observation
is the entire partial stack transformer, not merely an acceptance bit. -/
def orderedFrameRealization [DecidableEq Token] [DecidableEq Var] :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedFrame Token Var) (CompiledFrame Token Var)
      (List (Formula Token) → Option (Formula Token)) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted => runSourceFrame admitted.source
  observeArtifact := fun _ compiled => runCompiledFrame compiled
  adequate := by
    intro _ admitted
    funext stack
    exact runCompiledFrame_eq_runSourceFrame
      admitted.source admitted.compiled admitted.certificate stack

/-! ## Certified frame caches -/

/-- A persistent table of admitted rules indexed by an arbitrary generated key
type.  Rejected source frames cannot enter this compiled-store boundary. -/
abbrev FrameStore (Key : Type*) (Token : Type u) (Var : Type v) :=
  Key → Option (AdmittedFrame Token Var)

/-- A cache is certified against one admitted-store snapshot.  Exactness
requires every cached artifact to be the artifact carried by its admitted
source entry. -/
structure CertifiedFrameCache (Key : Type*) (Token : Type u) (Var : Type v)
    (sourceStore : FrameStore Key Token Var) where
  lookup : Key → Option (CompiledFrame Token Var)
  exact : ∀ key, lookup key = (sourceStore key).map (fun entry => entry.compiled)

/-- Build the canonical exact cache for a source-store snapshot. -/
def buildFrameCache (sourceStore : FrameStore Key Token Var) :
    CertifiedFrameCache Key Token Var sourceStore where
  lookup := fun key => (sourceStore key).map (fun entry => entry.compiled)
  exact := fun _ => rfl

/-- Interpret one keyed source frame. -/
def runSourceAt [DecidableEq Token] [DecidableEq Var]
    (sourceStore : FrameStore Key Token Var) (key : Key)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let entry ← sourceStore key
  runSourceFrame entry.source stack

/-- Execute one keyed compiled frame from a certified cache. -/
def runCachedAt [DecidableEq Token] [DecidableEq Var]
    {sourceStore : FrameStore Key Token Var}
    (cache : CertifiedFrameCache Key Token Var sourceStore) (key : Key)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let compiled ← cache.lookup key
  runCompiledFrame compiled stack

/-- Compiling every admitted persistent frame once and looking it up thereafter
preserves the complete partial stack-transformer observation. -/
theorem runCachedAt_eq_runSourceAt
    [DecidableEq Token] [DecidableEq Var]
    (sourceStore : FrameStore Key Token Var)
    (cache : CertifiedFrameCache Key Token Var sourceStore)
    (key : Key) (stack : List (Formula Token)) :
    runCachedAt cache key stack = runSourceAt sourceStore key stack := by
  unfold runCachedAt runSourceAt
  rw [cache.exact key]
  cases sourceStore key with
  | none => simp
  | some entry =>
      simp only [Option.map]
      exact runCompiledFrame_eq_runSourceFrame
        entry.source entry.compiled entry.certificate stack

/-- A cache compiled from an earlier store snapshot remains valid for a key
exactly when that key's source frame is preserved by the update.  No property
of the key or guest language is used. -/
theorem runCachedAt_eq_runSourceAt_of_entry_persistent
    [DecidableEq Token] [DecidableEq Var]
    (before after : FrameStore Key Token Var)
    (cache : CertifiedFrameCache Key Token Var before)
    (key : Key) (stack : List (Formula Token))
    (persistent : before key = after key) :
    runCachedAt cache key stack = runSourceAt after key stack := by
  have exactBefore := runCachedAt_eq_runSourceAt before cache key stack
  have sourceRunPersistent :
      runSourceAt before key stack = runSourceAt after key stack := by
    unfold runSourceAt
    rw [persistent]
  exact exactBefore.trans sourceRunPersistent

/-- The backend representation emitted for an admitted frame table. -/
abbrev FrameCacheArtifact (Key : Type*) (Token : Type u) (Var : Type v) :=
  Key → Option (CompiledFrame Token Var)

/-- Execute a raw compiled-cache artifact. -/
def runFrameCacheArtifactAt [DecidableEq Token] [DecidableEq Var]
    (artifact : FrameCacheArtifact Key Token Var) (key : Key)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let compiled ← artifact key
  runCompiledFrame compiled stack

/-- Whole-table certified realization.  This packages compile-once frame
memoization as a normal composable lowering pass, observing every keyed stack
transformer rather than one selected example. -/
def frameCacheRealization [DecidableEq Token] [DecidableEq Var] :
    Mettapedia.GSLT.SimpleRealization
      (FrameStore Key Token Var)
      (FrameCacheArtifact Key Token Var)
      (Key → List (Formula Token) → Option (Formula Token)) where
  compile := fun _ sourceStore key =>
    (sourceStore key).map (fun entry => entry.compiled)
  observeSource := fun _ sourceStore key stack =>
    runSourceAt sourceStore key stack
  observeArtifact := fun _ artifact key stack =>
    runFrameCacheArtifactAt artifact key stack
  adequate := by
    intro _ sourceStore
    funext key stack
    unfold runFrameCacheArtifactAt runSourceAt
    cases sourceEq : sourceStore key with
    | none => simp [sourceEq]
    | some entry =>
        simpa [sourceEq] using
          (runCompiledFrame_eq_runSourceFrame
            entry.source entry.compiled entry.certificate stack)

/-! ## Non-vacuity canaries -/

private def canarySource : SourceFrame Nat Nat where
  hypotheses :=
    [ .binder { head := 10, holeId := 0 }
    , .matching [.literal 20, .hole 0] ]
  conclusion := [.literal 30, .hole 0]

private def canaryCompiled : CompiledFrame Nat Nat where
  binders := [{ head := 10, holeId := 0 }]
  patterns := [[.literal 20, .hole 0]]
  conclusion := [.literal 30, .hole 0]

private def canaryAdmitted : AdmittedFrame Nat Nat where
  source := canarySource
  compiled := canaryCompiled
  certificate := rfl

/-- Positive witness: the admitted one-pass machine performs a real
substitution and returns the instantiated conclusion. -/
example :
    compileFrame canarySource = some canaryCompiled ∧
      runCompiledFrame canaryCompiled [[10, 7, 8], [20, 7, 8]] =
        some [30, 7, 8] := by
  decide

/-- Negative witness: an essential hypothesis before a binder is outside the
admitted scheduling fragment. -/
example :
    compileFrame
      { hypotheses :=
          [ Hypothesis.matching [.literal 20, .hole 0]
          , Hypothesis.binder { head := 10, holeId := 0 } ]
        conclusion := [.hole 0] } = none := by
  decide

/-- Negative witness: an admitted frame still rejects a mismatching stack. -/
example :
    runCompiledFrame canaryCompiled [[10, 7, 8], [20, 7, 9]] = none := by
  decide

private def canaryStoreBefore : FrameStore Nat Nat Nat
  | 0 => some canaryAdmitted
  | _ => none

private def canaryStoreUnrelatedUpdate : FrameStore Nat Nat Nat
  | 0 => some canaryAdmitted
  | 1 => some
      { source :=
          { hypotheses := []
            conclusion := [.literal 99] }
        compiled :=
          { binders := []
            patterns := []
            conclusion := [.literal 99] }
        certificate := rfl }
  | _ => none

private def canaryChangedSource : SourceFrame Nat Nat where
  hypotheses := canarySource.hypotheses
  conclusion := [.literal 31, .hole 0]

private def canaryChangedCompiled : CompiledFrame Nat Nat where
  binders := canaryCompiled.binders
  patterns := canaryCompiled.patterns
  conclusion := [.literal 31, .hole 0]

private def canaryChangedAdmitted : AdmittedFrame Nat Nat where
  source := canaryChangedSource
  compiled := canaryChangedCompiled
  certificate := rfl

private def canaryStoreChangedEntry : FrameStore Nat Nat Nat
  | 0 => some canaryChangedAdmitted
  | _ => none

private def canaryCache :
    CertifiedFrameCache Nat Nat Nat canaryStoreBefore :=
  buildFrameCache canaryStoreBefore

/-- Positive cache witness: changing an unrelated source entry preserves the
cached frame's source observation. -/
example :
    runCachedAt canaryCache 0 [[10, 7, 8], [20, 7, 8]] =
      runSourceAt canaryStoreUnrelatedUpdate 0
        [[10, 7, 8], [20, 7, 8]] := by
  apply runCachedAt_eq_runSourceAt_of_entry_persistent
  rfl

/-- Negative cache witness: reusing a cache after its source entry changes is
observably unsound, so the persistence premise is load-bearing. -/
example :
    runCachedAt canaryCache 0 [[10, 7, 8], [20, 7, 8]] ≠
      runSourceAt canaryStoreChangedEntry 0
        [[10, 7, 8], [20, 7, 8]] := by
  decide

end Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation
