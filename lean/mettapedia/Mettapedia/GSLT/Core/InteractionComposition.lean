import Mettapedia.GSLT.Core.InteractionEvent

/-!
# Composition of proof-relevant interaction events

An interaction presentation gives the authenticated one-step occurrences of a
GSLT.  This module derives paths, normalization, and continuation composition
without enlarging that one-step relation.

The central construction is normalizing bind: follow authenticated events to
a semantic normal form, then enter an authored continuation.  Ordinary
execution is bind with the identity continuation.  One-step inspection is the
already existing enabled-event family.  Thus execution and inspection need no
second source of semantic steps.
-/

namespace Mettapedia.GSLT.Core.InteractionComposition

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation

universe uSite uEvent uResult uFirst uSecond uThird uA uB uC uD

variable {theory : GSLT}
  (presentation : InteractionPresentation.{uSite, uEvent} theory)

/-- A finite path retaining the exact interaction event at every edge. -/
inductive EventPath : theory.Term → theory.Term → Type _ where
  | nil (term : theory.Term) : EventPath term term
  | cons {source middle target : theory.Term} {site : presentation.Site}
      (event : presentation.Event site source middle)
      (rest : EventPath middle target) : EventPath source target

namespace EventPath

/-- Length of an occurrence-preserving event path. -/
def pathLength : {source target : theory.Term} →
    EventPath presentation source target → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => 1 + pathLength rest

/-- Chaining is composition of occurrence-preserving paths, derived from the
one-step presentation rather than added to its event family. -/
def append {source middle target : theory.Term} :
    EventPath presentation source middle →
      EventPath presentation middle target →
      EventPath presentation source target
  | .nil _, suffix => suffix
  | .cons event rest, suffix => .cons event (append rest suffix)

@[simp] theorem nil_append {source target : theory.Term}
    (path : EventPath presentation source target) :
    append presentation (.nil source) path = path :=
  rfl

@[simp] theorem append_nil {source target : theory.Term}
    (path : EventPath presentation source target) :
    append presentation path (.nil target) = path := by
  induction path with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [append]
      rw [inductionHypothesis]

@[simp] theorem append_assoc {first second third fourth : theory.Term}
    (left : EventPath presentation first second)
    (middle : EventPath presentation second third)
    (right : EventPath presentation third fourth) :
    append presentation (append presentation left middle) right =
      append presentation left (append presentation middle right) := by
  induction left with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [append]
      rw [inductionHypothesis]

@[simp] theorem pathLength_append {source middle target : theory.Term}
    (prefixPath : EventPath presentation source middle)
    (suffix : EventPath presentation middle target) :
    pathLength presentation (append presentation prefixPath suffix) =
      pathLength presentation prefixPath + pathLength presentation suffix := by
  induction prefixPath with
  | nil => simp [append, pathLength]
  | cons event rest inductionHypothesis =>
      simp [append, pathLength, inductionHypothesis, Nat.add_assoc]

/-- Forget event identity while retaining the authorized GSLT rewrite path. -/
def erase : {source target : theory.Term} →
    EventPath presentation source target → theory.RewritePath source target
  | _, _, .nil term => .nil term
  | _, _, .cons event rest =>
      .cons (presentation.sound event) (erase rest)

/-- Event paths and their endpoint erasures have the same length. -/
@[simp] theorem erase_length {source target : theory.Term}
    (path : EventPath presentation source target) :
    path.erase.length = pathLength presentation path := by
  induction path with
  | nil => rfl
  | cons _ rest inductionHypothesis =>
      simp only [erase, pathLength, GSLT.RewritePath.length]
      exact congrArg (fun length => 1 + length) inductionHypothesis

/-- A complete presentation lifts every endpoint rewrite path to at least one
occurrence-preserving event path. -/
theorem nonempty_of_rewritePath
    (complete : presentation.Complete) :
    {source target : theory.Term} → theory.RewritePath source target →
      Nonempty (EventPath presentation source target)
  | _, _, .nil term => ⟨.nil term⟩
  | _, _, .cons step rest => by
      obtain ⟨⟨site, event⟩⟩ := complete step
      obtain ⟨eventRest⟩ := nonempty_of_rewritePath complete rest
      exact ⟨.cons (site := site) event eventRest⟩

end EventPath

/-- Proof-relevant evaluation to a semantic normal form. -/
structure EventNormalizes (source target : theory.Term) where
  path : EventPath presentation source target
  normal : theory.IsNormalForm target

namespace EventNormalizes

/-- Endpoint-only normalization obtained by erasing event occurrences. -/
structure Endpoint (source target : theory.Term) where
  path : theory.RewritePath source target
  normal : theory.IsNormalForm target

/-- Erase an occurrence-preserving normalization article. -/
def erase {source target : theory.Term}
    (normalization : EventNormalizes presentation source target) :
    Endpoint (theory := theory) source target where
  path := normalization.path.erase
  normal := normalization.normal

/-- Completeness lifts every endpoint normalization to at least one article
retaining the exact event at every edge. -/
theorem nonempty_of_endpoint
    (complete : presentation.Complete) {source target : theory.Term}
    (normalization : Endpoint (theory := theory) source target) :
    Nonempty (EventNormalizes presentation source target) := by
  obtain ⟨path⟩ := EventPath.nonempty_of_rewritePath presentation complete
    normalization.path
  exact ⟨⟨path, normalization.normal⟩⟩

/-- A term already in normal form has the empty normalization article. -/
def refl {term : theory.Term} (normal : theory.IsNormalForm term) :
    EventNormalizes presentation term term where
  path := .nil term
  normal := normal

end EventNormalizes

/-! ## Proof-relevant relational composition -/

/-- Composition of proof-relevant relations.  The intermediate value and both
pieces of evidence remain available. -/
def Then {A : Type uA} {B : Type uB} {C : Type uC}
    (first : A → B → Type uFirst) (second : B → C → Type uSecond)
    (source : A) (target : C) : Type _ :=
  Σ middle, first source middle × second middle target

/-- Relational composition is associative by evidence-preserving
reassociation, not by erasing the intermediate witnesses. -/
def thenAssoc {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    (first : A → B → Type uFirst) (second : B → C → Type uSecond)
    (third : C → D → Type uThird) (source : A) (target : D) :
    Then (Then first second) third source target ≃
      Then first (Then second third) source target where
  toFun
    | ⟨secondMiddle, ⟨firstMiddle, firstEvidence, secondEvidence⟩,
        thirdEvidence⟩ =>
      ⟨firstMiddle, firstEvidence,
        ⟨secondMiddle, secondEvidence, thirdEvidence⟩⟩
  invFun
    | ⟨firstMiddle, firstEvidence,
        ⟨secondMiddle, secondEvidence, thirdEvidence⟩⟩ =>
      ⟨secondMiddle,
        ⟨firstMiddle, firstEvidence, secondEvidence⟩, thirdEvidence⟩
  left_inv := by intro evidence; cases evidence with | mk _ rest => cases rest; rfl
  right_inv := by intro evidence; cases evidence with | mk _ rest => cases rest; rfl

/-- Identity continuation. -/
def Return {A : Type uA} (source target : A) : Type := PLift (source = target)

/-- Right identity for proof-relevant relational composition. -/
def thenReturnRight {A : Type uA} {B : Type uB}
    (relation : A → B → Type uFirst) (source : A) (target : B) :
    Then relation Return source target ≃ relation source target where
  toFun
    | ⟨middle, evidence, ⟨equal⟩⟩ => equal ▸ evidence
  invFun evidence := ⟨target, evidence, ⟨rfl⟩⟩
  left_inv := by
    intro composed
    obtain ⟨middle, evidence, ⟨equal⟩⟩ := composed
    cases equal
    rfl
  right_inv := by intro evidence; rfl

/-- Left identity for proof-relevant relational composition. -/
def thenReturnLeft {A : Type uA} {B : Type uB}
    (relation : A → B → Type uFirst) (source : A) (target : B) :
    Then Return relation source target ≃ relation source target where
  toFun
    | ⟨middle, ⟨equal⟩, evidence⟩ => equal.symm ▸ evidence
  invFun evidence := ⟨source, ⟨rfl⟩, evidence⟩
  left_inv := by
    intro composed
    obtain ⟨middle, ⟨equal⟩, evidence⟩ := composed
    cases equal
    rfl
  right_inv := by intro evidence; rfl

/-! ## The derived basis -/

/-- Normalizing bind: evaluate through authenticated events to a semantic
normal form, then enter the authored continuation.  This is the theoretical
meaning of a MeTTa-shaped `let`; it is not another primitive step relation. -/
def Bind {Result : Type uResult}
    (continuation : theory.Term → Result → Type uFirst)
    (source : theory.Term) (result : Result) :
    Type _ :=
  Then (EventNormalizes presentation) continuation source result

/-- Ordinary execution is normalizing bind with the identity continuation. -/
def Run (source result : theory.Term) : Type _ :=
  Bind presentation Return source result

/-- Running contains exactly the same evidence as normalization; `run` is
therefore derived rather than a second semantic operator. -/
def runEquivNormalizes (source result : theory.Term) :
    Run presentation source result ≃
      EventNormalizes presentation source result :=
  thenReturnRight (EventNormalizes presentation) source result

/-- One-step inspection is the enabled-event family already supplied by the
presentation.  It observes authority without adding a new step constructor. -/
abbrev Inspect (source : theory.Term) : Type _ :=
  presentation.Enabled source

/-! ## Positive and negative canaries -/

namespace Canary

def onceTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

inductive OnceSite where
  | advance

inductive OnceEvent : OnceSite → Bool → Bool → Type where
  | advance : OnceEvent .advance false true

def oncePresentation : InteractionPresentation onceTheory where
  Site := OnceSite
  Event := OnceEvent
  sound := by
    intro site source target event
    cases event
    exact ⟨rfl, rfl⟩

theorem true_normal : onceTheory.IsNormalForm true := by
  rintro ⟨target, step⟩
  exact Bool.noConfusion step.1

def advanceNormalization :
    EventNormalizes oncePresentation false true where
  path := .cons OnceEvent.advance
    (.nil (presentation := oncePresentation) true)
  normal := true_normal

structure Accepted (value : Bool) (result : String) : Type where
  valueIsTrue : value = true
  resultIsAccepted : result = "accepted"

/-- Positive: ordinary bind follows the authenticated edge and enters the
continuation only at the resulting normal form. -/
def acceptedBind :
    Bind oncePresentation Accepted false "accepted" :=
  ⟨true, advanceNormalization, ⟨rfl, rfl⟩⟩

/-- Negative: the reducible source cannot be returned as a completed value. -/
theorem false_does_not_normalize_to_itself :
    EventNormalizes oncePresentation false false → False := by
  intro normalization
  exact normalization.normal ⟨true, ⟨rfl, rfl⟩⟩

/-- Negative: a continuation with no constructor for a result cannot forge
that result. -/
theorem bind_cannot_forge_rejected :
    Bind oncePresentation Accepted false "rejected" → False := by
  rintro ⟨value, _normalization, continuation⟩
  have impossible := continuation.resultIsAccepted
  simp at impossible

end Canary

end Mettapedia.GSLT.Core.InteractionComposition
