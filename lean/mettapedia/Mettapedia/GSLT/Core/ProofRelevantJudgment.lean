import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.GSLT.Core.SemanticImplementation

/-!
# Proof-relevant judgments as operational GSLTs

A relation presented as an evidence family can itself be an operational
language.  A query steps to an answer exactly when its evidence fibre is
inhabited; the associated `StepEvidence` retains the particular inhabitant.

An exact change of evidence representation is therefore not an informal
intermediate representation.  It induces an exact proof-relevant GSLT
translation, an equation-class semantic cover after erasure, and an
equivalence of every fixed query/answer evidence fibre.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofRelevantJudgment

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ProofRelevant

universe u

/-- A proof-relevant binary judgment. -/
structure Judgment (Input Output : Type u) where
  Evidence : Input -> Output -> Type u

variable {Input Output : Type u}

/-- Operational terms expose a submitted query and an accepted answer. -/
inductive Term (judgment : Judgment Input Output) where
  | query (input : Input)
  | answer (input : Input) (output : Output)

namespace Term

/-- Change only the judgment that indexes an operational term. -/
def rebase {first : Judgment Input Output}
    (second : Judgment Input Output) : Term first -> Term second
  | .query input => .query input
  | .answer input output => .answer input output

/-- Rebasing between two evidence presentations is an equivalence of the
operational term carriers. -/
def rebaseEquiv (first second : Judgment Input Output) :
    Term first ≃ Term second where
  toFun := rebase second
  invFun := rebase first
  left_inv term := by cases term <;> rfl
  right_inv term := by cases term <;> rfl

end Term

/-- A one-step receipt is the exact evidence accepting one answer. -/
inductive TransitionEvidence (judgment : Judgment Input Output) :
    Term judgment -> Term judgment -> Type u where
  | accepted {input : Input} {output : Output}
      (evidence : judgment.Evidence input output) :
      TransitionEvidence judgment (.query input) (.answer input output)

namespace Judgment

/-- The extensional operational theory of a proof-relevant judgment. -/
def theory (judgment : Judgment Input Output) : GSLT where
  Term := Term judgment
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (TransitionEvidence judgment source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The proof-relevant receipts erase exactly to the judgment GSLT's steps. -/
def stepEvidence (judgment : Judgment Input Output) :
    StepEvidence judgment.theory where
  Evidence := TransitionEvidence judgment
  erases_iff := fun _ _ => Iff.rfl

/-- Bundle the extensional operational theory with its exact receipts. -/
def system (judgment : Judgment Input Output) : ProofRelevantGSLT :=
  ⟨judgment.theory, judgment.stepEvidence⟩

@[simp]
theorem query_step_answer_iff (judgment : Judgment Input Output)
    (input : Input) (output : Output) :
    judgment.theory.Step (.query input) (.answer input output) <->
      Nonempty (judgment.Evidence input output) := by
  change Nonempty (TransitionEvidence judgment (.query input)
      (.answer input output)) <-> Nonempty (judgment.Evidence input output)
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | accepted witness => exact ⟨witness⟩
  · rintro ⟨witness⟩
    exact ⟨.accepted witness⟩

/-- Submitted queries have no incoming query-to-query edge. -/
theorem not_query_step_query (judgment : Judgment Input Output)
    (first second : Input) :
    Not (judgment.theory.Step (.query first) (.query second)) := by
  rintro ⟨evidence⟩
  cases evidence

/-- Accepted answers are terminal. -/
theorem answer_isNormalForm (judgment : Judgment Input Output)
    (input : Input) (output : Output) :
    judgment.theory.IsNormalForm (.answer input output) := by
  rintro ⟨target, ⟨evidence⟩⟩
  cases evidence

end Judgment

/-! ## Exact changes of evidence presentation -/

/-- Two judgments have exactly the same fixed-endpoint evidence fibres. -/
structure ExactEquivalence (first second : Judgment Input Output) where
  evidenceEquiv : forall input output,
    first.Evidence input output ≃ second.Evidence input output

namespace ExactEquivalence

variable {first second : Judgment Input Output}

/-- Map a transition receipt without erasing its judgment evidence. -/
def mapEvidence (equivalence : ExactEquivalence first second)
    {source target : Term first} :
    TransitionEvidence first source target ->
      TransitionEvidence second (source.rebase second) (target.rebase second)
  | .accepted evidence =>
      .accepted (equivalence.evidenceEquiv _ _ evidence)

/-- Reflect a transition receipt to the source evidence presentation. -/
def reflectEvidence (equivalence : ExactEquivalence first second)
    {source target : Term first} :
    TransitionEvidence second (source.rebase second) (target.rebase second) ->
      TransitionEvidence first source target := by
  intro evidence
  cases source with
  | query input =>
      cases target with
      | query other => cases evidence
      | answer other output =>
          cases evidence with
          | accepted targetEvidence =>
              exact .accepted
                ((equivalence.evidenceEquiv input output).symm targetEvidence)
  | answer input output =>
      cases target <;> cases evidence

@[simp]
theorem reflectEvidence_mapEvidence
    (equivalence : ExactEquivalence first second)
    {source target : Term first}
    (evidence : TransitionEvidence first source target) :
    equivalence.reflectEvidence (equivalence.mapEvidence evidence) = evidence := by
  cases evidence with
  | accepted witness =>
      simp [mapEvidence, reflectEvidence]

@[simp]
theorem mapEvidence_reflectEvidence
    (equivalence : ExactEquivalence first second)
    {source target : Term first}
    (evidence : TransitionEvidence second
      (source.rebase second) (target.rebase second)) :
    equivalence.mapEvidence (equivalence.reflectEvidence evidence) = evidence := by
  cases source with
  | query input =>
      cases target with
      | query other => cases evidence
      | answer other output =>
          cases evidence with
          | accepted witness =>
              simp [mapEvidence, reflectEvidence]
  | answer input output =>
      cases target <;> cases evidence

/-- Exact equivalence of the complete transition-evidence fibres. -/
def transitionEquiv (equivalence : ExactEquivalence first second)
    (source target : Term first) :
    TransitionEvidence first source target ≃
      TransitionEvidence second
        (source.rebase second) (target.rebase second) where
  toFun := equivalence.mapEvidence
  invFun := equivalence.reflectEvidence
  left_inv := equivalence.reflectEvidence_mapEvidence
  right_inv := equivalence.mapEvidence_reflectEvidence

/-- Exact evidence equivalence induces the proof-relevant operational
translation between the two judgment GSLTs. -/
def exactTranslation (equivalence : ExactEquivalence first second) :
    ProofRelevant.ExactTranslation first.system second.system where
  toTranslation :=
    { mapTerm := Term.rebase second
      mapEquiv := by
        intro left right equal
        subst right
        rfl
      mapEvidence := equivalence.mapEvidence
      liftEvidence := by
        intro source target evidence
        cases source with
        | query input =>
            cases target with
            | query other => cases evidence
            | answer other output =>
                cases evidence with
                | accepted targetEvidence =>
                    exact ⟨.answer input output,
                      .accepted
                        ((equivalence.evidenceEquiv input output).symm
                          targetEvidence),
                      ⟨⟨rfl⟩⟩⟩
        | answer input output =>
            cases target <;> cases evidence }
  evidenceEquiv := equivalence.transitionEquiv
  evidenceEquiv_agrees := by
    intro source target evidence
    rfl

/-- Erasing proof receipts gives the equation-class semantic cover used by
ordinary GSLT and OSLF consumers. -/
def semanticCover (equivalence : ExactEquivalence first second) :
    SemanticCoveredTranslation first.theory second.theory :=
  SemanticCoveredTranslation.ofCoveredTranslation
    equivalence.exactTranslation.toTranslation.toCovered

/-- Exact evidence equivalence also preserves and reflects every semantic
one-step judgment. -/
theorem step_iff (equivalence : ExactEquivalence first second)
    (source target : Term first) :
    first.theory.Step source target <->
      second.theory.Step (source.rebase second) (target.rebase second) := by
  constructor
  · rintro ⟨evidence⟩
    exact ⟨equivalence.mapEvidence evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨equivalence.reflectEvidence evidence⟩

end ExactEquivalence

/-! ## Positive and negative controls -/

namespace Canary

def twoEvidence : Judgment Unit Unit where
  Evidence := fun _ _ => Bool

def optionalEvidence : Judgment Unit Unit where
  Evidence := fun _ _ => Option Unit

/-- A nonidentity change of receipt representation retains both inhabitants. -/
def exact : ExactEquivalence twoEvidence optionalEvidence where
  evidenceEquiv _ _ := by
    change Bool ≃ Option Unit
    exact
      { toFun := fun value => if value then some () else none
        invFun := fun value => value.isSome
        left_inv := by intro value; cases value <;> rfl
        right_inv := by intro value; cases value <;> rfl }

theorem positive_step_maps : optionalEvidence.theory.Step
    (exact.semanticCover.mapTerm (.query ()))
    (exact.semanticCover.mapTerm (.answer () ())) :=
  exact.semanticCover.mapStep ⟨.accepted false⟩

def oneEvidence : Judgment Unit Unit where
  Evidence := fun _ _ => Unit

/-- Negative control: a two-element receipt fibre cannot be called exactly
equivalent to a singleton receipt fibre. -/
theorem no_exact_two_to_one :
    Not (Nonempty (ExactEquivalence twoEvidence oneEvidence)) := by
  rintro ⟨equivalence⟩
  have fibre : Bool ≃ Unit := by
    simpa [twoEvidence, oneEvidence] using
      equivalence.evidenceEquiv () ()
  apply Bool.false_ne_true
  apply fibre.injective
  exact Subsingleton.elim _ _

end Canary

#print axioms ExactEquivalence.step_iff
#print axioms ExactEquivalence.semanticCover
#print axioms Canary.positive_step_maps
#print axioms Canary.no_exact_two_to_one

end Mettapedia.GSLT.ProofRelevantJudgment
