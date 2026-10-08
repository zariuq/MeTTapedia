import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

/-!
# Generated contextual modalities under a declared rule interpretation

The stable authored focus still supplies the instantiated source, while
the declared interpretation supplies its operational contractum. The
dependent rules retain a chosen target and its actual certificate. Their
predicate erasure is an existential modal specification; it does not infer
a coherent family of certificates from propositional inhabitation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InterpretedGeneratedModality

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (RuleInterpretation)
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality (StablePath RelySatisfied)

universe u v

def RuleFires (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (bindings : Bindings) : Prop :=
  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base lang
    (applyBindings bindings rule.left) (interpretation.instantiateRule lang rule bindings)

def RelyPossibly (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (B : Pattern → Prop) (term : Pattern) : Prop :=
  ∀ bindings : Bindings, RelySatisfied rule pos A bindings →
    RuleFires interpretation base lang rule bindings →
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings term) = some source ∧
      Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base lang
        source target ∧ B target

/-- The complete dependent result of one admitted filling. -/
structure Outcome (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (pos : Position) (term : Pattern)
    (bindings : Bindings) (B : Pattern → Type u) where
  source : Pattern
  target : Pattern
  filling : plug (applyBindings bindings rule.left) pos (applyBindings bindings term) = some source
  firing : Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base lang
    source target
  evidence : B target

/-- A supplied implementation of every admitted operational request. -/
def RelyEvidence (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (B : Pattern → Type u) (term : Pattern) : Type u :=
  ∀ bindings : Bindings, RelySatisfied rule pos A bindings →
    RuleFires interpretation base lang rule bindings →
    Outcome interpretation base lang rule pos term bindings B

/-- M-FORM changes only the predicates assigned to the actual rely variables. -/
def relyEvidenceCongr {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A A' : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (same : ∀ name ∈ relyVars rule.left pos, A name = A' name) :
    RelyEvidence interpretation base lang rule pos A B term ≃
      RelyEvidence interpretation base lang rule pos A' B term where
  toFun implementation := fun bindings rely fires =>
    implementation bindings (fun name member value lookup =>
      (same name member) ▸ rely name member value lookup) fires
  invFun implementation := fun bindings rely fires =>
    implementation bindings (fun name member value lookup =>
      (same name member).symm ▸ rely name member value lookup) fires
  left_inv _ := by
    funext bindings rely fires
    rfl
  right_inv _ := by
    funext bindings rely fires
    rfl

/-- M-INTRO stores the supplied right-hand-side certificate and uses the
checked stability theorem for the source filling. -/
def introduce {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (stable : StablePath rule.left pos = true)
    (focus : subtermAt rule.left pos = some term)
    (implementation : ∀ bindings, RelySatisfied rule pos A bindings →
      RuleFires interpretation base lang rule bindings →
      B (interpretation.instantiateRule lang rule bindings)) :
    RelyEvidence interpretation base lang rule pos A B term :=
  fun bindings rely fires =>
    { source := applyBindings bindings rule.left
      target := interpretation.instantiateRule lang rule bindings
      filling := GeneratedModality.plug_applyBindings bindings stable focus
      firing := fires
      evidence := implementation bindings rely fires }

/-- M-STEP delivers the actual filled source, chosen target and genuine step. -/
theorem step {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (implementation : RelyEvidence interpretation base lang rule pos A B term)
    (bindings : Bindings) (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings) :
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings term) = some source ∧
      Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base lang
        source target := by
  let actual := implementation bindings rely fires
  exact ⟨actual.source, actual.target, actual.filling, actual.firing⟩

/-- M-ELIM returns the supplied witness at the actual target, without changing
the target or replacing a dependent certificate by support. -/
def result {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (implementation : RelyEvidence interpretation base lang rule pos A B term)
    (bindings : Bindings) (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings) : Σ target, B target :=
  ⟨(implementation bindings rely fires).target, (implementation bindings rely fires).evidence⟩

theorem introduce_result {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (stable : StablePath rule.left pos = true) (focus : subtermAt rule.left pos = some term)
    (implementation : ∀ bindings, RelySatisfied rule pos A bindings →
      RuleFires interpretation base lang rule bindings →
      B (interpretation.instantiateRule lang rule bindings))
    (bindings : Bindings) (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings) :
    result (introduce stable focus implementation) bindings rely fires =
      ⟨interpretation.instantiateRule lang rule bindings, implementation bindings rely fires⟩ := rfl

/-- Predicate support of the supplied implementation is the modal specification. -/
theorem evidence_support {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
    {A : String → Pattern → Prop} {B : Pattern → Type u} {term : Pattern}
    (implementation : RelyEvidence interpretation base lang rule pos A B term) :
    RelyPossibly interpretation base lang rule pos A (fun target => Nonempty (B target)) term := by
  intro bindings rely fires
  let actual := implementation bindings rely fires
  exact ⟨actual.source, actual.target, actual.filling, actual.firing, ⟨actual.evidence⟩⟩

/-- The general interpretation agrees with the existing syntactic modality
at the syntactic interpretation, including its operational premise. -/
theorem syntactic_iff {base : BasePremiseEvaluator} {lang : LanguageDef}
    {rule : RewriteRule} {pos : Position} {A : String → Pattern → Prop}
    {B : Pattern → Prop} {term : Pattern} :
    RelyPossibly .syntactic base lang rule pos A B term ↔
      GeneratedModality.RelyPossibly base lang rule pos A B term := by
  unfold RelyPossibly GeneratedModality.RelyPossibly RuleFires GeneratedModality.RuleFires
  simp only [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_syntactic_iff_contextual]
  rfl

/-- A live admitted firing prevents vacuous inhabitation at an empty result. -/
theorem not_relyPossibly_empty {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {term : Pattern}
    (bindings : Bindings) (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings) :
    ¬ RelyPossibly interpretation base lang rule pos A (fun _ => False) term := by
  intro certificate
  obtain ⟨_, _, _, _, impossible⟩ := certificate bindings rely fires
  exact impossible

end Mettapedia.OSLF.Framework.InterpretedGeneratedModality
