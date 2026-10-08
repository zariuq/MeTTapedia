import Mettapedia.OSLF.Framework.InterpretedGeneratedModality
import Mettapedia.GSLT.Topos.InteractionEventPresheaf

/-!
# Native event families for generated contextual modalities

A generated occurrence retains its supplied bindings, rely premises,
primitive rule firing and a separately supplied contextual step. Its presentation is sound for
the declared raw-pattern operational theory. No coverage of every language
step is assumed. The general existential modality does not require its
contextual step to select the saved primitive rule at the saved position.
A dependent modal implementation supplies an actual
native event certificate, with the same target witness recovered by the
native result map. Observer-context substitution acts on the whole receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneratedEventCertificates

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (RuleInterpretation)
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality (RelySatisfied)
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.PresheafEventCertificates
open InterpretedGeneratedModality

universe u

/-- The actual operational relation on raw patterns, retaining the declared
interpretation rather than replacing it by structural substitution. -/
def operationalTheory (interpretation : RuleInterpretation)
    (base : BasePremiseEvaluator) (lang : LanguageDef) : Mettapedia.GSLT.GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
    interpretation base lang
  rewrites_resp_left := by
    intro source source' target same firing
    subst source'
    exact ⟨target, firing, rfl⟩
  rewrites_resp_right := by
    intro source target target' firing same
    subst target'
    exact firing

/-- A supplied request together with its actual contextual operational edge. -/
structure Occurrence (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (term : Pattern)
    (bindings : Bindings) (source target : Pattern) : Type where
  rely : RelySatisfied rule pos A bindings
  fires : RuleFires interpretation base lang rule bindings
  filling : plug (applyBindings bindings rule.left) pos
    (applyBindings bindings term) = some source
  firing : Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
    interpretation base lang source target

/-- Generated requests give a sound authored event presentation. Their
binding sites and firing evidence are retained independently of endpoints. -/
def presentation (interpretation : RuleInterpretation) (base : BasePremiseEvaluator)
    (lang : LanguageDef) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (term : Pattern) :
    InteractionPresentation.{0, 0} (operationalTheory interpretation base lang) where
  Site := Bindings
  Event := Occurrence interpretation base lang rule pos A term
  sound occurrence := occurrence.firing

variable {C : Type} [Category C]
variable {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
variable {lang : LanguageDef} {rule : RewriteRule} {pos : Position}
variable {A : String → Pattern → Prop} {term : Pattern}

/-- A modal outcome supplies the exact enabled occurrence of its request. -/
def enabled {B : Pattern → Type u} {bindings : Bindings}
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings)
    (outcome : Outcome interpretation base lang rule pos term bindings B) :
    (presentation interpretation base lang rule pos A term).Enabled outcome.source where
  site := bindings
  target := outcome.target
  evidence := ⟨rely, fires, outcome.filling, outcome.firing⟩

/-- A contextual postcondition receives the outcome's supplied witness at
its actual target, through the same native sum used for all event spans. -/
def nativeCertificate
    (B : DisplayedFamily.{0, 0, 0, 0}
      ((presentation interpretation base lang rule pos A term).states (C := C)))
    (world : Cᵒᵖ) {bindings : Bindings}
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings)
    (outcome : Outcome interpretation base lang rule pos term bindings
      (fun target => B.obj ⟨world, target⟩)) :
    (((presentation interpretation base lang rule pos A term).eventSpan (C := C)).certificates B).obj
      ⟨world, outcome.source⟩ :=
  ((presentation interpretation base lang rule pos A term).eventSpan (C := C)).introduce B
    world ⟨outcome.source, enabled rely fires outcome⟩ outcome.evidence

/-- The event readout retains the original bindings and the actual firing. -/
theorem nativeCertificate_event
    (B : DisplayedFamily.{0, 0, 0, 0}
      ((presentation interpretation base lang rule pos A term).states (C := C)))
    (world : Cᵒᵖ) {bindings : Bindings}
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings)
    (outcome : Outcome interpretation base lang rule pos term bindings
      (fun target => B.obj ⟨world, target⟩)) :
    (((presentation interpretation base lang rule pos A term).eventSpan (C := C)).eventReadout B).app
      world ⟨outcome.source, nativeCertificate B world rely fires outcome⟩ =
        ⟨outcome.source, enabled rely fires outcome⟩ := rfl

/-- Native elimination returns the original dependent target witness. -/
theorem nativeCertificate_result
    (B : DisplayedFamily.{0, 0, 0, 0}
      ((presentation interpretation base lang rule pos A term).states (C := C)))
    (world : Cᵒᵖ) {bindings : Bindings}
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings)
    (outcome : Outcome interpretation base lang rule pos term bindings
      (fun target => B.obj ⟨world, target⟩)) :
    (((presentation interpretation base lang rule pos A term).eventSpan (C := C)).resultReadout B).app
      world ⟨outcome.source, nativeCertificate B world rely fires outcome⟩ =
        ⟨outcome.target, outcome.evidence⟩ := rfl

/-- Operational soundness uses the occurrence's real step, without event
completeness or an erased existence-to-evidence principle. -/
theorem nativeCertificate_sound
    (B : DisplayedFamily.{0, 0, 0, 0}
      ((presentation interpretation base lang rule pos A term).states (C := C)))
    (world : Cᵒᵖ) {bindings : Bindings}
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires interpretation base lang rule bindings)
    (outcome : Outcome interpretation base lang rule pos term bindings
      (fun target => B.obj ⟨world, target⟩)) :
    ∃ target, (operationalTheory interpretation base lang).Step outcome.source target ∧
      Nonempty (B.obj ⟨world, target⟩) :=
  (presentation interpretation base lang rule pos A term).certificate_sound B world outcome.source
    (nativeCertificate B world rely fires outcome)

end Mettapedia.OSLF.Framework.GeneratedEventCertificates
