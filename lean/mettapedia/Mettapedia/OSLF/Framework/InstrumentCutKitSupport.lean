import Mettapedia.OSLF.Framework.InstrumentCutKitReactions

/-!
# Hereditary instrument support of actual typed terms and contexts

Original constructors remain available. Argument formers, probes and their
interaction profiles require the corresponding kit permission, at every
stored subtree. Filling and path composition preserve support, and support
of a composite reflects to both actual factors. Proper source reactions
preserve this grammar independently of administrative permission.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitSupportQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

inductive KitConstructor (opened : InstrumentObservations.Policy Symbols) :
    Constructor Symbols arity → Prop where
  | original (constructor : Symbols) : KitConstructor opened (.original constructor)
  | arguments (constructor : Symbols) (permission : opened constructor) :
      KitConstructor opened (.arguments constructor)
  | probe (instrument : Probe Symbols arity)
      (permission : opened (instrumentConstructor arity instrument)) :
      KitConstructor opened (.probe instrument)
  | cut (instrument : Probe Symbols arity)
      (permission : opened (instrumentConstructor arity instrument)) :
      KitConstructor opened (.cut instrument)

def KitSupported (opened : InstrumentObservations.Policy Symbols) :
    {sort : Srt Symbols arity} → Value arity sort → Prop
  | _, .node constructor arguments => KitConstructor arity opened constructor ∧
      ∀ position, KitSupported opened (arguments position)

theorem kitSupported_original (opened : InstrumentObservations.Policy Symbols)
    (constructor : Symbols) (arguments : Fin (arity constructor) → Value arity .base)
    (children : ∀ position, KitSupported arity opened (arguments position)) :
    KitSupported arity opened (original arity constructor arguments) := ⟨.original constructor, children⟩

theorem kitSupported_bundle (opened : InstrumentObservations.Policy Symbols)
    (constructor : Symbols) (permission : opened constructor)
    (arguments : Fin (arity constructor) → Value arity .base)
    (children : ∀ position, KitSupported arity opened (arguments position)) :
    KitSupported arity opened (bundle arity constructor arguments) := ⟨.arguments constructor permission, children⟩

theorem kitSupported_probe (opened : InstrumentObservations.Policy Symbols)
    (instrument : Probe Symbols arity) (permission : opened (instrumentConstructor arity instrument)) :
    KitSupported arity opened (probe arity instrument) :=
  ⟨.probe instrument permission, fun position => Fin.elim0 position⟩

theorem embedSource_kitSupported (opened : InstrumentObservations.Policy Symbols)
    (source : InstrumentObservations.Tree Symbols arity) : KitSupported arity opened (embedSource arity source) := by
  induction source with
  | node constructor arguments inductionHypothesis => exact ⟨.original constructor, inductionHypothesis⟩

def KitFrame (opened : InstrumentObservations.Policy Symbols) :
    {source target : Srt Symbols arity} → Frame (signature arity) source target → Prop
  | _, _, .slot constructor position siblings => KitConstructor arity opened constructor ∧
      ∀ other different, KitSupported arity opened (siblings other different)

theorem kitSupported_fill {opened : InstrumentObservations.Policy Symbols}
    {source target : Srt Symbols arity} {frame : Frame (signature arity) source target}
    {value : Value arity source} (frameSupported : KitFrame arity opened frame)
    (valueSupported : KitSupported arity opened value) : KitSupported arity opened (frame.fill value) := by
  classical
  refine @Frame.casesOn (signature arity)
    (fun source _ frame => ∀ value : Value arity source,
      KitFrame arity opened frame → KitSupported arity opened value →
        KitSupported arity opened (frame.fill value))
    source target frame ?_ value frameSupported valueSupported
  intro constructor position siblings value frameSupported valueSupported
  refine ⟨frameSupported.1, ?_⟩
  intro other
  by_cases same : other = position
  · subst other
    simpa [Frame.fill] using valueSupported
  · simpa only [Frame.fill, dif_neg same] using frameSupported.2 other same

theorem kitSupported_fill_inv {opened : InstrumentObservations.Policy Symbols}
    {source target : Srt Symbols arity} (frame : Frame (signature arity) source target)
    (value : Value arity source) (supported : KitSupported arity opened (frame.fill value)) :
    KitSupported arity opened value ∧ KitFrame arity opened frame := by
  classical
  refine @Frame.casesOn (signature arity)
    (fun source _ frame => ∀ value : Value arity source,
      KitSupported arity opened (frame.fill value) →
        KitSupported arity opened value ∧ KitFrame arity opened frame)
    source target frame ?_ value supported
  intro constructor position siblings value supported
  refine ⟨?_, supported.1, ?_⟩
  · simpa [Frame.fill] using supported.2 position
  · intro other different
    simpa only [Frame.fill, dif_neg different] using supported.2 other

inductive KitContext (opened : InstrumentObservations.Policy Symbols) :
    {source target : Srt Symbols arity} → Context (signature arity) source target → Prop where
  | nil (sort : Srt Symbols arity) : KitContext opened (.nil : Context (signature arity) sort sort)
  | cons {source middle target : Srt Symbols arity}
      {previous : Context (signature arity) source middle} {frame : Frame (signature arity) middle target}
      (previousSupported : KitContext opened previous) (frameSupported : KitFrame arity opened frame) :
      KitContext opened (previous.cons frame)

theorem KitContext.fill {opened : InstrumentObservations.Policy Symbols}
    {source target : Srt Symbols arity} {context : Context (signature arity) source target}
    (supported : KitContext arity opened context) {value : Value arity source}
    (valueSupported : KitSupported arity opened value) :
    KitSupported arity opened ((action (signature arity)).path context value) := by
  induction supported with
  | nil => exact valueSupported
  | cons previous frame inductionHypothesis => exact kitSupported_fill arity frame inductionHypothesis

theorem kitSupported_context_inv {opened : InstrumentObservations.Policy Symbols}
    {source target : Srt Symbols arity} (context : Context (signature arity) source target)
    (value : Value arity source) (supported : KitSupported arity opened ((action (signature arity)).path context value)) :
    KitSupported arity opened value ∧ KitContext arity opened context := by
  induction context with
  | nil => exact ⟨supported, .nil _⟩
  | cons previous frame inductionHypothesis =>
    obtain ⟨innerSupported, frameSupported⟩ := kitSupported_fill_inv arity frame _ supported
    obtain ⟨valueSupported, previousSupported⟩ := inductionHypothesis innerSupported
    exact ⟨valueSupported, .cons previousSupported frameSupported⟩

theorem KitContext.comp {opened : InstrumentObservations.Policy Symbols}
    {source middle target : Srt Symbols arity} {first : Context (signature arity) source middle}
    {second : Context (signature arity) middle target}
    (firstSupported : KitContext arity opened first) (secondSupported : KitContext arity opened second) :
    KitContext arity opened (first.comp second) := by
  induction secondSupported with
  | nil => exact firstSupported
  | cons previous frame inductionHypothesis => exact .cons inductionHypothesis frame

theorem kitContext_comp_inv {opened : InstrumentObservations.Policy Symbols}
    {source middle target : Srt Symbols arity} (first : Context (signature arity) source middle)
    (second : Context (signature arity) middle target) (supported : KitContext arity opened (first.comp second)) :
    KitContext arity opened first ∧ KitContext arity opened second := by
  induction second with
  | nil => exact ⟨supported, .nil _⟩
  | cons previous frame inductionHypothesis =>
    cases supported with
    | cons previousSupported frameSupported =>
      obtain ⟨firstSupported, secondSupported⟩ := inductionHypothesis previousSupported
      exact ⟨firstSupported, .cons secondSupported frameSupported⟩

inductive KitArrow (opened : InstrumentObservations.Policy Symbols) :
    {source target : ContextObject (signature arity)} → (source ⟶ target) → Prop where
  | identity : KitArrow opened (Arrow.identity (action := action (signature arity)))
  | value {target : Srt Symbols arity} {value : Value arity target}
      (supported : KitSupported arity opened value) : KitArrow opened (termArrow (signature arity) value)
  | context {source target : Srt Symbols arity} {context : Context (signature arity) source target}
      (supported : KitContext arity opened context) : KitArrow opened (contextArrow (signature arity) context)

theorem KitArrow.id (opened : InstrumentObservations.Policy Symbols) (object : ContextObject (signature arity)) :
    KitArrow arity opened (𝟙 object) := by
  cases object with
  | origin => exact .identity
  | interface sort => exact .context (.nil sort)

theorem KitArrow.comp {opened : InstrumentObservations.Policy Symbols}
    {source middle target : ContextObject (signature arity)} {first : source ⟶ middle} {second : middle ⟶ target}
    (firstSupported : KitArrow arity opened first) (secondSupported : KitArrow arity opened second) :
    KitArrow arity opened (first ≫ second) := by
  cases firstSupported with
  | identity => exact secondSupported
  | value valueSupported =>
    cases secondSupported with
    | context contextSupported => exact .value (contextSupported.fill arity valueSupported)
  | context firstSupported =>
    cases secondSupported with
    | context secondSupported => exact .context (firstSupported.comp arity secondSupported)

theorem kitArrow_comp_inv {opened : InstrumentObservations.Policy Symbols}
    {source middle target : ContextObject (signature arity)} (first : source ⟶ middle) (second : middle ⟶ target)
    (supported : KitArrow arity opened (first ≫ second)) :
    KitArrow arity opened first ∧ KitArrow arity opened second := by
  cases first with
  | identity => exact ⟨.identity, supported⟩
  | value supplied =>
    cases second with
    | context context =>
      cases supported with
      | value valueSupported =>
        obtain ⟨inputSupported, contextSupported⟩ := kitSupported_context_inv arity context supplied valueSupported
        exact ⟨.value inputSupported, .context contextSupported⟩
  | context first =>
    cases second with
    | context second =>
      cases supported with
      | context contextSupported =>
        obtain ⟨firstSupported, secondSupported⟩ := kitContext_comp_inv arity first second contextSupported
        exact ⟨.context firstSupported, .context secondSupported⟩

theorem proper_rule_support (opened : InstrumentObservations.Policy Symbols) (rule : SourceRule arity) :
    KitArrow arity opened rule.reaction.redex ∧ KitArrow arity opened rule.reaction.reactum :=
  ⟨.value (embedSource_kitSupported arity opened rule.redex),
    .value (embedSource_kitSupported arity opened rule.reactum)⟩

theorem administrative_support {opened : InstrumentObservations.Policy Symbols}
    {instrument : Probe Symbols arity} (instance_ : AdministrativeInstance arity instrument)
    (supported : KitSupported arity opened (cut arity instrument (probe arity instrument) instance_.body)) :
    opened (instrumentConstructor arity instrument) ∧ KitSupported arity opened instance_.output := by
  have permission : opened (instrumentConstructor arity instrument) := by
    cases supported.1 with
    | cut _ permission => exact permission
  have bodySupported : KitSupported arity opened instance_.body := supported.2 (1 : Fin 2)
  refine ⟨permission, ?_⟩
  cases instance_ with
  | ask constructor arguments => exact kitSupported_bundle arity opened constructor permission arguments bodySupported.2
  | get constructor position arguments => exact bodySupported.2 position
  | build constructor arguments => exact kitSupported_original arity opened constructor arguments bodySupported.2

end Mettapedia.OSLF.Framework.InstrumentCutContexts
