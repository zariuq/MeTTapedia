import Mettapedia.GSLT.Core.AuthoredClosedTheory
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRelations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxLimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Nonidentity program transport and retained rule origins

The program relation is the actual graph of Boolean negation. Its closed
theory endomap exchanges both programs and reduction events; a stationary
false-to-false event is rejected. Two authored rule origins remain distinct
even when their complete reduction actions coincide.

Independent relative syntax exercises annotated abstraction and its generated
beta law. An identity with the wrong source cannot be admitted, and a
deliberate collision of fresh arrow names does not reflect source identity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.AuthoredClosedTheoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ProgramReductionTheory AuthoredClosedTheory

def negate : Bool ⟶ Bool := TypeCat.ofHom Bool.not

def graph : Bool ⟶ Bool ⨯ Bool := prod.lift (𝟙 Bool) negate

instance graph_mono : Mono graph where
  right_cancellation first second same := by
    have projected := congrArg (fun arrow => arrow ≫ (prod.fst : Bool ⨯ Bool ⟶ Bool)) same
    simpa only [Category.assoc, graph, prod.lift_fst, Category.comp_id] using projected

abbrev theory : Theory.{1,0} where
  closed :=
    { Obj := Type
      instCategory := inferInstance
      instCartesianMonoidal := inferInstance
      instMonoidalClosed := inferInstance
      instHasFiniteLimits := inferInstance }
  program := Bool
  reduction := Subobject.mk graph

def eventIso : theory.Event ≅ Bool := Subobject.underlyingIso graph

theorem event_source : theory.source = eventIso.hom := by
  change (Subobject.mk graph).arrow ≫ prod.fst = eventIso.hom
  rw [← Subobject.underlyingIso_hom_comp_eq_mk graph, Category.assoc]
  exact (congrArg (eventIso.hom ≫ ·) (prod.lift_fst (𝟙 Bool) negate)).trans
    (Category.comp_id _)

theorem event_target : theory.target = eventIso.hom ≫ negate := by
  change (Subobject.mk graph).arrow ≫ prod.snd = eventIso.hom ≫ negate
  rw [← Subobject.underlyingIso_hom_comp_eq_mk graph, Category.assoc]
  exact congrArg (eventIso.hom ≫ ·) (prod.lift_snd (𝟙 Bool) negate)

def exchange : Bool ≅ Bool where
  hom := negate
  inv := negate
  hom_inv_id := by ext value; cases value <;> rfl
  inv_hom_id := by ext value; cases value <;> rfl

def exchangeMap : Map theory theory where
  closed := LambdaTheoryMap.id theory.closed
  program := exchange
  reduction := eventIso.hom ≫ negate ≫ eventIso.inv
  source := by
    change (eventIso.hom ≫ negate ≫ eventIso.inv) ≫ theory.source =
      theory.source ≫ negate
    rw [event_source, Category.assoc, Category.assoc, eventIso.inv_hom_id, Category.comp_id]
  target := by
    change (eventIso.hom ≫ negate ≫ eventIso.inv) ≫ theory.target =
      theory.target ≫ negate
    rw [event_target, Category.assoc, Category.assoc, ← Category.assoc eventIso.inv,
      eventIso.inv_hom_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm

def suppliedEvent : theory.Event := eventIso.inv false

theorem nonidentity_program_readout : exchangeMap.program.hom false = true := rfl

theorem exchanged_event_readout : eventIso.hom (exchangeMap.reduction suppliedEvent) = true := by
  have inverse := congrArg (fun arrow : Bool ⟶ Bool => arrow false) eventIso.inv_hom_id
  change eventIso.hom (eventIso.inv (negate (eventIso.hom suppliedEvent))) = true
  have read : eventIso.hom suppliedEvent = false := inverse
  have flipped := congrArg (fun arrow : Bool ⟶ Bool => arrow true) eventIso.inv_hom_id
  rw [read]
  exact flipped

theorem stationary_event_rejected :
    ¬ ∃ event : theory.Event, theory.source event = false ∧ theory.target event = false := by
  rintro ⟨event, source, target⟩
  rw [event_source] at source
  rw [event_target] at target
  change negate (eventIso.hom event) = false at target
  rw [source] at target
  cases target

def negationRule : Rule theory where
  parameters := Bool
  left := 𝟙 Bool
  right := negate
  action := eventIso.inv
  source := by rw [event_source]; exact eventIso.inv_hom_id
  target := by rw [event_target, ← Category.assoc, eventIso.inv_hom_id, Category.id_comp]

def wholePosition : Position negationRule where
  environment := Bool
  carrier := Bool
  relies := 𝟙 Bool
  focus := 𝟙 Bool
  plug := prod.snd
  decomposition := prod.lift_snd _ _

def authored : Presentation theory where
  ConstructorOrigin := Bool
  constructor name := ⟨Bool, if name then negate else 𝟙 Bool⟩
  RuleOrigin := Bool
  rule _ := negationRule
  PositionOrigin _ := Unit
  position _ _ := wholePosition

theorem duplicate_origins_retain_complete_action :
    (authored.rule false).action = (authored.rule true).action := rfl

theorem duplicate_rule_origins_differ : (false : authored.RuleOrigin) ≠ true := Bool.false_ne_true

theorem transported_rule_changes_source :
    (Rule.transport exchangeMap negationRule).left false = true := rfl

theorem actual_rule_transport_composes :
    Rule.transport exchangeMap (Rule.transport exchangeMap negationRule) =
      Rule.transport (Map.compose exchangeMap exchangeMap) negationRule :=
  Rule.transport_compose exchangeMap exchangeMap negationRule

theorem supplied_position_transport_decomposes :
    prod.lift (Position.transport exchangeMap wholePosition).relies
        (Position.transport exchangeMap wholePosition).focus ≫
      (Position.transport exchangeMap wholePosition).plug =
        (Rule.transport exchangeMap negationRule).left :=
  (Position.transport exchangeMap wholePosition).decomposition

open Mettapedia.CategoryTheory.RelativeClosedSyntax

abbrev syntaxSymbols : Symbols where
  ObjectName := Unit
  ArrowName := Bool
  EquationName := Empty

def syntaxSignature : Signature (C := Type) (symbols := syntaxSymbols) where
  objectRank _ := 0
  arrowRank name := if name then 2 else 1
  source _ := .name ()
  target _ := .name ()
  source_before name := by simp only [ObjectCode.before]; cases name <;> decide
  target_before name := by simp only [ObjectCode.before]; cases name <;> decide
  equationRank origin := origin.elim
  equationSource origin := origin.elim
  equationTarget origin := origin.elim
  left origin := origin.elim
  right origin := origin.elim
  equation_before origin := origin.elim

abbrev contextCode : ObjectCode (Type) syntaxSymbols := .name ()

def contextFormation : Derivation syntaxSignature (.object contextCode) :=
  Derivation.objectName (signature := syntaxSignature) ()

def annotatedBody : ArrowCode (Type) syntaxSymbols := .second contextCode contextCode

def annotatedBodyTyped : Derivation syntaxSignature
    (.arrow (.product contextCode contextCode) contextCode annotatedBody) :=
  .second contextFormation contextFormation

def annotatedAbstraction : ArrowCode (Type) syntaxSymbols :=
  .curry contextCode contextCode contextCode annotatedBody

def annotatedAbstractionTyped : Derivation syntaxSignature
    (.arrow contextCode (.exponential contextCode contextCode) annotatedAbstraction) :=
  .curry contextFormation contextFormation contextFormation annotatedBodyTyped

def generatedBeta : Derivation syntaxSignature
    (.equation (.product contextCode contextCode) contextCode
      (.compose (.pair (.compose (.first contextCode contextCode) annotatedAbstraction)
        (.second contextCode contextCode)) (.evaluation contextCode contextCode)) annotatedBody) :=
  .exponentialBeta contextFormation contextFormation contextFormation annotatedBodyTyped

theorem wrong_identity_source_rejected :
    ¬ Nonempty (Derivation syntaxSignature
      (.arrow .terminal (.product .terminal .terminal)
        (.identity (.product .terminal .terminal)))) := by
  rintro ⟨tree⟩
  cases tree

abbrev collidedSymbols : Symbols where
  ObjectName := Unit
  ArrowName := Unit
  EquationName := Empty

theorem source_arrow_names_are_distinct :
    (ArrowCode.name false : ArrowCode (Type) syntaxSymbols) ≠ .name true := by
  intro same
  cases same

theorem actual_name_collision :
    (ArrowCode.name false : ArrowCode (Type) syntaxSymbols).map (Functor.id (Type))
        (symbols := syntaxSymbols) (targetSymbols := collidedSymbols) id (fun _ => ()) =
      (ArrowCode.name true : ArrowCode (Type) syntaxSymbols).map (Functor.id (Type))
        (symbols := syntaxSymbols) (targetSymbols := collidedSymbols) id (fun _ => ()) := rfl

namespace Generated

open Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory

def dataObject : Object syntaxSignature := ⟨contextCode, ⟨contextFormation⟩⟩

def suppliedBody : product dataObject dataObject ⟶ dataObject :=
  classOf ⟨annotatedBody, ⟨annotatedBodyTyped⟩⟩

def suppliedFunction : dataObject ⟶ exponentialObject dataObject dataObject := abstraction suppliedBody

theorem complete_generic_argument_readout :
    pairing (first dataObject dataObject ≫ suppliedFunction) (second dataObject dataObject) ≫
      evaluation dataObject dataObject = second dataObject dataObject :=
  unabstract_abstraction suppliedBody

theorem complete_supplied_function_recovery : abstraction (unabstract suppliedFunction) =
    suppliedFunction := abstraction_unabstract suppliedFunction

def diagonal : dataObject ⟶ product dataObject dataObject := pairing (𝟙 dataObject) (𝟙 dataObject)

theorem diagonal_commutes : diagonal ≫ first dataObject dataObject =
    diagonal ≫ second dataObject dataObject :=
  (pairing_first (𝟙 dataObject) (𝟙 dataObject)).trans
    (pairing_second (𝟙 dataObject) (𝟙 dataObject)).symm

def suppliedEqualizerLift : dataObject ⟶
    equalizerObject (first dataObject dataObject) (second dataObject dataObject) :=
  equalizerLift (first dataObject dataObject) (second dataObject dataObject) diagonal diagonal_commutes

theorem equalizer_retains_first_variable :
    suppliedEqualizerLift ≫ equalizerInclusion (first dataObject dataObject) (second dataObject dataObject) ≫
      first dataObject dataObject = 𝟙 dataObject := by
  change equalizerLift (first dataObject dataObject) (second dataObject dataObject)
    diagonal diagonal_commutes ≫
      equalizerInclusion (first dataObject dataObject) (second dataObject dataObject) ≫
      first dataObject dataObject = 𝟙 dataObject
  rw [← Category.assoc, equalizerLift_inclusion]
  exact pairing_first (𝟙 dataObject) (𝟙 dataObject)

theorem equalizer_retains_second_variable :
    suppliedEqualizerLift ≫ equalizerInclusion (first dataObject dataObject) (second dataObject dataObject) ≫
      second dataObject dataObject = 𝟙 dataObject := by
  change equalizerLift (first dataObject dataObject) (second dataObject dataObject)
    diagonal diagonal_commutes ≫
      equalizerInclusion (first dataObject dataObject) (second dataObject dataObject) ≫
      second dataObject dataObject = 𝟙 dataObject
  rw [← Category.assoc, equalizerLift_inclusion]
  exact pairing_second (𝟙 dataObject) (𝟙 dataObject)

theorem equalizer_complete_factor_unique
    (candidate : dataObject ⟶ equalizerObject (first dataObject dataObject) (second dataObject dataObject))
    (complete : candidate ≫ equalizerInclusion (first dataObject dataObject) (second dataObject dataObject) =
      diagonal) : candidate = suppliedEqualizerLift :=
  equalizer_joint_cancel (first dataObject dataObject) (second dataObject dataObject)
    (complete.trans (equalizerLift_inclusion _ _ diagonal diagonal_commutes).symm)

end Generated

namespace StagedHeader

abbrev symbols : Symbols where
  ObjectName := Empty
  ArrowName := Unit
  EquationName := Unit

abbrev identityCode : ArrowCode (Type) symbols := .identity .terminal

abbrev compositeCode : ArrowCode (Type) symbols := .compose identityCode identityCode

abbrev innerObject : ObjectCode (Type) symbols :=
  .equalizer .terminal .terminal identityCode identityCode

abbrev innerLift : ArrowCode (Type) symbols :=
  .equalizerLift .terminal .terminal identityCode identityCode .terminal identityCode

abbrev sourceCode : ObjectCode (Type) symbols :=
  .equalizer .terminal innerObject innerLift innerLift

def signature : Signature (C := Type) (symbols := symbols) where
  objectRank origin := origin.elim
  arrowRank _ := 1
  source _ := sourceCode
  target _ := .terminal
  source_before _ := by simp only [ObjectCode.before, ArrowCode.before]; trivial
  target_before _ := trivial
  equationRank _ := 2
  equationSource _ := .terminal
  equationTarget _ := .terminal
  left _ := compositeCode
  right _ := compositeCode
  equation_before _ := by simp only [ObjectCode.before, ArrowCode.before]; trivial

def terminalFormed : Derivation signature (.object .terminal) := .terminalObject

def identityTyped : Derivation signature (.arrow .terminal .terminal identityCode) :=
  .identity terminalFormed

def compositeTyped : Derivation signature (.arrow .terminal .terminal compositeCode) :=
  .compose identityTyped identityTyped

def lateEquation : Derivation signature
    (.equation .terminal .terminal compositeCode compositeCode) :=
  .declaredEquation () compositeTyped compositeTyped

def innerFormed : Derivation signature (.object innerObject) :=
  .equalizerObject terminalFormed terminalFormed identityTyped identityTyped

def suppliedLift : Derivation signature (.arrow .terminal innerObject innerLift) :=
  .equalizerLift terminalFormed terminalFormed terminalFormed identityTyped identityTyped
    identityTyped lateEquation

def suppliedSource : Derivation signature (.object sourceCode) :=
  .equalizerObject terminalFormed innerFormed suppliedLift suppliedLift

def headers : HeaderFormation signature where
  source _ := suppliedSource
  target _ := terminalFormed
  left _ := compositeTyped
  right _ := compositeTyped

theorem raw_header_has_only_earlier_names :
    (signature.source ()).before signature.objectRank signature.arrowRank (signature.arrowRank ()) :=
  signature.source_before ()

/-- This particular supplied tree is not an earlier-stage header certificate:
its lift uses the separately authored later equation, despite the raw header
containing no fresh names. No claim rules out a different earlier proof. -/
theorem supplied_header_uses_a_later_equation :
    ¬ (headers.source ()).bounded (signature.arrowRank ()) := by
  simp only [headers, suppliedSource, suppliedLift, innerFormed, terminalFormed,
    identityTyped, lateEquation, compositeTyped, Derivation.bounded, signature]
  decide

def earlierLift : Derivation signature (.arrow .terminal innerObject innerLift) :=
  .equalizerLift terminalFormed terminalFormed terminalFormed identityTyped identityTyped
    identityTyped (.reflexivity compositeTyped)

def earlierSource : Derivation signature (.object sourceCode) :=
  .equalizerObject terminalFormed innerFormed earlierLift earlierLift

def earlierHeaders : HeaderFormation signature where
  source _ := earlierSource
  target _ := terminalFormed
  left _ := compositeTyped
  right _ := compositeTyped

def orderedHeaders : OrderedHeaderFormation signature where
  formation := earlierHeaders
  source_before _ := by
    simp only [earlierHeaders, earlierSource, earlierLift, innerFormed, terminalFormed,
      identityTyped, compositeTyped, Derivation.bounded]
    trivial
  target_before _ := trivial
  left_before _ := by
    simp only [earlierHeaders, compositeTyped, identityTyped, terminalFormed, Derivation.bounded]
    trivial
  right_before _ := by
    simp only [earlierHeaders, compositeTyped, identityTyped, terminalFormed, Derivation.bounded]
    trivial

theorem same_header_retains_distinct_formation_trees : suppliedSource ≠ earlierSource := by
  intro same
  apply supplied_header_uses_a_later_equation
  change suppliedSource.bounded (signature.arrowRank ())
  rw [same]
  exact orderedHeaders.source_before ()

end StagedHeader

end Mettapedia.GSLT.Core.AuthoredClosedTheoryControls
