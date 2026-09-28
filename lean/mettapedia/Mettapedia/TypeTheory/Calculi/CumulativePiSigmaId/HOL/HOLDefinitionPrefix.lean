import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionModelExtension

/-!
# Ordered semantic prefixes of checked HOL definitions

Each successor is a fresh definition checked against exactly the preceding
signature. Its source model is extended by interpreting the new constant as
its closed body. The prefix retains an embedding of every earlier source term,
including terms containing names introduced by earlier successors.

This is a semantic and admission prefix over the existing HOL/native syntax;
it is not a replacement for the external document parser or NIK replay.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionPrefix

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface HOLImpredicativeRepresentation
open HOLDefinitionModelExtension

universe u v w

-- The constant universe is closed under `DefinedConst`; the model universe
-- remains independent. Their combined occurrence in this dependent package
-- is intentional, despite the generic universe-coincidence linter heuristic.
set_option linter.checkUnivs false
/-- One state of a checked, definition-respecting HOL/native prefix. -/
structure State (Base : Type u) where
  Const : HOL.Ty Base → Type (max u v)
  signature : LogicalSignature Base Const
  model : HOL.HenkinModel.{u, max u v, w} Base Const
set_option linter.checkUnivs true

/-- A successor is determined by a source body and a fresh native name.
Both the logical signature and the Henkin model are extended by the same
definition; neither may be supplied independently by a caller. -/
def State.advance {Base : Type u} (state : State.{u, v, w} Base)
    (name : DeclName) {type : HOL.Ty Base} (body : HOL.Term state.Const [] type)
    (fresh : state.signature.rules.constantType name = none) : State.{u, v, w} Base where
  Const := HOL.DefinedConst state.Const type
  signature := extendedSignature state.signature name body fresh
  model := state.model.definitionExtension body

/-- A dependently typed telescope of checked fresh definitions. The type of
each later body is the signature produced by all preceding definitions. -/
inductive CheckedPrefix {Base : Type u} (initial : State.{u, v, w} Base) :
    State.{u, v, w} Base → Type _ where
  | nil : CheckedPrefix initial initial
  | snoc {prior : State.{u, v, w} Base} (chain : CheckedPrefix initial prior)
      (name : DeclName) {type : HOL.Ty Base}
      (body : HOL.Term prior.Const [] type)
      (fresh : prior.signature.rules.constantType name = none) :
      CheckedPrefix initial (prior.advance name body fresh)

/-- The actual retained source syntax map through an ordered prefix. -/
def CheckedPrefix.embed {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term initial.Const gamma type) : HOL.Term final.Const gamma type :=
  match chain with
  | .nil => term
  | .snoc earlier _ _ _ => HOL.DefinedConst.embed (earlier.embed term)

/-- Translation of any earlier term is literally unchanged at every later
prefix state. This is the native-code counterpart of source embedding. -/
theorem CheckedPrefix.translate_embed
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term initial.Const gamma type) :
    translate final.signature (chain.embed term) =
      translate initial.signature term := by
  induction chain with
  | nil => rfl
  | @snoc prior earlier name type body fresh ih =>
      change translate (extendedSignature prior.signature name body fresh)
        (HOL.DefinedConst.embed (earlier.embed term)) = _
      rw [translate_embedded prior.signature name body fresh (earlier.embed term)]
      exact ih

/-- Every declaration and licensed root computation from the initial
inventory remains available after any number of fresh definitions. -/
theorem CheckedPrefix.declarations_extend
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final) :
    initial.signature.declarations.Extends final.signature.declarations := by
  induction chain with
  | nil => exact Signature.Extends.refl _
  | @snoc prior earlier name type body fresh ih =>
      exact ih.trans (Signature.extends_insert_of_absent prior.signature.declarations
        name (HOLDefinitionAdmission.entry prior.signature body)
        (prior_name_absent prior.signature name fresh))

/-- The prefix inclusion is operational as well as semantic: no earlier
declared root step disappears from the final native signature. -/
theorem CheckedPrefix.retains_root_step
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {n : Nat} {left right : Tower.Tm n}
    (step : initial.signature.declarations.computation.step left right) :
    final.signature.declarations.computation.step left right :=
  chain.declarations_extend.computation step

/-- The native computation relation retains *all* earlier roots, including
δ reductions of previous definitions and inherited base computations. -/
theorem CheckedPrefix.retains_native_root_step
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {n : Nat} {left right : Tower.Tm n}
    (step : initial.signature.rules.computation.step left right) :
    final.signature.rules.computation.step left right := by
  have extension := chain.declarations_extend
  change RootStep Tower.rules initial.signature.declarations n left right at step
  change RootStep Tower.rules final.signature.declarations n left right
  cases step with
  | inherited core => exact .inherited core
  | delta selected => exact .delta (extension.valueOf selected)
  | declared licensed => exact .declared (extension.computation licensed)

/-- Any retained dependent typing derivation over the earlier native rules
remains valid after the entire checked prefix, including derivations that
refer to definitions installed in an earlier part of the chain. -/
theorem CheckedPrefix.retains_typing
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing initial.signature.rules context term type) :
    Typing final.signature.rules context term type :=
  typed.monoSignature chain.declarations_extend

/-- Every earlier source term retains its meaning through every checked
definition, not only through the immediately following one. -/
theorem CheckedPrefix.denote_closed_embed
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {type : HOL.Ty Base}
    (term : HOL.Term initial.Const [] type) :
    HEq (final.model.denote (chain.embed term) (fun index => nomatch index))
      (initial.model.denote term (fun index => nomatch index)) := by
  induction chain with
  | nil => rfl
  | @snoc prior earlier name type body fresh ih =>
      have old := prior.model.definitionExtension_embed body
        (earlier.embed term) (fun index => nomatch index)
      exact (heq_of_eq old).trans ih

/-- Every earlier closed HOL formula has exactly the same truth value after
the entire definition prefix. This retains source axioms and theorems as
distinct source claims; it does not turn an axiom into a proved theorem. -/
theorem CheckedPrefix.models_embed
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    (formula : HOL.ClosedFormula initial.Const) :
    final.model.models (chain.embed formula) ↔ initial.model.models formula := by
  have same := eq_of_heq (chain.denote_closed_embed formula)
  exact Iff.of_eq (congrArg ULift.down same)

/-- The unchanged native translation of any earlier closed term denotes its
source value in the final definition-respecting model. The separate
`denote_closed_embed` theorem relates this value to the initial model. -/
theorem CheckedPrefix.prior_closed_term_denotes
    {Base : Type u} {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final)
    {type : HOL.Ty Base} (term : HOL.Term initial.Const [] type)
    (gamma : HOL.Ctx Base) :
    NativeHOLSignatureDenotation.Denotes final.signature final.model
      (gamma := gamma) (type := type)
      (liftClosed (translate initial.signature term))
      (fun _ => final.model.denote (chain.embed term) (fun index => nomatch index)) := by
  have meaning := NativeHOLImpredicativeDenotation.translate_closed_denotes
    final.signature final.model (chain.embed term) gamma
  rw [chain.translate_embed term] at meaning
  exact meaning

#print axioms CheckedPrefix.denote_closed_embed
#print axioms CheckedPrefix.models_embed
#print axioms CheckedPrefix.translate_embed
#print axioms CheckedPrefix.declarations_extend
#print axioms CheckedPrefix.retains_root_step
#print axioms CheckedPrefix.retains_native_root_step
#print axioms CheckedPrefix.retains_typing
#print axioms CheckedPrefix.prior_closed_term_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionPrefix
