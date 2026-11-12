import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLParallelDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedDisjunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLOccurrenceCoding

/-!
# Exact readback and meanings of the loaded parallel operations

Independent typed bodies are checked against the actual received defining
equations. Their disjunction uses the already interpreted source connective.
The meaning theorem applies to every full-domain model of the extended
definition cache, whose existence follows from conservative replay.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelBodies

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLBodySyntax HOLModelsBody

namespace Store

abbrev operationType : HOL.Ty AtomicTy := .arr storeType (.arr storeType storeType)

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("left", storeType), ("right", storeType), ("x", termType), ("y", termType)]
    (apps (constant HOLLoadedDisjunction.symbol)
      [apps (varTerm "left") [varTerm "x", varTerm "y"],
       apps (varTerm "right") [varTerm "x", varTerm "y"]])

theorem body_typed : (checkClosed operationType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol operationType := (checkClosed operationType sourceBody).get body_typed

theorem constant_available :
    (List.lookup "tc_parallel_store" HOLParallelDefinitions.received.symbols.constants).isSome = true := by
  decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_parallel_store" HOLParallelDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol operationType := .constant constant (Ty.fromHOL operationType) (Ty.toHOL_fromHOL operationType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 19 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition :
    ExactFormulaReadback.ReadFact HOLParallelDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 19 definition).get definition_readable

end Store

namespace Present

open HOLOccurrenceCoding

abbrev operationType : HOL.Ty AtomicTy := .arr setType (.arr setType setType)

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("left", setType), ("right", setType), ("occ", occurrenceType)]
    (apps (constant HOLLoadedDisjunction.symbol)
      [apps (varTerm "left") [varTerm "occ"], apps (varTerm "right") [varTerm "occ"]])

theorem body_typed : (checkClosed operationType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol operationType := (checkClosed operationType sourceBody).get body_typed

theorem constant_available :
    (List.lookup "tc_parallel_present" HOLParallelDefinitions.received.symbols.constants).isSome = true := by
  decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_parallel_present" HOLParallelDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol operationType := .constant constant (Ty.fromHOL operationType) (Ty.toHOL_fromHOL operationType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 20 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition :
    ExactFormulaReadback.ReadFact HOLParallelDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 20 definition).get definition_readable

end Present

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLParallelDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include equations in
theorem original_equations :
    ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula :=
  fun fact member => equations fact (HOLParallelDefinitions.original_cache_included member)

include full equations in
theorem store_meaning (left right : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (x y : HOL.Ty.denote.{0,w+1} model.Carrier termType) :
    model.constDen Store.symbol left right x y = ULift.up ((left x y).down ∨ (right x y).down) := by
  rw [ExactReadbackCache.definition_value model full equations Store.symbol Store.body Store.readDefinition]
  simp [Store.body, checkClosed, Store.sourceBody, lambdas, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  exact HOLLoadedDisjunction.operational_meaning model full (original_equations model equations) _ _

include full equations in
theorem present_meaning (left right : HOL.Ty.denote.{0,w+1} model.Carrier HOLOccurrenceCoding.setType)
    (occ : HOL.Ty.denote.{0,w+1} model.Carrier HOLOccurrenceCoding.occurrenceType) :
    model.constDen Present.symbol left right occ = ULift.up ((left occ).down ∨ (right occ).down) := by
  rw [ExactReadbackCache.definition_value model full equations Present.symbol Present.body Present.readDefinition]
  simp [Present.body, checkClosed, Present.sourceBody, lambdas, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  exact HOLLoadedDisjunction.operational_meaning model full (original_equations model equations) _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelBodies
