import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLBodySyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Disjunction in the actual received Boolean definition history

The loaded connective has its impredicative defining body. Exact readback
and the already established universal/implication meanings identify its
denotation, without adding a Boolean interpretation assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedDisjunction

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

abbrev connectiveType : HOL.Ty AtomicTy := .arr .prop (.arr .prop .prop)

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("p", .prop), ("q", .prop)]
    (all "r" .prop (implication (implication (varTerm "p") (varTerm "r"))
      (implication (implication (varTerm "q") (varTerm "r")) (varTerm "r"))))

theorem body_typed : (checkClosed connectiveType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol connectiveType := (checkClosed connectiveType sourceBody).get body_typed

theorem constant_available :
    (List.lookup "\\/" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "\\/" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol connectiveType := .constant constant (Ty.fromHOL connectiveType) (Ty.toHOL_fromHOL connectiveType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 5 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 5 definition).get definition_readable

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

theorem denote_body (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (p q : HOL.Ty.denote.{0,w+1} model.Carrier .prop) :
    model.denote body (fun index => nomatch index) p q = ULift.up (p.down ∨ q.down) := by
  simp [body, checkClosed, sourceBody, lambdas, all, implication, apps, HOLBodySyntax.constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  rw [booleans.universal]
  simp only [booleans.implication]
  apply ULift.ext
  apply propext
  constructor
  · intro holds
    exact holds (ULift.up (p.down ∨ q.down)) (full _ _) Or.inl Or.inr
  · intro holds r _ first second
    exact holds.elim first second

variable (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem constant_value : model.constDen symbol = model.denote body (fun index => nomatch index) :=
  HOLLoadedReadback.definition_value model full equations symbol body readDefinition

include full equations in
theorem operational_meaning (p q : HOL.Ty.denote.{0,w+1} model.Carrier .prop) :
    model.constDen symbol p q = ULift.up (p.down ∨ q.down) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full) p q

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedDisjunction
