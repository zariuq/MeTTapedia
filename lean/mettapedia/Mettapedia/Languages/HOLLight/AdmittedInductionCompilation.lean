import Mettapedia.GSLT.LanguageDef.AdmittedContainerInduction
import Mettapedia.Languages.HOLLight.InterpretedCompilation

/-!
# Primitive certificate construction for admitted-source induction

The source constructor cases, membership evidence and constructor law feed
the existing admitted induction program. Its constructed layer closure is
compiled by the ordinary HOL primitive compiler. This interface constructs
forward certificates; source-reader adequacy and reflection are separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedInductionCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.TypeTheory
open HOL Mettapedia.GSLT.LanguageDef
open AdmittedContainerHOL IndexedContainerPositionTerms IndexedPolynomial.Description

universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
    {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : HOL.Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → HOL.Term Const Γ reading.number)
    (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    {space : Ty Base} (bottom : HOL.Term Const Γ space)
    (constructor : HOL.Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    {assumptions : List (HOL.Formula Const Γ)}
    (motive : HOL.Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement constructor))
    (cases : ScopedSourceIndexedCases block registered guards rho numeral constructor zero successor bottom
      (PredicateFixedPoint.intersection
        (recursiveSignature block registered (guards := guards) rho numeral zero successor bottom constructor).least
        (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructor) motive))
      motive assumptions)
    (value : HOL.Term Const Γ space) (index : HOL.Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions (.app
        (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottom constructor) value) index))
    (interpretation : HOL.TermInterpretation Base Const AtomicTy Symbol)

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def compile
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (casesFree :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottom constructor
      ∀ {Ξ : Ctx Base} (images : HOL.Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree)
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute interpretation.types)))
    (origin : ProofExecution.Origin) :
    RetainedCompilation.Compiled emptyAxiomPolicy names
      ((assumptions.map interpretation.term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (interpretation.term (.app (.app motive value) index))) :=
  InterpretedCompilation.compile interpretation
    (memberInductionFromSourceCases block registered guards rho numeral constructor zero successor bottom
      motive injectivity cases value index member)
    (memberInductionFromSourceCases_free block registered guards rho numeral constructor zero successor bottom
      motive injectivity cases value index member injectivityFree casesFree memberFree)
    names origin

theorem compile_conclusion
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (casesFree :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottom constructor
      ∀ {Ξ : Ctx Base} (images : HOL.Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree)
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute interpretation.types)))
    (origin : ProofExecution.Origin) :
    (compile block registered guards rho numeral zero successor bottom constructor motive injectivity cases
      value index member interpretation injectivityFree casesFree memberFree names origin).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical names
        (ImpredicativeConnectives.expand (interpretation.term (.app (.app motive value) index))) :=
  (compile block registered guards rho numeral zero successor bottom constructor motive injectivity cases
    value index member interpretation injectivityFree casesFree memberFree names origin).conclusion_exact

#print axioms compile
#print axioms compile_conclusion

end Mettapedia.Languages.HOLLight.AdmittedInductionCompilation
