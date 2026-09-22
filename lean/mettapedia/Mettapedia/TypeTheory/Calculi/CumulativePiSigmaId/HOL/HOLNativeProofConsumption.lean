import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution

/-!
# Consuming actual compiled evidence in another retained HOL proof

The provider is a retained proof with its own assumptions. The consumer is
another retained proof, with one explicit assumption supplied by the provider's
actual compiled term. Both pass through the existing compiler. Native typing
and displayed denotation compose without recompiling the provider, inventing
its assumption, or constructing an independent proof of the conclusion.

This is a native proof-attachment law. It retains the two source trees and
their connecting formula; it does not claim source-tree cut elimination or a
byte-level verification of the C implementation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofConsumption

open Presentation Mettapedia.Logic FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler

universe u v w u' v'

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Compose two invocations of the one compiler, retaining its actual result.
This is a staging driver, not another recursive proof compiler. -/
def compile? (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) := do
  let provided ← compile signature proofName operations provider objects hypotheses
  compile signature proofName operations consumer objects (fun _ => provided)

/-- The actual successful provider compilation supplies the consumer's premise. -/
theorem typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {context : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (objectsTyped : GenericTyping.Objects signature context objects)
    (hypothesesTyped : GenericTyping.Hypotheses signature operations context objects hypotheses)
    {provided returned : Tower.Tm n}
    (providerCompiled : compile signature proofName operations provider objects hypotheses = some provided)
    (consumerCompiled : compile signature proofName operations consumer objects
      (fun _ => provided) = some returned) :
    ∃ code, represent signature conclusion = some code ∧
      FormationSensitive.Typing operations.target context returned
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  obtain ⟨code, represented, providedTyped⟩ :=
    GenericTyping.compile_typed signature proofName operations provider
      objectsTyped hypothesesTyped providerCompiled
  have consumerHypotheses : GenericTyping.Hypotheses signature operations context objects
      (delta := [premise]) (fun _ => provided) := by
    intro index
    have zero : index = 0 := Fin.eq_zero index
    subst index
    exact ⟨code, represented, providedTyped⟩
  exact GenericTyping.compile_typed signature proofName operations consumer
    objectsTyped consumerHypotheses consumerCompiled

/-- The same returned term denotes the consumer conclusion in the same model. -/
theorem denotes (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {provided returned : Tower.Tm n}
    (providerCompiled : compile signature proofName operations provider objects hypotheses = some provided)
    (consumerCompiled : compile signature proofName operations consumer objects
      (fun _ => provided) = some returned)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state returned conclusion := by
  have providedMeaning := GenericSemantics.compile_denotes signature proofName operations
    semantics provider providerCompiled state hypothesesMeaning
  have consumerHypotheses : GenericSemantics.Hypotheses semantics state
      (delta := [premise]) (fun _ => provided) := by
    intro index
    have zero : index = 0 := Fin.eq_zero index
    subst index
    exact providedMeaning
  exact GenericSemantics.compile_denotes signature proofName operations
    semantics consumer consumerCompiled state consumerHypotheses

/-- Successful consumption has the represented conclusion's native type. -/
theorem compile_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {context : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (objectsTyped : GenericTyping.Objects signature context objects)
    (hypothesesTyped : GenericTyping.Hypotheses signature operations context objects hypotheses)
    {returned : Tower.Tm n}
    (success : compile? signature proofName operations provider consumer objects hypotheses = some returned) :
    ∃ code, represent signature conclusion = some code ∧
      FormationSensitive.Typing operations.target context returned
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  cases provided : compile signature proofName operations provider objects hypotheses with
  | none => simp [compile?, provided] at success
  | some actual =>
      simp only [compile?, provided] at success
      exact typed signature proofName operations provider consumer objectsTyped hypothesesTyped
        provided success

/-- Successful consumption denotes that same conclusion in the same model. -/
theorem compile_denotes (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {returned : Tower.Tm n}
    (success : compile? signature proofName operations provider consumer objects hypotheses = some returned)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state returned conclusion := by
  cases provided : compile signature proofName operations provider objects hypotheses with
  | none => simp [compile?, provided] at success
  | some actual =>
      simp only [compile?, provided] at success
      exact denotes signature proofName operations semantics provider consumer provided success
        state hypothesesMeaning

/-- A type-specialized source provider feeds a type-specialized consumer
through the existing compiler. Both inputs are the actual transformed proof
trees; the returned dependent term has the represented specialized conclusion. -/
theorem specialized_compile_typed
    {Base' : Type u'} {Const' : HOL.Ty Base' → Type v'}
    (specialize : Base → HOL.Ty Base')
    (constants : ∀ {A}, Const A → Const' (HOL.Ty.substitute specialize A))
    (signature : LogicalSignature Base' Const') (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {context : Tower.Ctx n}
    {objects : Sub Tower.Head (gamma.map (HOL.Ty.substitute specialize)).length n}
    {hypotheses : Fin (delta.map (HOL.mapTypes specialize constants)).length → Tower.Tm n}
    (objectsTyped : GenericTyping.Objects signature context objects)
    (hypothesesTyped : GenericTyping.Hypotheses signature operations context objects hypotheses)
    {returned : Tower.Tm n}
    (success : compile? signature proofName operations
      (provider.mapTypes specialize constants) (consumer.mapTypes specialize constants)
      objects hypotheses = some returned) :
    ∃ code, represent signature (HOL.mapTypes specialize constants conclusion) = some code ∧
      FormationSensitive.Typing operations.target context returned
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) :=
  compile_typed signature proofName operations
    (provider.mapTypes specialize constants) (consumer.mapTypes specialize constants)
    objectsTyped hypothesesTyped success

/-- The same specialized compiled result has the target interpretation's
meaning, with the target algebra and source assumptions supplied explicitly. -/
theorem specialized_compile_denotes
    {Base' : Type u'} {Const' : HOL.Ty Base' → Type v'}
    (specialize : Base → HOL.Ty Base')
    (constants : ∀ {A}, Const A → Const' (HOL.Ty.substitute specialize A))
    (signature : LogicalSignature Base' Const') (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : GenericSemantics.Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} {objects : Sub Tower.Head (gamma.map (HOL.Ty.substitute specialize)).length n}
    {hypotheses : Fin (delta.map (HOL.mapTypes specialize constants)).length → Tower.Tm n}
    {returned : Tower.Tm n}
    (success : compile? signature proofName operations
      (provider.mapTypes specialize constants) (consumer.mapTypes specialize constants)
      objects hypotheses = some returned)
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state returned (HOL.mapTypes specialize constants conclusion) :=
  compile_denotes signature proofName operations semantics
    (provider.mapTypes specialize constants) (consumer.mapTypes specialize constants)
    success state hypothesesMeaning

theorem unsupported_provider (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {premise conclusion : HOL.Formula Const gamma}
    (provider : HOL.ProofSyntax Const delta premise)
    (consumer : HOL.ProofSyntax Const [premise] conclusion)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n)
    (unsupported : compile signature proofName operations provider objects hypotheses = none) :
    compile? signature proofName operations provider consumer objects hypotheses = none := by
  simp [compile?, unsupported]

/-- Supply the retained premise to a new continuation, producing a new conclusion. -/
def continuation {gamma : HOL.Ctx Base} (premise conclusion : HOL.Formula Const gamma) :
    HOL.ProofSyntax Const [premise] (.imp (.imp premise conclusion) conclusion) :=
  .impI (.impE (.hyp 0) (.hyp 1))

#print axioms typed
#print axioms denotes
#print axioms compile_typed
#print axioms compile_denotes
#print axioms specialized_compile_typed
#print axioms specialized_compile_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeProofConsumption
