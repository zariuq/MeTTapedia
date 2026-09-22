import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompiler

/-!
# Displayed semantics of the generic HOL proof compiler

The recursive compiler is an initial fold over retained HOL proof syntax.
Its semantic correctness therefore depends on two context-extension actions
and on local soundness of the operations emitted at each proof constructor.
This module packages exactly that displayed algebra and proves the recursive
fusion theorem once.

The semantic state is indexed by the actual source-object substitution.  A
proof assumption extends only the native target scope, whereas a quantified
object extends both the source telescope and target scope.  Keeping those two
actions distinct prevents a proof variable from being mistaken for an object
variable and makes weakening an explicit law rather than an implicit cast.

This is an interface theorem, not by itself a model: a useful instance must
define `Denotes` independently and discharge every local law.  In particular,
choosing the constantly true relation would establish no adequacy result.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace GenericSemantics

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- A displayed semantic algebra over one lawful compiler operation algebra.
`State objects` contains the target semantic context, source valuation, and
the proof that the native object substitution realizes that valuation. -/
structure Algebra (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName) where
  State : {gamma : HOL.Ctx Base} → {n : Nat} →
    Sub Tower.Head gamma.length n → Type w
  Denotes : {gamma : HOL.Ctx Base} → {n : Nat} →
    {objects : Sub Tower.Head gamma.length n} →
    State objects → Tower.Tm n → HOL.Formula Const gamma → Prop

  proofExtension : {gamma : HOL.Ctx Base} → {n : Nat} →
    {objects : Sub Tower.Head gamma.length n} →
    State objects → (premise : HOL.Formula Const gamma) →
    State (fun index => rename wk (objects index))
  objectExtension : {gamma : HOL.Ctx Base} → {n : Nat} →
    {objects : Sub Tower.Head gamma.length n} →
    State objects → (type : HOL.Ty Base) →
    State (gamma := type :: gamma) (liftSub objects)

  proofVariable : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n}
      (state : State objects) (premise : HOL.Formula Const gamma),
    Denotes (proofExtension state premise) (.var 0) premise
  proofWeakening : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n}
      {formula : HOL.Formula Const gamma}
      (state : State objects) (premise : HOL.Formula Const gamma),
    Denotes state term formula →
      Denotes (proofExtension state premise) (rename wk term) formula
  objectWeakening : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n}
      {formula : HOL.Formula Const gamma}
      (state : State objects) (type : HOL.Ty Base),
    Denotes state term formula →
      Denotes (objectExtension state type) (rename wk term)
        (HOL.weaken (σ := type) formula)

  implicationIntro : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n}
      {premise conclusion : HOL.Formula Const gamma}
      {premiseCode : Tower.Tm gamma.length} {body : Tower.Tm (n + 1)}
      (state : State objects),
    represent signature premise = some premiseCode →
    Denotes (proofExtension state premise) body conclusion →
    Denotes state (.lam body) (.imp premise conclusion)
  implicationElim : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n}
      {premise conclusion : HOL.Formula Const gamma}
      {function argument : Tower.Tm n} (state : State objects),
    Denotes state function (.imp premise conclusion) →
    Denotes state argument premise →
    Denotes state (.app function argument) conclusion
  universalIntro : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty Base}
      {formula : HOL.Formula Const (type :: gamma)} {body : Tower.Tm (n + 1)}
      (state : State objects),
    Denotes (objectExtension state type) body formula →
    Denotes state (.lam body) (.all formula)
  universalElim : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty Base}
      {formula : HOL.Formula Const (type :: gamma)}
      {argument : HOL.Term Const gamma type}
      {argumentCode : Tower.Tm gamma.length} {function : Tower.Tm n}
      (state : State objects),
    represent signature argument = some argumentCode →
    Denotes state function (.all formula) →
    Denotes state (.app function (subst objects argumentCode))
      (HOL.instantiate argument formula)

  reflexivity : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty Base}
      {term : HOL.Term Const gamma type} {code : Tower.Tm gamma.length}
      {out : Tower.Tm n} (state : State objects),
    represent signature term = some code →
    operations.raw.reflexivity = some out →
    Denotes state out (term.eq term)
  symmetry : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty Base}
      {left right : HOL.Term Const gamma type}
      {leftCode rightCode : Tower.Tm gamma.length}
      {comparison out : Tower.Tm n} (state : State objects),
    represent signature left = some leftCode →
    represent signature right = some rightCode →
    operations.raw.symmetry type (subst objects leftCode) comparison = some out →
    Denotes state comparison (left.eq right) →
    Denotes state out (right.eq left)
  transitivity : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty Base}
      {left middle right : HOL.Term Const gamma type}
      {leftCode middleCode rightCode : Tower.Tm gamma.length}
      {first second out : Tower.Tm n} (state : State objects),
    represent signature left = some leftCode →
    represent signature middle = some middleCode →
    represent signature right = some rightCode →
    operations.raw.transitivity type (subst objects leftCode) first second = some out →
    Denotes state first (left.eq middle) →
    Denotes state second (middle.eq right) →
    Denotes state out (left.eq right)
  propositionExtensionality : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n}
      {left right : HOL.Formula Const gamma}
      {leftCode rightCode : Tower.Tm gamma.length}
      {forward backward out : Tower.Tm n} (state : State objects),
    represent signature left = some leftCode →
    represent signature right = some rightCode →
    operations.raw.propositionExtensionality
      (subst objects leftCode) (subst objects rightCode) forward backward = some out →
    Denotes state forward (.imp left right) →
    Denotes state backward (.imp right left) →
    Denotes state out (left.eq right)
  propositionForward : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n}
      {left right : HOL.Formula Const gamma}
      {comparison out : Tower.Tm n} (state : State objects),
    operations.raw.propositionForward comparison = some out →
    Denotes state comparison (left.eq right) →
    Denotes state out (.imp left right)
  functionCongruence : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain result : HOL.Ty Base}
      {function other : HOL.Term Const gamma (.arr domain result)}
      {argument : HOL.Term Const gamma domain}
      {functionCode otherCode argumentCode : Tower.Tm gamma.length}
      {comparison out : Tower.Tm n} (state : State objects),
    represent signature function = some functionCode →
    represent signature other = some otherCode →
    represent signature argument = some argumentCode →
    operations.raw.functionCongruence result (subst objects functionCode)
      (subst objects argumentCode) comparison = some out →
    Denotes state comparison (function.eq other) →
    Denotes state out
      ((HOL.Term.app function argument).eq (HOL.Term.app other argument))
  argumentCongruence : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain result : HOL.Ty Base}
      {function : HOL.Term Const gamma (.arr domain result)}
      {left right : HOL.Term Const gamma domain}
      {functionCode leftCode rightCode : Tower.Tm gamma.length}
      {comparison out : Tower.Tm n} (state : State objects),
    represent signature function = some functionCode →
    represent signature left = some leftCode →
    represent signature right = some rightCode →
    operations.raw.argumentCongruence result (subst objects functionCode)
      (subst objects leftCode) comparison = some out →
    Denotes state comparison (left.eq right) →
    Denotes state out
      ((HOL.Term.app function left).eq (HOL.Term.app function right))
  lambdaCongruence : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty Base}
      {left right : HOL.Term Const (domain :: gamma) codomain}
      {leftCode rightCode : Tower.Tm (domain :: gamma).length}
      {comparison : Tower.Tm (n + 1)} {out : Tower.Tm n}
      (state : State objects),
    represent signature left = some leftCode →
    represent signature right = some rightCode →
    operations.raw.functionExtensionality
      (typeAt signature.types n domain) (typeAt signature.types n codomain)
      (.lam (subst (liftSub objects) leftCode))
      (.lam (subst (liftSub objects) rightCode)) (.lam comparison) = some out →
    Denotes (objectExtension state domain) comparison (left.eq right) →
    Denotes state out ((HOL.Term.lam left).eq (HOL.Term.lam right))
  functionExtensionality : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty Base}
      {function other : HOL.Term Const gamma (.arr domain codomain)}
      {functionCode otherCode : Tower.Tm gamma.length}
      {pointwise out : Tower.Tm n} (state : State objects),
    represent signature function = some functionCode →
    represent signature other = some otherCode →
    operations.raw.functionExtensionality
      (typeAt signature.types n domain) (typeAt signature.types n codomain)
      (subst objects functionCode) (subst objects otherCode) pointwise = some out →
    Denotes state pointwise
      (.all (.eq
        (HOL.Term.app (HOL.weaken function) (.var .vz))
        (HOL.Term.app (HOL.weaken other) (.var .vz)))) →
    Denotes state out (function.eq other)
  beta : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty Base}
      {argument : HOL.Term Const gamma domain}
      {body : HOL.Term Const (domain :: gamma) codomain}
      {argumentCode : Tower.Tm gamma.length}
      {bodyCode : Tower.Tm (domain :: gamma).length}
      {out : Tower.Tm n} (state : State objects),
    represent signature argument = some argumentCode →
    represent signature body = some bodyCode →
    operations.raw.reflexivity = some out →
    Denotes state out
      ((HOL.Term.app (HOL.Term.lam body) argument).eq
        (HOL.instantiate argument body))
  eta : ∀ {gamma : HOL.Ctx Base} {n : Nat}
      {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty Base}
      {function : HOL.Term Const gamma (.arr domain codomain)}
      {functionCode : Tower.Tm gamma.length}
      {pointwise : Tower.Tm (n + 1)} {out : Tower.Tm n}
      (state : State objects),
    represent signature function = some functionCode →
    operations.raw.reflexivity = some pointwise →
    operations.raw.functionExtensionality
      (typeAt signature.types n domain) (typeAt signature.types n codomain)
      (.lam (.app (rename wk (subst objects functionCode)) (.var 0)))
      (subst objects functionCode) (.lam pointwise) = some out →
    Denotes state out
      ((HOL.Term.lam (HOL.Term.app (HOL.weaken function) (.var .vz))).eq function)

/-- Every supplied native hypothesis realizes the corresponding source
formula at one displayed semantic state. -/
def Hypotheses {signature : LogicalSignature Base Const} {proofName : DeclName}
    {operations : Operations signature proofName}
    (semantics : Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : semantics.State objects)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ index, semantics.Denotes state (hypotheses index) (delta.get index)

theorem Hypotheses.prepend
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    {operations : Operations signature proofName}
    (semantics : Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : semantics.State objects)
    {hypotheses : Fin delta.length → Tower.Tm n}
    (meaning : Hypotheses semantics state hypotheses)
    (premise : HOL.Formula Const gamma) :
    Hypotheses semantics (semantics.proofExtension state premise)
      (delta := premise :: delta)
      (Fin.cases (.var 0) (fun index => rename wk (hypotheses index))) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact semantics.proofVariable state premise
  · exact semantics.proofWeakening state premise (meaning prior)

theorem Hypotheses.lift
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    {operations : Operations signature proofName}
    (semantics : Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : semantics.State objects)
    {hypotheses : Fin delta.length → Tower.Tm n}
    (meaning : Hypotheses semantics state hypotheses) (type : HOL.Ty Base) :
    Hypotheses semantics (semantics.objectExtension state type)
      (delta := HOL.weakenHyps (σ := type) delta)
      (fun index => rename wk
        (hypotheses (index.cast (by simp [HOL.weakenHyps])))) := by
  intro index
  let prior : Fin delta.length := index.cast (by simp [HOL.weakenHyps])
  have entry : (HOL.weakenHyps (σ := type) delta).get index =
      HOL.weaken (delta.get prior) := by
    have valid : index.val < delta.length := by
      simpa [HOL.weakenHyps] using index.isLt
    change (delta.map (HOL.weaken (σ := type)))[index.val] =
      HOL.weaken delta[index.val]
    simp only [List.getElem_map]
  rw [entry]
  exact semantics.objectWeakening state type (meaning prior)

/-- Successful compilation preserves every displayed semantic algebra.
Unsupported source constructors cannot satisfy the success premise. -/
theorem compile_denotes
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (semantics : Algebra signature proofName operations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {conclusion : HOL.Formula Const gamma}
    (source : HOL.ProofSyntax Const delta conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile signature proofName operations source objects hypotheses =
      some native) :
    ∀ state : semantics.State objects,
      Hypotheses semantics state hypotheses →
      semantics.Denotes state native conclusion := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst native
      intro state hypothesesMeaning
      exact hypothesesMeaning occurrence
  | @impI gamma delta premise conclusion body inductionHypothesis =>
      cases premiseRepresentation : represent signature premise with
      | none => simp [compile, premiseRepresentation] at success
      | some premiseCode =>
          cases bodyCompilation : compile signature proofName operations body
              (fun index => rename wk (objects index))
              (Fin.cases (.var 0)
                (fun index => rename wk (hypotheses index))) with
          | none => simp [compile, premiseRepresentation, bodyCompilation] at success
          | some bodyCode =>
              simp [compile, premiseRepresentation, bodyCompilation] at success
              subst native
              intro state hypothesesMeaning
              apply semantics.implicationIntro state premiseRepresentation
              exact inductionHypothesis bodyCompilation
                (semantics.proofExtension state premise)
                (Hypotheses.prepend semantics state hypothesesMeaning premise)
  | impE function argument functionInduction argumentInduction =>
      cases functionCompilation : compile signature proofName operations function
          objects hypotheses with
      | none => simp [compile, functionCompilation] at success
      | some functionCode =>
          cases argumentCompilation : compile signature proofName operations argument
              objects hypotheses with
          | none => simp [compile, functionCompilation, argumentCompilation] at success
          | some argumentCode =>
              simp [compile, functionCompilation, argumentCompilation] at success
              subst native
              intro state hypothesesMeaning
              exact semantics.implicationElim state
                (functionInduction functionCompilation state hypothesesMeaning)
                (argumentInduction argumentCompilation state hypothesesMeaning)
  | @allI gamma delta type formula body inductionHypothesis =>
      cases bodyCompilation : compile signature proofName operations body
          (liftSub objects)
          (fun index => rename wk
            (hypotheses (index.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, bodyCompilation] at success
      | some bodyCode =>
          simp [compile, bodyCompilation] at success
          subst native
          intro state hypothesesMeaning
          apply semantics.universalIntro state
          exact inductionHypothesis bodyCompilation
            (semantics.objectExtension state type)
            (Hypotheses.lift semantics state hypothesesMeaning type)
  | @allE gamma delta type formula argument function inductionHypothesis =>
      cases argumentRepresentation : represent signature argument with
      | none => simp [compile, argumentRepresentation] at success
      | some argumentCode =>
          cases functionCompilation : compile signature proofName operations function
              objects hypotheses with
          | none => simp [compile, argumentRepresentation, functionCompilation] at success
          | some functionCode =>
              simp [compile, argumentRepresentation, functionCompilation] at success
              subst native
              intro state hypothesesMeaning
              exact semantics.universalElim state argumentRepresentation
                (inductionHypothesis functionCompilation state hypothesesMeaning)
  | @eqRefl gamma delta type term =>
      cases represented : represent signature term with
      | none => simp [compile, represented] at success
      | some code =>
          cases emitted : (operations.raw.reflexivity : Option (Tower.Tm n)) with
          | none => simp [compile, represented, emitted] at success
          | some out =>
              simp [compile, represented, emitted] at success
              subst native
              intro state _
              exact semantics.reflexivity state represented emitted
  | @eqSymm gamma delta type left right comparison inductionHypothesis =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : represent signature right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile signature proofName operations comparison
                  objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  cases emitted : operations.raw.symmetry type
                      (subst objects leftCode) comparisonCode with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                  | some out =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                      subst native
                      intro state hypothesesMeaning
                      exact semantics.symmetry state leftRepresentation rightRepresentation emitted
                        (inductionHypothesis comparisonCompilation state hypothesesMeaning)
  | @eqTrans gamma delta type left middle right first second firstInduction
      secondInduction =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases middleRepresentation : represent signature middle with
          | none => simp [compile, leftRepresentation, middleRepresentation] at success
          | some middleCode =>
              cases rightRepresentation : represent signature right with
              | none =>
                  simp [compile, leftRepresentation, middleRepresentation,
                    rightRepresentation] at success
              | some rightCode =>
                  cases firstCompilation : compile signature proofName operations first
                      objects hypotheses with
                  | none =>
                      simp [compile, leftRepresentation, middleRepresentation,
                        rightRepresentation, firstCompilation] at success
                  | some firstCode =>
                      cases secondCompilation : compile signature proofName operations second
                          objects hypotheses with
                      | none =>
                          simp [compile, leftRepresentation, middleRepresentation,
                            rightRepresentation, firstCompilation, secondCompilation] at success
                      | some secondCode =>
                          cases emitted : operations.raw.transitivity type
                              (subst objects leftCode) firstCode secondCode with
                          | none =>
                              simp [compile, leftRepresentation, middleRepresentation,
                                rightRepresentation, firstCompilation, secondCompilation,
                                emitted] at success
                          | some out =>
                              simp [compile, leftRepresentation, middleRepresentation,
                                rightRepresentation, firstCompilation, secondCompilation,
                                emitted] at success
                              subst native
                              intro state hypothesesMeaning
                              exact semantics.transitivity state leftRepresentation
                                middleRepresentation rightRepresentation emitted
                                (firstInduction firstCompilation state hypothesesMeaning)
                                (secondInduction secondCompilation state hypothesesMeaning)
  | @eqPropI gamma delta left right forward backward forwardInduction
      backwardInduction =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : represent signature right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases forwardCompilation : compile signature proofName operations forward
                  objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    forwardCompilation] at success
              | some forwardCode =>
                  cases backwardCompilation : compile signature proofName operations backward
                      objects hypotheses with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        forwardCompilation, backwardCompilation] at success
                  | some backwardCode =>
                      cases emitted : operations.raw.propositionExtensionality
                          (subst objects leftCode) (subst objects rightCode)
                          forwardCode backwardCode with
                      | none =>
                          simp [compile, leftRepresentation, rightRepresentation,
                            forwardCompilation, backwardCompilation, emitted] at success
                      | some out =>
                          simp [compile, leftRepresentation, rightRepresentation,
                            forwardCompilation, backwardCompilation, emitted] at success
                          subst native
                          intro state hypothesesMeaning
                          exact semantics.propositionExtensionality state leftRepresentation
                            rightRepresentation emitted
                            (forwardInduction forwardCompilation state hypothesesMeaning)
                            (backwardInduction backwardCompilation state hypothesesMeaning)
  | @eqPropEL gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : represent signature right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile signature proofName operations comparison
                  objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  cases emitted : operations.raw.propositionForward comparisonCode with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                  | some out =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                      subst native
                      intro state hypothesesMeaning
                      exact semantics.propositionForward state emitted
                        (inductionHypothesis comparisonCompilation state hypothesesMeaning)
  | @eqPropER gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : represent signature right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile signature proofName operations comparison
                  objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  cases reversed : operations.raw.symmetry .prop
                      (subst objects leftCode) comparisonCode with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, reversed] at success
                  | some reversedCode =>
                      cases emitted : operations.raw.propositionForward reversedCode with
                      | none =>
                          simp [compile, leftRepresentation, rightRepresentation,
                            comparisonCompilation, reversed, emitted] at success
                      | some out =>
                          simp [compile, leftRepresentation, rightRepresentation,
                            comparisonCompilation, reversed, emitted] at success
                          subst native
                          intro state hypothesesMeaning
                          have reversedMeaning := semantics.symmetry state leftRepresentation
                            rightRepresentation reversed
                            (inductionHypothesis comparisonCompilation state hypothesesMeaning)
                          exact semantics.propositionForward state emitted reversedMeaning
  | @eqApp gamma delta domain result function other argument comparison
      inductionHypothesis =>
      cases functionRepresentation : represent signature function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          cases otherRepresentation : represent signature other with
          | none => simp [compile, functionRepresentation, otherRepresentation] at success
          | some otherCode =>
              cases argumentRepresentation : represent signature argument with
              | none =>
                  simp [compile, functionRepresentation, otherRepresentation,
                    argumentRepresentation] at success
              | some argumentCode =>
                  cases comparisonCompilation : compile signature proofName operations comparison
                      objects hypotheses with
                  | none =>
                      simp [compile, functionRepresentation, otherRepresentation,
                        argumentRepresentation, comparisonCompilation] at success
                  | some comparisonCode =>
                      cases emitted : operations.raw.functionCongruence result
                          (subst objects functionCode) (subst objects argumentCode)
                          comparisonCode with
                      | none =>
                          simp [compile, functionRepresentation, otherRepresentation,
                            argumentRepresentation, comparisonCompilation, emitted] at success
                      | some out =>
                          simp [compile, functionRepresentation, otherRepresentation,
                            argumentRepresentation, comparisonCompilation, emitted] at success
                          subst native
                          intro state hypothesesMeaning
                          exact semantics.functionCongruence state functionRepresentation
                            otherRepresentation argumentRepresentation emitted
                            (inductionHypothesis comparisonCompilation state hypothesesMeaning)
  | @eqAppArg gamma delta domain result function left right comparison
      inductionHypothesis =>
      cases functionRepresentation : represent signature function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          cases leftRepresentation : represent signature left with
          | none => simp [compile, functionRepresentation, leftRepresentation] at success
          | some leftCode =>
              cases rightRepresentation : represent signature right with
              | none =>
                  simp [compile, functionRepresentation, leftRepresentation,
                    rightRepresentation] at success
              | some rightCode =>
                  cases comparisonCompilation : compile signature proofName operations comparison
                      objects hypotheses with
                  | none =>
                      simp [compile, functionRepresentation, leftRepresentation,
                        rightRepresentation, comparisonCompilation] at success
                  | some comparisonCode =>
                      cases emitted : operations.raw.argumentCongruence result
                          (subst objects functionCode) (subst objects leftCode)
                          comparisonCode with
                      | none =>
                          simp [compile, functionRepresentation, leftRepresentation,
                            rightRepresentation, comparisonCompilation, emitted] at success
                      | some out =>
                          simp [compile, functionRepresentation, leftRepresentation,
                            rightRepresentation, comparisonCompilation, emitted] at success
                          subst native
                          intro state hypothesesMeaning
                          exact semantics.argumentCongruence state functionRepresentation
                            leftRepresentation rightRepresentation emitted
                            (inductionHypothesis comparisonCompilation state hypothesesMeaning)
  | @eqLam gamma delta domain codomain left right comparison inductionHypothesis =>
      cases leftRepresentation : represent signature left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : represent signature right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile signature proofName operations comparison
                  (liftSub objects)
                  (fun index => rename wk
                    (hypotheses (index.cast (by simp [HOL.weakenHyps])))) with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  cases emitted : operations.raw.functionExtensionality
                      (typeAt signature.types n domain)
                      (typeAt signature.types n codomain)
                      (.lam (subst (liftSub objects) leftCode))
                      (.lam (subst (liftSub objects) rightCode))
                      (.lam comparisonCode) with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                  | some out =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        comparisonCompilation, emitted] at success
                      subst native
                      intro state hypothesesMeaning
                      exact semantics.lambdaCongruence state leftRepresentation
                        rightRepresentation emitted
                        (inductionHypothesis comparisonCompilation
                          (semantics.objectExtension state domain)
                          (Hypotheses.lift semantics state hypothesesMeaning domain))
  | @funExt gamma delta domain codomain function other pointwise inductionHypothesis =>
      cases functionRepresentation : represent signature function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          cases otherRepresentation : represent signature other with
          | none => simp [compile, functionRepresentation, otherRepresentation] at success
          | some otherCode =>
              cases pointwiseCompilation : compile signature proofName operations pointwise
                  objects hypotheses with
              | none =>
                  simp [compile, functionRepresentation, otherRepresentation,
                    pointwiseCompilation] at success
              | some pointwiseCode =>
                  cases emitted : operations.raw.functionExtensionality
                      (typeAt signature.types n domain)
                      (typeAt signature.types n codomain)
                      (subst objects functionCode) (subst objects otherCode)
                      pointwiseCode with
                  | none =>
                      simp [compile, functionRepresentation, otherRepresentation,
                        pointwiseCompilation, emitted] at success
                  | some out =>
                      simp [compile, functionRepresentation, otherRepresentation,
                        pointwiseCompilation, emitted] at success
                      subst native
                      intro state hypothesesMeaning
                      exact semantics.functionExtensionality state functionRepresentation
                        otherRepresentation emitted
                        (inductionHypothesis pointwiseCompilation state hypothesesMeaning)
  | @beta gamma delta domain codomain argument body =>
      cases argumentRepresentation : represent signature argument with
      | none => simp [compile, argumentRepresentation] at success
      | some argumentCode =>
          cases bodyRepresentation : represent signature body with
          | none => simp [compile, argumentRepresentation, bodyRepresentation] at success
          | some bodyCode =>
              cases emitted : (operations.raw.reflexivity : Option (Tower.Tm n)) with
              | none =>
                  simp [compile, argumentRepresentation, bodyRepresentation, emitted] at success
              | some out =>
                  simp [compile, argumentRepresentation, bodyRepresentation, emitted] at success
                  subst native
                  intro state _
                  exact semantics.beta state argumentRepresentation bodyRepresentation emitted
  | @eta gamma delta domain codomain function =>
      cases functionRepresentation : represent signature function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          let functionTarget := subst objects functionCode
          cases pointwiseEmitted :
              (operations.raw.reflexivity : Option (Tower.Tm (n + 1))) with
          | none => simp [compile, functionRepresentation, pointwiseEmitted] at success
          | some pointwise =>
              cases emitted : operations.raw.functionExtensionality
                  (typeAt signature.types n domain) (typeAt signature.types n codomain)
                  (.lam (.app (rename wk functionTarget) (.var 0))) functionTarget
                  (.lam pointwise) with
              | none =>
                  simp [compile, functionRepresentation, pointwiseEmitted, emitted,
                    functionTarget] at success
              | some out =>
                  simp [compile, functionRepresentation, pointwiseEmitted, emitted,
                    functionTarget] at success
                  subst native
                  intro state _
                  exact semantics.eta state functionRepresentation pointwiseEmitted emitted
  | _ => simp [compile] at success

end GenericSemantics

#print axioms GenericSemantics.Hypotheses.prepend
#print axioms GenericSemantics.Hypotheses.lift
#print axioms GenericSemantics.compile_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
