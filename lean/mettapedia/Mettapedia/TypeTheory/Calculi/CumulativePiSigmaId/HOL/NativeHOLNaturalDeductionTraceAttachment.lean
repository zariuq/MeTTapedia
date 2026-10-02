import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceLambdaSemantics

/-!
# The natural-deduction compiler lands in the trace lambda fragment

This module runs the existing HOL natural-deduction traversal directly into
the typed variable/lambda/application fragment and proves that erasing its
result is exactly the term emitted by the existing native compiler.  The
result covers hypotheses, implication introduction/elimination and universal
introduction.  Universal elimination is included whenever its represented
object argument is itself made only from native variables, lambdas and
applications; all other object syntax is rejected explicitly by `ofTower?`.

The theorem is an attachment to the actual compiler, not a second example
whose output merely resembles it.  It deliberately stops short of a semantic
soundness claim for the uniform-list signature: that requires trace codes for
its three base sorts and a proof that represented object terms denote their
source meanings.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLNaturalDeductionTraceAttachment

open Presentation Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily)

namespace Trace

open NativeTraceLambdaSemantics

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Formula (gamma : SourceContext) := HOL.Formula Symbol gamma

def weakenHypotheses {k n : Nat}
    (hypotheses : Fin k → NativeTraceLambdaSemantics.Tm n) :
    Fin (k + 1) → NativeTraceLambdaSemantics.Tm (n + 1) :=
  Fin.cases (.var 0) (fun i => (hypotheses i).rename wk)

def weakenTowerHypotheses {k n : Nat} (hypotheses : Fin k → Tower.Tm n) :
    Fin (k + 1) → Tower.Tm (n + 1) :=
  Fin.cases (.var 0) (fun i => Presentation.rename wk (hypotheses i))

@[simp] theorem weakenHypotheses_erase {k n : Nat}
    (hypotheses : Fin k → NativeTraceLambdaSemantics.Tm n) (i : Fin (k + 1)) :
    (weakenHypotheses hypotheses i).erase =
      weakenTowerHypotheses (fun j => (hypotheses j).erase) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact NativeTraceLambdaSemantics.Tm.erase_rename wk (hypotheses j)

/-- The existing proof traversal, now with an intrinsically delimited target.
The only partiality added beyond the source compiler is the honest recognition
boundary for an object supplied to universal elimination. -/
def compile {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Fin gamma.length → NativeTraceLambdaSemantics.Tm n)
    (hypotheses : Fin delta.length → NativeTraceLambdaSemantics.Tm n) :
    Option (NativeTraceLambdaSemantics.Tm n) :=
  match source with
  | .hyp occurrence => some (hypotheses occurrence)
  | @HOL.ProofSyntax.impI _ _ gamma delta p _ body => do
      let _ ← HOLNaturalDeductionNativeTranslation.represent p
      let nativeBody ← compile body (fun i => (objects i).rename wk)
        (weakenHypotheses hypotheses)
      pure (.lam nativeBody)
  | .impE function argument => do
      let nativeFunction ← compile function objects hypotheses
      let nativeArgument ← compile argument objects hypotheses
      pure (.app nativeFunction nativeArgument)
  | .allI body => do
      let nativeBody ← compile body (liftSubTm objects)
        (fun i => (hypotheses (i.cast (by simp [HOL.weakenHyps]))).rename wk)
      pure (.lam nativeBody)
  | .allE term function => do
      let representedArgument ← HOLNaturalDeductionNativeTranslation.represent term
      let nativeArgument := Presentation.subst (fun i => (objects i).erase) representedArgument
      let traceArgument ← NativeTraceLambdaSemantics.Tm.ofTower? nativeArgument
      let nativeFunction ← compile function objects hypotheses
      pure (.app nativeFunction traceArgument)
  | _ => none

/-- Exact attachment to the pre-existing native compiler.  No denotation is
read from that compiler: both functions recurse over the retained proof, and
this theorem shows their independently constructed syntax commutes with
erasure. -/
theorem compile_erases {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Fin gamma.length → NativeTraceLambdaSemantics.Tm n)
    (hypotheses : Fin delta.length → NativeTraceLambdaSemantics.Tm n)
    {result : NativeTraceLambdaSemantics.Tm n}
    (success : compile source objects hypotheses = some result) :
    HOLNaturalDeductionNativeTranslation.compile source
        (fun i => (objects i).erase) (fun i => (hypotheses i).erase) = some result.erase := by
  induction source generalizing n result with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst result
      rfl
  | @impI gamma delta p q body inductionHypothesis =>
      cases represented : HOLNaturalDeductionNativeTranslation.represent p with
      | none => simp [compile, represented] at success
      | some code =>
          cases compiled : compile body (fun i => (objects i).rename wk)
              (weakenHypotheses hypotheses) with
          | none => simp [compile, represented, compiled] at success
          | some bodyTerm =>
              simp [compile, represented, compiled] at success
              subst result
              have bodyAttached := inductionHypothesis
                (fun i => (objects i).rename wk)
                (weakenHypotheses hypotheses) compiled
              have bodyAttached' :
                  HOLNaturalDeductionNativeTranslation.compile body
                    (fun i => Presentation.rename wk (objects i).erase)
                    (fun i => weakenTowerHypotheses
                      (fun j => (hypotheses j).erase) i) =
                    some bodyTerm.erase := by
                simpa only [NativeTraceLambdaSemantics.Tm.erase_rename,
                  weakenHypotheses_erase] using bodyAttached
              have bodyAttachedRaw :
                  HOLNaturalDeductionNativeTranslation.compile body
                    (fun i => Presentation.rename wk (objects i).erase)
                    (Fin.cases (.var 0)
                      (fun i => Presentation.rename wk (hypotheses i).erase)) =
                    some bodyTerm.erase := by
                convert bodyAttached' using 1
                all_goals rfl
              simp [HOLNaturalDeductionNativeTranslation.compile, represented,
                bodyAttachedRaw,
                NativeTraceLambdaSemantics.Tm.erase]
  | impE function argument functionInduction argumentInduction =>
      cases functionCompiled : compile function objects hypotheses with
      | none => simp [compile, functionCompiled] at success
      | some functionTerm =>
          cases argumentCompiled : compile argument objects hypotheses with
          | none => simp [compile, functionCompiled, argumentCompiled] at success
          | some argumentTerm =>
              simp [compile, functionCompiled, argumentCompiled] at success
              subst result
              have functionAttached := functionInduction objects hypotheses functionCompiled
              have argumentAttached := argumentInduction objects hypotheses argumentCompiled
              simp [HOLNaturalDeductionNativeTranslation.compile,
                functionAttached, argumentAttached, NativeTraceLambdaSemantics.Tm.erase]
  | @allI gamma delta type phi body inductionHypothesis =>
      cases compiled : compile body (liftSubTm objects)
          (fun i => (hypotheses (i.cast (by simp [HOL.weakenHyps]))).rename wk) with
      | none => simp [compile, compiled] at success
      | some bodyTerm =>
          simp [compile, compiled] at success
          subst result
          have bodyAttached := inductionHypothesis (liftSubTm objects)
            (fun i => (hypotheses (i.cast (by simp [HOL.weakenHyps]))).rename wk) compiled
          have bodyAttached' :
              HOLNaturalDeductionNativeTranslation.compile body
                (liftSub (fun i => (objects i).erase))
                (fun i => Presentation.rename wk
                  (hypotheses (i.cast (by simp [HOL.weakenHyps]))).erase) =
                some bodyTerm.erase := by
            have attached := bodyAttached
            simp only [erase_liftSubTm,
              NativeTraceLambdaSemantics.Tm.erase_rename] at attached
            exact attached
          simp [HOLNaturalDeductionNativeTranslation.compile, bodyAttached',
            NativeTraceLambdaSemantics.Tm.erase]
  | allE sourceArgument function inductionHypothesis =>
      cases represented : HOLNaturalDeductionNativeTranslation.represent sourceArgument with
      | none => simp [compile, represented] at success
      | some representedArgument =>
          let nativeArgument := Presentation.subst
            (fun i => (objects i).erase) representedArgument
          cases recognized : NativeTraceLambdaSemantics.Tm.ofTower? nativeArgument with
          | none => simp [compile, represented, nativeArgument, recognized] at success
          | some traceArgument =>
              have erasedArgument : traceArgument.erase = nativeArgument :=
                NativeTraceLambdaSemantics.Tm.ofTower?_sound recognized
              cases compiled : compile function objects hypotheses with
              | none =>
                  simp [compile, represented, compiled] at success
              | some functionTerm =>
                  simp [compile, represented, nativeArgument, recognized, compiled] at success
                  subst result
                  have functionAttached := inductionHypothesis objects hypotheses compiled
                  simp [HOLNaturalDeductionNativeTranslation.compile, represented,
                    functionAttached, nativeArgument, erasedArgument,
                    NativeTraceLambdaSemantics.Tm.erase]
  | _ => simp [compile] at success

def implicationIdentity {gamma : SourceContext} (p : Formula gamma) :
    HOL.ProofSyntax Symbol [] (.imp p p) := .impI (.hyp 0)

theorem implicationIdentity_attached {gamma : SourceContext} (p : Formula gamma)
    {code : Tower.Tm gamma.length}
    (represented : HOLNaturalDeductionNativeTranslation.represent p = some code)
    {n : Nat} (objects : Fin gamma.length → NativeTraceLambdaSemantics.Tm n) :
    compile (implicationIdentity p) objects Fin.elim0 = some (.lam (.var 0)) ∧
      HOLNaturalDeductionNativeTranslation.compile (implicationIdentity p)
        (fun i => (objects i).erase) Fin.elim0 =
          some (NativeTraceLambdaSemantics.Tm.lam (.var 0)).erase := by
  constructor
  · simp [implicationIdentity, compile, represented, weakenHypotheses]
  · apply compile_erases (source := implicationIdentity p) (objects := objects)
      (hypotheses := fun i => Fin.elim0 i)
    simp [implicationIdentity, compile, represented, weakenHypotheses]

/-- The exact syntax emitted for implication identity denotes the actual trace
identity section.  This is independent of both the HOL proof interpreter and
the native compiler: it follows from variable projection and trace lambda. -/
theorem implicationIdentity_denotes {n : Nat}
    (context : NativeTraceLambdaSemantics.Context n)
    (a : SetFamily context.Environment) :
    NativeTraceLambdaSemantics.Denotes context (.lam (.var 0))
      (ZFSetTraceContextual.piFamily a (fun point => a point.1))
      (ZFSetTraceContextual.lam (fun point => point.2)) := by
  exact NativeTraceLambdaSemantics.Denotes.lam
    (NativeTraceLambdaSemantics.Denotes.var (context.snoc a) 0)

#print axioms compile_erases
#print axioms implicationIdentity_attached
#print axioms implicationIdentity_denotes

end Trace
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLNaturalDeductionTraceAttachment
