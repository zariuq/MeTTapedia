import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTraceSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTrace

/-!
# Native residual interchanges in the source trace carrier

The valid values are actual native runs at a fixed initial state. An invalid
sentinel inhabits the raw HOL carrier without inventing a valid event fibre.
The generators are actual canonical residual interchanges and transport
similarities. Their generated relation is the existing native trace relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLNativeTrace

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open HOLTraceSemantics ReferenceBooleanSemantics ModelInterpretation

universe uO uT uH uOcc uS uF uI w

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

abbrev RawRun (source : State) := Option (P.Run source)

def generators {source : State} : RawRun (P := P) source → RawRun (P := P) source → Prop
  | some left, some right => T.Interchange left right ∨ T.Similar left right
  | _, _ => False

theorem some_eqvGen_iff {source : State} (left right : P.Run source) :
    Relation.EqvGen (generators T) (some left) (some right) ↔ T.TraceEquiv source left right := by
  rw [← T.presentedTrace_iff_traceEquiv]
  constructor
  · intro related
    let decode : RawRun (P := P) source → P.Run source := fun value => value.getD (.nil source)
    have preserves (one two : RawRun (P := P) source) (related : generators T one two) :
        T.Interchange (decode one) (decode two) ∨ T.Similar (decode one) (decode two) := by
      cases one <;> cases two <;> first | exact False.elim related | exact related
    exact eqvGen_map decode preserves related
  · intro related
    exact eqvGen_map (fun run : P.Run source => (some run : RawRun (P := P) source))
      (fun _ _ proof => proof) related

theorem invalid_separated {source : State} (run : P.Run source) :
    ¬Relation.EqvGen (generators T) none (some run) := by
  intro related
  have preserves : Respects (generators T) (fun value : RawRun (P := P) source => value.isSome = true) := by
    intro left right generator
    cases left <;> cases right <;> simp_all [generators]
  have impossible := respects_eqvGen preserves related
  simp only [Option.isSome_none, Bool.false_eq_true, Option.isSome_some, iff_true] at impossible

variable (signature : HOLTraceSemantics.Signature) (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def generatorValue {source : State} (code : signature.Carrier model ≃ RawRun (P := P) source) :
    signature.Carrier model → signature.Carrier model → ULift.{w+1} Prop :=
  fun left right => .up (generators T (code left) (code right))

theorem loaded_trace_iff (full : model.FullDomains) (meanings : Meanings model)
    (meaning : model.models signature.meaningFormula) {source : State}
    (code : signature.Carrier model ≃ RawRun (P := P) source) (left right : P.Run source) :
    (signature.traceValue model (generatorValue T signature model code)
      (code.symm (some left)) (code.symm (some right))).down ↔ T.TraceEquiv source left right :=
  (signature.trace_iff_eqvGen model full meanings meaning _ _ _).trans
    ((eqvGen_equiv code (generators T) _ _).trans (some_eqvGen_iff T left right))

theorem loaded_invalid_separated (full : model.FullDomains) (meanings : Meanings model)
    (meaning : model.models signature.meaningFormula) {source : State}
    (code : signature.Carrier model ≃ RawRun (P := P) source) (run : P.Run source) :
    ¬(signature.traceValue model (generatorValue T signature model code)
      (code.symm none) (code.symm (some run))).down := by
  intro related
  have raw := (signature.trace_iff_eqvGen model full meanings meaning _ _ _).mp related
  exact invalid_separated T run ((eqvGen_equiv code (generators T) _ _).mp raw)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLNativeTrace
