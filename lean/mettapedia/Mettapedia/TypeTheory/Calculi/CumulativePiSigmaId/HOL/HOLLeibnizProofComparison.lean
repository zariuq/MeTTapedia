import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation

/-!
# Retained HOL equality and Leibniz predicate proofs

Primitive HOL equality and its predicate formulation are related by actual
proof trees of the existing extensional calculus. The comparison uses no new
logical assumptions and does not identify either presentation with native
identity. Reflexivity and composition in the predicate presentation use only
implication, quantification and hypotheses, making that part available to
the existing native proof compiler. The primitive comparison itself still
uses HOL equality rules and is not a completed native equality attachment.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizProofComparison

open Mettapedia.Logic

namespace Source

open HOL

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {gamma : Ctx Base}
variable {type : Ty Base}

/-- Quantification is over the existing HOL predicate type, not over arbitrary
native dependent families. -/
def leibniz (x y : Term Const gamma type) : Formula Const gamma :=
  .all (.imp (.app (.var .vz) (weaken x)) (.app (.var .vz) (weaken y)))

theorem leibniz_rename {target : Ctx Base} (rho : Rename Base gamma target)
    (x y : Term Const gamma type) :
    rename rho (leibniz x y) = leibniz (rename rho x) (rename rho y) := by
  simp only [leibniz, rename, ExtDerivation.rename_weaken, Rename.lift]

theorem leibniz_weaken {a : Ty Base} (x y : Term Const gamma type) :
    weaken (σ := a) (leibniz x y) = leibniz (weaken x) (weaken y) :=
  leibniz_rename Rename.weaken x y

theorem leibniz_subst {target : Ctx Base} (sigma : Subst Const gamma target)
    (x y : Term Const gamma type) :
    subst sigma (leibniz x y) = leibniz (subst sigma x) (subst sigma y) := by
  simp only [leibniz, subst, subst_weaken, Subst.lift]

theorem instantiate_predicate (x y : Term Const gamma type)
    (predicate : Term Const gamma (type ⇒ .prop)) :
    instantiate predicate
      (.imp (.app (.var .vz) (weaken x)) (.app (.var .vz) (weaken y))) =
      .imp (.app predicate x) (.app predicate y) := by
  change Term.imp (.app predicate (instantiate predicate (weaken x)))
      (.app predicate (instantiate predicate (weaken y))) = _
  rw [instantiate_weaken, instantiate_weaken]

def specialize {delta : List (Formula Const gamma)} (x y : Term Const gamma type)
    (predicate : Term Const gamma (type ⇒ .prop))
    (major : ProofSyntax Const delta (leibniz x y)) :
    ProofSyntax Const delta (.imp (.app predicate x) (.app predicate y)) :=
  cast (congrArg (ProofSyntax Const delta) (instantiate_predicate x y predicate))
    (.allE predicate major)

def primitiveToLeibniz (x y : Term Const gamma type) :
    ProofSyntax Const [] (.imp (.eq x y) (leibniz x y)) := by
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact .impE (.eqPropEL (.eqAppArg (.var .vz) (.hyp 1))) (.hyp 0)

def leibnizToPrimitive (x y : Term Const gamma type) :
    ProofSyntax Const [] (.imp (leibniz x y) (.eq x y)) := by
  apply ProofSyntax.impI
  let predicate : Term Const gamma (type ⇒ .prop) := .lam (.eq (weaken x) (.var .vz))
  have betaResult (t : Term Const gamma type) :
      instantiate t (.eq (weaken x) (.var .vz)) = .eq x t := by
    change Term.eq (instantiate t (weaken x)) t = .eq x t
    rw [instantiate_weaken]
  have leftBeta : ProofSyntax Const [leibniz x y]
      (.eq (.app predicate x) (.eq x x)) := by
    simpa only [predicate, betaResult]
      using (ProofSyntax.beta (Δ := [leibniz x y]) x (.eq (weaken x) (.var .vz)))
  have rightBeta : ProofSyntax Const [leibniz x y]
      (.eq (.app predicate y) (.eq x y)) := by
    simpa only [predicate, betaResult]
      using (ProofSyntax.beta (Δ := [leibniz x y]) y (.eq (weaken x) (.var .vz)))
  exact .impE (.eqPropEL rightBeta)
    (.impE (specialize x y predicate (.hyp 0))
      (.impE (.eqPropER leftBeta) (.eqRefl x)))

/-- Both implications are retained; an erasure theorem does not select a
replacement proof or erase the original route. -/
def equivalence (x y : Term Const gamma type) :
    ProofSyntax Const [] (.and (.imp (.eq x y) (leibniz x y))
      (.imp (leibniz x y) (.eq x y))) :=
  .andI (primitiveToLeibniz x y) (leibnizToPrimitive x y)

theorem equivalence_derivable (x y : Term Const gamma type) :
    ExtDerivation Const [] (.and (.imp (.eq x y) (leibniz x y))
      (.imp (leibniz x y) (.eq x y))) :=
  (equivalence x y).erase

/-- Apply the retained comparison to an actual primitive equality proof,
transporting the comparison's empty hypothesis list into the caller's list. -/
def ofPrimitive {delta : List (Formula Const gamma)} {x y : Term Const gamma type}
    (equality : ProofSyntax Const delta (.eq x y)) :
    ProofSyntax Const delta (leibniz x y) :=
  .impE (ProofSyntax.mono (Δ := []) (Δ' := delta)
    ⟨Fin.elim0, fun occurrence => Fin.elim0 occurrence⟩ (primitiveToLeibniz x y)) equality

def toPrimitive {delta : List (Formula Const gamma)} {x y : Term Const gamma type}
    (relation : ProofSyntax Const delta (leibniz x y)) :
    ProofSyntax Const delta (.eq x y) :=
  .impE (ProofSyntax.mono (Δ := []) (Δ' := delta)
    ⟨Fin.elim0, fun occurrence => Fin.elim0 occurrence⟩ (leibnizToPrimitive x y)) relation

/-- Logical equivalence is not a lossless reconstruction of the initial
proof syntax. The round trip keeps its actual comparison inferences. -/
theorem roundTrip_distinct (x : Term Const gamma type) :
    toPrimitive (ofPrimitive (ProofSyntax.eqRefl (Δ := []) x)) ≠ ProofSyntax.eqRefl x := by
  intro equal
  have roots := congrArg ProofSyntax.rootObservation equal
  cases roots

theorem roundTrip_same_admission (x : Term Const gamma type) :
    (toPrimitive (ofPrimitive (ProofSyntax.eqRefl (Δ := []) x))).intrinsicAdmission =
      (ProofSyntax.eqRefl (Δ := []) x).intrinsicAdmission :=
  ProofSyntax.intrinsicAdmission_eq _ _

def reflexivity (x : Term Const gamma type) :
    ProofSyntax Const [] (leibniz x x) := .allI (.impI (.hyp 0))

def transitivity (x y z : Term Const gamma type) :
    ProofSyntax Const [] (.imp (leibniz x y) (.imp (leibniz y z) (leibniz x z))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let predicate : Term Const ((type ⇒ .prop) :: gamma) (type ⇒ .prop) := .var .vz
  have first : ProofSyntax Const
      [.app predicate (weaken x), weaken (leibniz y z), weaken (leibniz x y)]
      (leibniz (weaken x) (weaken y)) := by
    rw [← leibniz_weaken]
    exact .hyp 2
  have second : ProofSyntax Const
      [.app predicate (weaken x), weaken (leibniz y z), weaken (leibniz x y)]
      (leibniz (weaken y) (weaken z)) := by
    rw [← leibniz_weaken]
    exact .hyp 1
  exact .impE (specialize (weaken y) (weaken z) predicate second)
    (.impE (specialize (weaken x) (weaken y) predicate first) (.hyp 0))

end Source

namespace Native

open HOL.UniformListInduction Presentation
open HOLNaturalDeductionNativeTranslation

def closedReflexivity (type : HOL.Ty BaseSort) :
    HOL.ProofSyntax Symbol ([] : List (Formula []))
      (.all (Source.leibniz (type := type) (.var .vz) (.var .vz))) :=
  .allI (Source.reflexivity (.var .vz))

theorem compile_closedReflexivity (type : HOL.Ty BaseSort) :
    compile (closedReflexivity type) (n := 0) Fin.elim0 Fin.elim0 =
      some (.lam (.lam (.lam (.var 0)))) := rfl

theorem closedReflexivity_judgment (type : HOL.Ty BaseSort) :
    ∃ code : Tower.Tm 0,
      represent (gamma := []) (.all (Source.leibniz (type := type) (.var .vz) (.var .vz))) = some code ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil
        (.lam (.lam (.lam (.var 0)))) (FormationSensitiveHOLProofFamily.proof code) :=
  NativeTyping.compile_closed (closedReflexivity type) (compile_closedReflexivity type)

def closedTransitivity (type : HOL.Ty BaseSort) :
    HOL.ProofSyntax Symbol ([] : List (Formula []))
      (.all (.all (.all
        (.imp (Source.leibniz (type := type) (.var (.vs (.vs .vz))) (.var (.vs .vz)))
          (.imp (Source.leibniz (.var (.vs .vz)) (.var .vz))
            (Source.leibniz (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  .allI (.allI (.allI
    (Source.transitivity (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- Seven binders retain three objects, two relation proofs, a predicate and
its input witness; the two supplied relation proofs are genuinely used. -/
def transitivityTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam
    (.app (.app (.var 2) (.var 1)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))))

theorem compile_closedTransitivity (type : HOL.Ty BaseSort) :
    compile (closedTransitivity type) (n := 0) Fin.elim0 Fin.elim0 =
      some transitivityTerm := rfl

theorem closedTransitivity_judgment (type : HOL.Ty BaseSort) :
    ∃ code : Tower.Tm 0,
      represent (gamma := []) (.all (.all (.all
        (.imp (Source.leibniz (type := type) (.var (.vs (.vs .vz))) (.var (.vs .vz)))
          (.imp (Source.leibniz (.var (.vs .vz)) (.var .vz))
            (Source.leibniz (.var (.vs (.vs .vz))) (.var .vz))))))) = some code ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil
        transitivityTerm (FormationSensitiveHOLProofFamily.proof code) :=
  NativeTyping.compile_closed (closedTransitivity type) (compile_closedTransitivity type)

def predicateTransport {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (x y : HOL.Term Symbol gamma type) (predicate : HOL.Term Symbol gamma (.arr type .prop)) :
    HOL.ProofSyntax Symbol [Source.leibniz x y, .app predicate x] (.app predicate y) :=
  .impE (Source.specialize x y predicate (.hyp 0)) (.hyp 1)

theorem compile_predicateTransport {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (x y : HOL.Term Symbol gamma type) (predicate : HOL.Term Symbol gamma (.arr type .prop))
    {code : Tower.Tm gamma.length} (represented : represent predicate = some code)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin 2 → Tower.Tm n) :
    compile (predicateTransport x y predicate) objects hypotheses =
      some (.app (.app (hypotheses 0) (subst objects code)) (hypotheses 1)) := by
  simp only [predicateTransport, compile, Source.specialize]
  erw [compile_cast_conclusion]
  · simp [compile, represented]
  · exact Source.instantiate_predicate x y predicate

theorem predicateTransport_judgment {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (x y : HOL.Term Symbol gamma type) (predicate : HOL.Term Symbol gamma (.arr type .prop))
    {code : Tower.Tm gamma.length} (represented : represent predicate = some code)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin 2 → Tower.Tm n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules target)
    (objectTyped : NativeTyping.Objects target objects)
    (hypothesisTyped : NativeTyping.Hypotheses
      (delta := [Source.leibniz x y, .app predicate x]) target objects hypotheses) :
    ∃ conclusion, represent (.app predicate y) = some conclusion ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules target
        (.app (.app (hypotheses 0) (subst objects code)) (hypotheses 1))
        (FormationSensitiveHOLProofFamily.proof (subst objects conclusion)) :=
  NativeTyping.compile_judgment (predicateTransport x y predicate) formed objectTyped hypothesisTyped
    (compile_predicateTransport x y predicate represented objects hypotheses)

/-- Comparison proofs are retained HOL data, not silently admitted by the
five-rule native compiler before its equality cases are implemented. -/
theorem primitive_comparison_not_compiled :
    compile (Source.primitiveToLeibniz (nil : Expr [] sequence) nil)
      (n := 0) Fin.elim0 Fin.elim0 = none ∧
    compile (Source.leibnizToPrimitive (nil : Expr [] sequence) nil)
      (n := 0) Fin.elim0 Fin.elim0 = none := ⟨rfl, rfl⟩

/-- The new presentation does not install a computation rule for primitive
equality; the decoder still has exactly its original selective roots. -/
theorem primitive_equality_stays_undecoded (target : Tower.Tm 0) :
    ¬ FormationSensitiveHOLProofFamily.DecoderStep
      (FormationSensitiveHOLProofFamily.proof
        (FormationSensitiveHOLUniformList.rawEq sequence
          (.const `HOLUniformList.nil) (.const `HOLUniformList.nil))) target :=
  FormationSensitiveHOLProofFamily.equality_has_no_decoder_step _ _ _ _

end Native

#print axioms Source.primitiveToLeibniz
#print axioms Source.leibnizToPrimitive
#print axioms Source.equivalence_derivable
#print axioms Source.roundTrip_distinct
#print axioms Source.roundTrip_same_admission
#print axioms Source.reflexivity
#print axioms Source.transitivity
#print axioms Source.leibniz_rename
#print axioms Source.leibniz_subst
#print axioms Native.closedReflexivity_judgment
#print axioms Native.closedTransitivity_judgment
#print axioms Native.predicateTransport_judgment
#print axioms Native.primitive_comparison_not_compiled
#print axioms Native.primitive_equality_stays_undecoded

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizProofComparison
