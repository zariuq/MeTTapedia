import Mettapedia.TypeTheory.Calculi.NativeDependent.RuleInitiality
import Mettapedia.TypeTheory.JudgmentEquationInitiality

/-!
# Computation equations for the native quantifier rule grammar

The independently authored beta equation generates exactly the computation
congruence on the native proof grammar. Its quotient is initial among local
rule models satisfying that equation. The actual displayed-presheaf model
qualifies by its proved dependent beta calculation, and quotient evaluation
recovers the supplied native section.

Primitive declaration origins survive this quotient. This is equation-
qualified rule-algebra initiality for the fixed-object-sort quantifier
fragment, not initiality of a category with arbitrary type comprehension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.EquationInitiality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RuleInitiality PresheafInterpretation
open Mettapedia.TypeTheory.JudgmentDerivation
open Mettapedia.TypeTheory.DisplayedPresheafTransport

universe u
variable {Constant Predicate : Type u}
variable (Declaration : (n : Nat) → Formula Constant Predicate n → Type u)

/-- Only the primitive computation rule is imposed; congruence is generated
by the actual rule operations rather than assumed as an equation. -/
inductive PrimitiveEquation : {n : Nat} → {formula : Formula Constant Predicate n} →
    Proof Declaration n formula → Proof Declaration n formula → Prop where
  | beta {n : Nat} {body : Formula Constant Predicate (n + 1)}
      (proof : Proof Declaration (n + 1) body) (argument : ObjectTerm Constant n) :
      PrimitiveEquation (Proof.app (Proof.lam proof) argument)
        (Proof.substitute proof (ObjectSubstitution.instantiate argument))

def equations : JudgmentEquationInitiality.Equations (signature Declaration) :=
  fun left right => PrimitiveEquation Declaration
    (interpret (syntaxAlgebra Declaration) left)
    (interpret (syntaxAlgebra Declaration) right)

theorem primitive_sound {n : Nat} {formula : Formula Constant Predicate n}
    {left right : Proof Declaration n formula}
    (related : PrimitiveEquation Declaration left right) : ProofEquation left right := by
  cases related with
  | beta proof argument => exact .beta proof argument

/-- Closing the beta generator under the independent indexed rules is
sound for the original proof grammar's computation congruence. -/
theorem congruence_decode {judgment : (signature Declaration).Judgment}
    {left right : Derivation (signature Declaration) judgment}
    (related : JudgmentEquationInitiality.Congruence (equations Declaration) left right) :
    ProofEquation (interpret (syntaxAlgebra Declaration) left)
      (interpret (syntaxAlgebra Declaration) right) := by
  apply JudgmentEquationInitiality.congruence_least (equations Declaration)
    (fun left right => ProofEquation (interpret (syntaxAlgebra Declaration) left)
      (interpret (syntaxAlgebra Declaration) right))
    (fun imposed => primitive_sound Declaration imposed)
    (fun _ => .refl _) (fun ih => .symm ih) (fun first second => .trans first second)
    (rules := ?_) related
  rintro ⟨n, formula⟩ rule left right ih
  change Rule Declaration n formula at rule
  cases rule with
  | declaration name => exact .refl _
  | substitute _ replacements => exact .substitute (ih PUnit.unit) replacements
  | lam _ => exact .lam (ih PUnit.unit)
  | app _ argument => exact .app (ih PUnit.unit) argument
  | pair _ first => exact .pair first (ih PUnit.unit)

/-- Every original computation proof is represented by the generated
congruence; no extra semantic equality is used. -/
theorem proofEquation_generated {n : Nat} {formula : Formula Constant Predicate n}
    {left right : Proof Declaration n formula} (related : ProofEquation left right) :
    JudgmentEquationInitiality.Congruence (equations Declaration) (encode Declaration left)
      (encode Declaration right) := by
  induction related with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | beta proof argument =>
      apply JudgmentEquationInitiality.Congruence.equation
      change PrimitiveEquation Declaration
        (decode Declaration (encode Declaration _))
        (decode Declaration (encode Declaration _))
      rw [decode_encode, decode_encode]
      exact .beta proof argument
  | @substitute n m formula first second _ replacements ih =>
      exact .node (S := signature Declaration) (j := ⟨n, .substitute formula replacements⟩)
        (Rule.substitute formula replacements) _ _ (fun position => by cases position; exact ih)
  | @lam n body first second _ ih =>
      exact .node (S := signature Declaration) (j := ⟨n, .pi body⟩)
        (Rule.lam body) _ _ (fun position => by cases position; exact ih)
  | @app n body first second _ argument ih =>
      exact .node (S := signature Declaration)
        (j := ⟨n, .substitute body (ObjectSubstitution.instantiate argument)⟩)
        (Rule.app body argument) _ _ (fun position => by cases position; exact ih)
  | @pair n body argument first second _ ih =>
      exact .node (S := signature Declaration) (j := ⟨n, .sigma body⟩)
        (Rule.pair body argument) _ _ (fun position => by cases position; exact ih)

theorem congruence_iff {n : Nat} {formula : Formula Constant Predicate n}
    (left right : Derivation (signature Declaration) ⟨n, formula⟩) :
    JudgmentEquationInitiality.Congruence (equations Declaration) left right ↔
      ProofEquation (decode Declaration left) (decode Declaration right) := by
  constructor
  · exact congruence_decode Declaration
  · intro related
    have generated := proofEquation_generated Declaration related
    rw [encode_decode, encode_decode] at generated
    exact generated

/-- The supplied declaration is an invariant of the exact quotient. -/
def originReadout {judgment : Judgment (Constant := Constant) (Predicate := Predicate)} :
    JudgmentEquationInitiality.Presented (equations Declaration) judgment → Proof.Origin (Declaration := Declaration) :=
  Quotient.lift (fun tree => (interpret (syntaxAlgebra Declaration) tree).origin)
    (fun _ _ related => Proof.equation_origin (congruence_decode Declaration related))

@[simp] theorem originReadout_encode {n : Nat} {formula : Formula Constant Predicate n}
    (proof : Proof Declaration n formula) :
    originReadout Declaration (Quotient.mk _ (encode Declaration proof)) = proof.origin := by
  change (decode Declaration (encode Declaration proof)).origin = proof.origin
  rw [decode_encode]

/-- Equal result values cannot justify discarding independently supplied
declaration origins, even after generated beta equations are imposed. -/
theorem declaration_quotient_injective {n : Nat} {formula : Formula Constant Predicate n}
    {first second : Declaration n formula}
    (same : (Quotient.mk (JudgmentEquationInitiality.derivationSetoid (equations Declaration) ⟨n, formula⟩)
      (encode Declaration (Proof.declaration first))) =
      Quotient.mk _ (encode Declaration (Proof.declaration second))) : first = second := by
  have origins := congrArg (originReadout Declaration) same
  rw [originReadout_encode, originReadout_encode] at origins
  exact Proof.declaration_origin_injective origins

/-- Initiality is in the actual category of beta-qualified local rule
models, with both existence and uniqueness of interpretation. -/
noncomputable def presentedIsInitial :
    IsInitial (JudgmentEquationInitiality.presentedModel (equations Declaration)) :=
  JudgmentEquationInitiality.presentedIsInitial (equations Declaration)

variable {C : Type u} [Category.{u} C]
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u, u, u, u} D)
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (family D constants predicates formula).sections)

theorem native_interpret_decode {n : Nat} {formula : Formula Constant Predicate n}
    (tree : Derivation (signature Declaration) ⟨n, formula⟩) :
    interpret (nativeAlgebra Declaration D constants predicates declarations) tree =
      proof D constants predicates declarations (decode Declaration tree) := by
  have agrees := native_interpreter_agreement Declaration D constants predicates declarations
    (decode Declaration tree)
  rw [encode_decode] at agrees
  exact agrees

theorem native_primitive_sound {n : Nat} {formula : Formula Constant Predicate n}
    {left right : Proof Declaration n formula}
    (related : PrimitiveEquation Declaration left right) :
    proof D constants predicates declarations left = proof D constants predicates declarations right := by
  cases related with
  | beta proof argument => exact PresheafInterpretation.beta D constants predicates declarations proof argument

/-- The presheaf model satisfies the generator through its actual
dependent beta calculation, rather than a model-wide soundness assumption. -/
theorem native_satisfies : JudgmentEquationInitiality.Satisfies (equations Declaration)
    (nativeAlgebra Declaration D constants predicates declarations) := by
  intro judgment left right imposed
  rcases judgment with ⟨n, formula⟩
  rw [native_interpret_decode, native_interpret_decode]
  change PrimitiveEquation Declaration (decode Declaration left) (decode Declaration right) at imposed
  exact native_primitive_sound Declaration D constants predicates declarations imposed

noncomputable def nativeModel : JudgmentEquationInitiality.Model (equations Declaration) where
  algebra := nativeAlgebra Declaration D constants predicates declarations
  satisfies := native_satisfies Declaration D constants predicates declarations

noncomputable def nativeEvaluation :
    Hom (JudgmentEquationInitiality.presentedAlgebra (equations Declaration))
      (nativeAlgebra Declaration D constants predicates declarations) :=
  JudgmentEquationInitiality.evaluation (equations Declaration) _
    (native_satisfies Declaration D constants predicates declarations)

/-- Evaluation from the initial quotient computes the exact supplied
native certificate, including its genuinely input-dependent type. -/
theorem nativeEvaluation_encode {n : Nat} {formula : Formula Constant Predicate n}
    (term : Proof Declaration n formula) :
    (nativeEvaluation Declaration D constants predicates declarations).map
      (Quotient.mk _ (encode Declaration term)) =
        proof D constants predicates declarations term :=
  native_interpreter_agreement Declaration D constants predicates declarations term

end Mettapedia.TypeTheory.Calculi.NativeDependent.EquationInitiality
