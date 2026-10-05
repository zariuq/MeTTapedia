import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRules
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Confluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationRewriting

/-!
# Confluence of the executable package with proposition codes

The actual computation package is extended by implication, universal and
identity decoders. Its finite executable equations and all decoder instances
form one constructor system. The quantifier over proposition codes is included:
the constructor-system argument requires no restriction on its closed carrier.

The separation proofs below concern the existing instance-name parsers and the
existing executable equations. The two-sided schema presentation is obtained
from their independently proved presentations, without replacing the package's
root computation or its contextual reduction relation.

The object package speaks only of declared names (`code_declared`,
`objectNamesDeclared`): a name one of its codes decodes at is declared in it, and
so is every constant of a left side of its equations and of its decoders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.AlgebraicParallel (SchemaPresentation)
open Presentation.ConstructorSystem (ConstructorPresentation mentionsConst)
open Presentation.ConversionCoherence (ChurchRosser)
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Annotated (NamesDeclared)

namespace CodeModel

/-- No executable defined constant is a quantifier or equation instance. -/
theorem codeInstances_none_of_defined {name : DeclName} (defined : EquationDefined name) :
    programCodes.quantifiers name = none ∧ programCodes.equationCarrier name = none := by
  simp only [EquationDefined, equationArities, List.map, List.mem_cons,
    List.not_mem_nil, or_false] at defined
  rcases defined with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> decide

/-- The decoder does not occur anywhere in an executable left-hand side. -/
theorem executable_left_decoder_absent {m : Nat} {left right : Tower.Tm m}
    (rule : equations.family left right) : mentionsConst holdsN left = false := by
  have listed := equations_family rule
  simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at listed
  rcases listed with (same | same | same | same) | (same | same | same | same | same | same |
    same | same | same | same | same | same) <;> cases same <;> decide

/-- The program's code names satisfy the separation conditions for extending
the executable constructor system. -/
theorem programCodes_apart : programCodes.Apart system where
  holds_undefined := by change ¬ EquationDefined holdsN; decide
  holds_absent := executable_left_decoder_absent
  imp_undefined := by change ¬ EquationDefined impN; decide
  imp_ne_holds := by decide
  all_apart := by
    intro name carrier found
    refine ⟨fun defined => ?_, fun same => ?_⟩
    · have absent := (codeInstances_none_of_defined defined).1
      rw [absent] at found
      cases found
    · subst name
      have absent : programCodes.quantifiers programCodes.holds = none := by decide
      rw [absent] at found
      cases found
  eq_apart := by
    intro name carrier found
    refine ⟨fun defined => ?_, fun same => ?_, fun same => ?_⟩
    · have absent := (codeInstances_none_of_defined defined).2
      rw [absent] at found
      cases found
    · subst name
      have absent : programCodes.equationCarrier programCodes.holds = none := by decide
      rw [absent] at found
      cases found
    · subst name
      have absent : programCodes.equationCarrier programCodes.imp = none := by decide
      rw [absent] at found
      cases found

/-- A two-sided root presentation for the actual object package, including
every admitted decoder instance. -/
def objectPresentation : SchemaPresentation objectRules :=
  programCodes.extendPresentation presentation

/-- An actual root step is exactly a substituted executable equation or
decoder schema. Both directions use the original computation package. -/
theorem objectRoot_iff_schema {n : Nat} {source target : Tower.Tm n} :
    objectRules.computation.step source target ↔
      ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
        Codes.ExtendedSchema equations.family programCodes left right ∧
        subst σ left = source ∧ subst σ right = target := by
  constructor
  · exact objectPresentation.cover
  · rintro ⟨arity, left, right, σ, rule, rfl, rfl⟩
    exact objectPresentation.sound rule σ

/-- The complete object package as an orthogonal constructor system. -/
def objectConstructors : ConstructorPresentation objectRules :=
  programCodes.extendConstructors constructors programCodes_apart

/-- Church--Rosser for the existing object reduction and conversion. -/
theorem objectChurchRosser : ChurchRosser objectRules :=
  programCodes.extend_churchRosser constructors programCodes_apart

/-- Function-type conversion in the object package separates both components. -/
theorem objectPiConversionBoundary : PiConversionBoundary objectRules :=
  objectConstructors.piConversionBoundary

/-- Pair-type conversion in the object package separates both components. -/
theorem objectSigmaConversionBoundary : SigmaConversionBoundary objectRules :=
  objectConstructors.sigmaConversionBoundary

open Presentation.TypedEquality.Impredicative in
/-- A name a code of the object package decodes at is declared in the object package. -/
theorem code_declared {c : DeclName}
    (code : programCodes.quantifiers c ≠ none ∨ programCodes.equationCarrier c ≠ none) :
    objectRules.constantType c ≠ none := by
  have coded : programCodes.codeType c ≠ none := by
    unfold Codes.codeType
    split_ifs
    · exact Option.some_ne_none _
    · exact Option.some_ne_none _
    · exact Option.some_ne_none _
    · cases found : programCodes.quantifiers c with
      | some _ => exact Option.some_ne_none _
      | none =>
          rw [found] at code
          obtain ⟨A, carrier⟩ := Option.ne_none_iff_exists'.mp (code.resolve_left (by simp))
          simp [carrier]
  obtain ⟨T, typed⟩ := Option.ne_none_iff_exists'.mp coded
  rw [programCodes.extend_constantType_of_code rules typed]
  exact Option.some_ne_none _

open Presentation.TypedEquality.Impredicative in
/-- **The object package speaks only of declared names**: each of its defined constants, and
each constant of a left side of its equations and of its decoders, is declared in it. -/
theorem objectNamesDeclared : NamesDeclared objectConstructors where
  defined := by
    intro c defined
    rcases defined with listed | rfl
    · have declared : ∀ c ∈ equationArities.map Prod.fst,
          (objectRules.constantType c).isSome = true := by decide
      exact Option.isSome_iff_ne_none.mp (declared c listed)
    · decide
  left := by
    intro m left right rule c mentioned
    cases rule with
    | base rule =>
        have declared : ∀ entry ∈ equations,
            entry.2.1.allConstants (fun c => (objectRules.constantType c).isSome) = true := by
          decide
        exact Option.isSome_iff_ne_none.mp (ConstructorSystem.mentionsConst_allConstants _
          mentioned (declared _ (equations_family rule)))
    | decoder rule =>
        cases rule with
        | imp =>
            simp only [Codes.impLeft, Codes.holdsOf, Codes.impOf, ConstructorSystem.mentionsConst,
              Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at mentioned
            rcases mentioned with rfl | rfl <;> decide
        | @all a A carrier =>
            simp only [Codes.allLeft, Codes.holdsOf, ConstructorSystem.mentionsConst,
              Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at mentioned
            rcases mentioned with rfl | rfl
            · decide
            · exact code_declared (.inl (by rw [carrier]; exact Option.some_ne_none _))
        | @eq e A carrier =>
            simp only [Codes.eqLeft, Codes.holdsOf, ConstructorSystem.mentionsConst,
              Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at mentioned
            rcases mentioned with rfl | rfl
            · decide
            · exact code_declared (.inr (by rw [carrier]; exact Option.some_ne_none _))

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
