import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectConfluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallelBoundary

/-!
# Root and beta peaks in the object package

Each decoder family is exercised against beta reduction in its argument.
The universal peak is proved for every simple carrier and specialized to
`prop`, so the impredicative instance is covered explicitly. A definition
returning a pair exercises a retained argument after root contraction.

A malformed code table identifies implication with an equation constructor.
Its two decoder branches are a function type and an identity type, and the
generic nonconfluence theorem applies to this concrete counterexample.
The separate repeated-metavariable control remains available as a check on
the left-linearity requirement of the constructor-system argument.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.ConversionCoherence
open Presentation.TypedEquality.Normalization (DecoderStep)
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic

namespace CodeModel
namespace ConfluenceControls

abbrev ObjectStep {n : Nat} : Tower.Tm n → Tower.Tm n → Prop :=
  StepCore objectRules.computation objectRules.headEq

abbrev betaId {n : Nat} (term : Tower.Tm n) : Tower.Tm n :=
  .app (.lam (.var 0)) term

theorem betaId_step {n : Nat} (term : Tower.Tm n) : ObjectStep (betaId term) term :=
  .betaPi (.var 0) term

abbrev allCode {n : Nat} (type : HOL.Ty SetProfile.SetBase) (predicate : Tower.Tm n) :
    Tower.Tm n := .app (.const (SetProfile.allName type)) predicate

abbrev allDecoded {n : Nat} (type : HOL.Ty SetProfile.SetBase) (predicate : Tower.Tm n) :
    Tower.Tm n :=
  .pi (liftClosed (typeTerm type))
    (programCodes.holdsOf (.app (rename wk predicate) (.var 0)))

theorem all_decode {n : Nat} (type : HOL.Ty SetProfile.SetBase) (predicate : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (allCode type predicate)) (allDecoded type predicate) := by
  apply StepCore.root
  apply programCodes.extend_decoder_step rules
  apply DecoderStep.all
  change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- Decoding and reducing the predicate commute, including at `all@prop`. -/
theorem all_beta_peak {n : Nat} (type : HOL.Ty SetProfile.SetBase) (predicate : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (allCode type (betaId predicate)))
      (allDecoded type (betaId predicate)) ∧
    ObjectStep (programCodes.holdsOf (allCode type (betaId predicate)))
      (programCodes.holdsOf (allCode type predicate)) ∧
    ObjectStep (allDecoded type (betaId predicate)) (allDecoded type predicate) ∧
    ObjectStep (programCodes.holdsOf (allCode type predicate)) (allDecoded type predicate) := by
  refine ⟨all_decode type _, .congAppArg (.congAppArg (betaId_step predicate)), ?_,
    all_decode type predicate⟩
  exact .congPiCod (.congAppArg (.congAppFun ((betaId_step predicate).renameTerms wk)))

/-- The impredicative quantifier instance participates in the same root peak. -/
theorem all_prop_beta_peak {n : Nat} (predicate : Tower.Tm n) :
    ObjectStep (allDecoded .prop (betaId predicate)) (allDecoded .prop predicate) ∧
    ObjectStep (programCodes.holdsOf (allCode .prop predicate)) (allDecoded .prop predicate) :=
  (all_beta_peak .prop predicate).2.2

abbrev impDecoded {n : Nat} (p q : Tower.Tm n) : Tower.Tm n :=
  .pi (programCodes.holdsOf p) (programCodes.holdsOf (rename wk q))

theorem imp_decode {n : Nat} (p q : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (programCodes.impOf p q)) (impDecoded p q) :=
  .root (programCodes.extend_decoder_step rules (DecoderStep.imp p q))

/-- An implication decoder retains reduction of its first argument in the
domain of the resulting function type. -/
theorem imp_beta_peak {n : Nat} (p q : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (programCodes.impOf (betaId p) q))
      (impDecoded (betaId p) q) ∧
    ObjectStep (programCodes.holdsOf (programCodes.impOf (betaId p) q))
      (programCodes.holdsOf (programCodes.impOf p q)) ∧
    ObjectStep (impDecoded (betaId p) q) (impDecoded p q) ∧
    ObjectStep (programCodes.holdsOf (programCodes.impOf p q)) (impDecoded p q) :=
  ⟨imp_decode _ _, .congAppArg (.congAppFun (.congAppArg (betaId_step p))),
    .congPiDom (.congAppArg (betaId_step p)), imp_decode p q⟩

abbrev eqCode {n : Nat} (type : HOL.Ty SetProfile.SetBase) (x y : Tower.Tm n) :
    Tower.Tm n := .app (.app (.const (SetProfile.eqName type)) x) y

abbrev eqDecoded {n : Nat} (type : HOL.Ty SetProfile.SetBase) (x y : Tower.Tm n) :
    Tower.Tm n := .id (liftClosed (typeTerm type)) x y

theorem eq_decode {n : Nat} (type : HOL.Ty SetProfile.SetBase) (x y : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (eqCode type x y)) (eqDecoded type x y) := by
  apply StepCore.root
  apply programCodes.extend_decoder_step rules
  apply DecoderStep.eq
  change (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm = _
  rw [SetProfile.eqInstance?_eqName]
  rfl

/-- An equation decoder retains reduction of its first endpoint. -/
theorem eq_beta_peak {n : Nat} (type : HOL.Ty SetProfile.SetBase) (x y : Tower.Tm n) :
    ObjectStep (programCodes.holdsOf (eqCode type (betaId x) y))
      (eqDecoded type (betaId x) y) ∧
    ObjectStep (programCodes.holdsOf (eqCode type (betaId x) y))
      (programCodes.holdsOf (eqCode type x y)) ∧
    ObjectStep (eqDecoded type (betaId x) y) (eqDecoded type x y) ∧
    ObjectStep (programCodes.holdsOf (eqCode type x y)) (eqDecoded type x y) :=
  ⟨eq_decode _ _ _, .congAppArg (.congAppFun (.congAppArg (betaId_step x))),
    .congIdLeft (betaId_step x), eq_decode type x y⟩

abbrev kept {n : Nat} (A P x e : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const Package.keepName) A) P) x) e

theorem keep_step {n : Nat} (A P x e : Tower.Tm n) : ObjectStep (kept A P x e) (.pair x e) := by
  have rule := equation_listed 9 (by decide) (show equations[9] = Package.keepEquation from rfl)
  exact .root (programCodes.extend_base_step rules (equation_sound rule ![e, x, P, A]))

/-- Root contraction keeps the computational content of a returned argument. -/
theorem keep_beta_peak {n : Nat} (A P x e : Tower.Tm n) :
    ObjectStep (kept A P (betaId x) e) (.pair (betaId x) e) ∧
    ObjectStep (kept A P (betaId x) e) (kept A P x e) ∧
    ObjectStep (.pair (betaId x) e) (.pair x e) ∧
    ObjectStep (kept A P x e) (.pair x e) :=
  ⟨keep_step _ _ _ _, .congAppFun (.congAppArg (betaId_step x)),
    .congPairFst (betaId_step x), keep_step A P x e⟩

theorem numRec_suc_step {n : Nat} (P z s m : Tower.Tm n) :
    ObjectStep (Package.numRecApp P z s (.app (.const sucN) m))
      (.app (.app s m) (Package.numRecApp P z s m)) := by
  have rule := equation_listed 6 (by decide)
    (show equations[6] = Package.numRecSucEquation from rfl)
  exact .root (programCodes.extend_base_step rules (equation_sound rule ![m, s, z, P]))

/-- The successor recursor duplicates its method in the contractum. Reducing
one source method before contraction or both residual copies afterwards
reaches the same explicit term. -/
theorem numRec_duplicate_beta_peak {n : Nat} (P z s m : Tower.Tm n) :
    ObjectStep (Package.numRecApp P z (betaId s) (.app (.const sucN) m))
      (.app (.app (betaId s) m) (Package.numRecApp P z (betaId s) m)) ∧
    ObjectStep (Package.numRecApp P z (betaId s) (.app (.const sucN) m))
      (Package.numRecApp P z s (.app (.const sucN) m)) ∧
    StepStar objectRules
      (.app (.app (betaId s) m) (Package.numRecApp P z (betaId s) m))
      (.app (.app s m) (Package.numRecApp P z s m)) ∧
    ObjectStep (Package.numRecApp P z s (.app (.const sucN) m))
      (.app (.app s m) (Package.numRecApp P z s m)) := by
  refine ⟨numRec_suc_step _ _ _ _, .congAppFun (.congAppArg (betaId_step s)), ?_,
    numRec_suc_step P z s m⟩
  have first : ObjectStep
      (.app (.app (betaId s) m) (Package.numRecApp P z (betaId s) m))
      (.app (.app s m) (Package.numRecApp P z (betaId s) m)) :=
    .congAppFun (.congAppFun (betaId_step s))
  have second : ObjectStep
      (.app (.app s m) (Package.numRecApp P z (betaId s) m))
      (.app (.app s m) (Package.numRecApp P z s m)) :=
    .congAppArg (.congAppFun (.congAppArg (betaId_step s)))
  exact (Relation.ReflTransGen.single first).tail second

/-- Deliberately malformed table: implication is also an equation constructor. -/
def overlappingCodes : Codes Tower.Head :=
  { programCodes with equations := fun name =>
      if name = impN then some (.const propN) else none }

/-- Dropping decoder-name separation creates a genuine nonconfluent package. -/
theorem overlappingCodes_not_churchRosser : ¬ ChurchRosser (overlappingCodes.extend rules) := by
  apply overlappingCodes.extend_not_churchRosser constructors (A := .const propN)
  simp [overlappingCodes, Codes.equationCarrier, programCodes]

/-- Repeated schema variables invalidate an unrestricted one-step diamond
claim; they have not been assumed away for arbitrary algebraic systems. -/
theorem nonlinear_parallel_not_diamond :
    ¬ (∀ {source left right : AlgebraicParallel.NonlinearBoundary.ToyTerm},
      AlgebraicParallel.NonlinearBoundary.ToyParallel source left →
      AlgebraicParallel.NonlinearBoundary.ToyParallel source right →
      ∃ common,
        AlgebraicParallel.NonlinearBoundary.ToyParallel left common ∧
        AlgebraicParallel.NonlinearBoundary.ToyParallel right common) :=
  AlgebraicParallel.NonlinearBoundary.duplicateParallel_not_diamond

end ConfluenceControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
