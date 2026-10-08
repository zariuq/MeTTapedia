import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsSyntax
import Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation

/-!
# Proof assumption contexts in the native presheaf model

The raw context grammar is interpreted by actual comprehension. Its tuple
map remembers all object binders, while proof assumptions retain their
displayed evidence. Structural maps are constructed recursively and their
object-tuple equations are proved from the individual rules.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
open Mettapedia.TypeTheory.DisplayedPresheafPi
open Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution

universe u w
variable {C : Type u} [Category.{u} C] {Constant Predicate : Type u}
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u,u,u,u} D)

/-- Append a bound object to an arbitrary context tuple. -/
def objectTuple {P : Cᵒᵖ ⥤ Type u} {n : Nat}
    (tuple : P ⟶ ObjectInterpretation.context D n) :
    totalSpace (ObjectInterpretation.objectFamily D P) ⟶ ObjectInterpretation.context D (n + 1) where
  app _ := TypeCat.ofHom fun point => ⟨tuple.app _ point.1, point.2⟩
  naturality _ _ arrow := by
    ext point
    apply Sigma.ext (tuple.naturality_apply arrow point.1)
    rfl

structure ContextData (n : Nat) where
  base : Cᵒᵖ ⥤ Type u
  tuple : base ⟶ ObjectInterpretation.context D n

/-- Contexts and their object projections are defined together by structural
recursion on raw syntax, independently of judgments inhabiting them. -/
noncomputable def data : {n : Nat} → Scope Constant Predicate n → ContextData D n
  | n, .objects _ => ⟨ObjectInterpretation.context D n, 𝟙 _⟩
  | _, .object previous =>
      ⟨totalSpace (ObjectInterpretation.objectFamily D (data previous).base),
        objectTuple D (data previous).tuple⟩
  | _, .proof previous formula =>
      let previousData := data previous
      let assumed := reindexDisplayed previousData.tuple
        (PresheafInterpretation.family D constants predicates formula)
      ⟨totalSpace assumed, totalProjection assumed ≫ previousData.tuple⟩

noncomputable def context {n : Nat} (scope : Scope Constant Predicate n) : Cᵒᵖ ⥤ Type u :=
  (data D constants predicates scope).base

noncomputable def tuple {n : Nat} (scope : Scope Constant Predicate n) :
    context D constants predicates scope ⟶ ObjectInterpretation.context D n :=
  (data D constants predicates scope).tuple

noncomputable def legacyFamily {n : Nat} (scope : Scope Constant Predicate n)
    (formula : Formula Constant Predicate n) : DisplayedFamily.{u,u,u,u} (context D constants predicates scope) :=
  reindexDisplayed (tuple D constants predicates scope)
    (PresheafInterpretation.family D constants predicates formula)

theorem objectFamily_reindex {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q) :
    reindexDisplayed change (ObjectInterpretation.objectFamily D Q) =
      ObjectInterpretation.objectFamily D P := rfl

theorem objectTuple_eq_total {P : Cᵒᵖ ⥤ Type u} {n : Nat}
    (tuple : P ⟶ ObjectInterpretation.context D n) :
    objectTuple D tuple = totalReindexMap tuple
      (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n)) := by
  ext point value
  rfl

theorem tuple_weaken {n : Nat} (scope : Scope Constant Predicate n) :
    tuple D constants predicates (.object scope) ≫
        ObjectInterpretation.substitution D constants ObjectSubstitution.weaken =
      totalProjection (ObjectInterpretation.objectFamily D (context D constants predicates scope)) ≫
        tuple D constants predicates scope := by
  rw [ObjectInterpretation.substitution_weaken]
  ext point value
  rfl

theorem legacy_proof {n : Nat} (scope : Scope Constant Predicate n)
    (newFormula formula : Formula Constant Predicate n) :
    legacyFamily D constants predicates (.proof scope newFormula) formula =
      reindexDisplayed (totalProjection (legacyFamily D constants predicates scope newFormula))
        (legacyFamily D constants predicates scope formula) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem legacy_weaken {n : Nat} (scope : Scope Constant Predicate n)
    (formula : Formula Constant Predicate n) :
    legacyFamily D constants predicates (.object scope)
        (.substitute formula ObjectSubstitution.weaken) =
      reindexDisplayed
        (totalProjection (ObjectInterpretation.objectFamily D (context D constants predicates scope)))
        (legacyFamily D constants predicates scope formula) := by
  change reindexDisplayed (_ ≫ _) _ = reindexDisplayed (_ ≫ _) _
  rw [tuple_weaken]

/-- Each proof variable denotes the evidence at its actual binding position.
The two weakening rules act through the corresponding context projections. -/
noncomputable def hypothesis : {n : Nat} → {scope : Scope Constant Predicate n} →
    {formula : Formula Constant Predicate n} → Hypothesis scope formula →
      (legacyFamily D constants predicates scope formula).sections
  | _, _, _, .here scope formula => presheafVariable (legacyFamily D constants predicates scope formula)
  | _, _, _, .proofThere old newFormula => reindexDisplayedSection
      (totalProjection (legacyFamily D constants predicates _ newFormula))
      (legacyFamily D constants predicates _ _) (hypothesis old)
  | _, _, _, .objectThere old => by
      rw [legacy_weaken]
      exact reindexDisplayedSection
        (totalProjection (ObjectInterpretation.objectFamily D (context D constants predicates _)))
        (legacyFamily D constants predicates _ _) (hypothesis old)

set_option backward.isDefEq.respectTransparency false in
theorem legacy_sigma {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) :
    legacyFamily D constants predicates scope (.sigma body) =
      sigmaDisplayed (ObjectInterpretation.objectFamily D (context D constants predicates scope))
        (legacyFamily D constants predicates (.object scope) body) := by
  change reindexDisplayed (tuple D constants predicates scope)
      (sigmaDisplayed _ _) = _
  rw [sigmaDisplayed_reindex]
  congr 1

variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (PresheafInterpretation.family D constants predicates formula).sections)

noncomputable def objectSection {n : Nat} (scope : Scope Constant Predicate n) (term : ObjectTerm Constant n) :
    (ObjectInterpretation.objectFamily D (context D constants predicates scope)).sections :=
  reindexDisplayedSection (tuple D constants predicates scope)
    (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n))
    (ObjectInterpretation.objectSection D constants term)

theorem tuple_instantiate {n : Nat} (scope : Scope Constant Predicate n) (term : ObjectTerm Constant n) :
    sectionLift (ObjectInterpretation.objectFamily D (context D constants predicates scope))
        (objectSection D constants predicates scope term) ≫ tuple D constants predicates (.object scope) =
      tuple D constants predicates scope ≫
        ObjectInterpretation.substitution D constants (ObjectSubstitution.instantiate term) := by
  rw [ObjectInterpretation.substitution_instantiate]
  ext point value
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def piComparison {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) :
    piDisplayed (ObjectInterpretation.objectFamily D (context D constants predicates scope))
        (legacyFamily D constants predicates (.object scope) body) ≅
      legacyFamily D constants predicates scope (.pi body) := by
  change piDisplayed _
      (reindexDisplayed (objectTuple D (tuple D constants predicates scope))
        (PresheafInterpretation.family D constants predicates body)) ≅ _
  rw [objectTuple_eq_total]
  exact piSubstitutionIso (tuple D constants predicates scope)
    (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n))
    (PresheafInterpretation.family D constants predicates body)

noncomputable def abstraction {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (branch : (legacyFamily D constants predicates (.object scope) body).sections) :
    (legacyFamily D constants predicates scope (.pi body)).sections :=
  (Functor.sectionsFunctor _).map (piComparison D constants predicates scope body).hom
    (lamDisplayed branch)

set_option backward.isDefEq.respectTransparency false in
noncomputable def opening {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (branch : (legacyFamily D constants predicates (.object scope) body).sections)
    (argument : ObjectTerm Constant n) :
    (legacyFamily D constants predicates scope (.substitute body (ObjectSubstitution.instantiate argument))).sections := by
  have opened := reindexDisplayedSection
    (sectionLift (ObjectInterpretation.objectFamily D (context D constants predicates scope))
      (objectSection D constants predicates scope argument))
    (legacyFamily D constants predicates (.object scope) body) branch
  change (reindexDisplayed (tuple D constants predicates scope ≫
    ObjectInterpretation.substitution D constants (ObjectSubstitution.instantiate argument))
      (PresheafInterpretation.family D constants predicates body)).sections
  rw [← tuple_instantiate]
  exact opened

set_option backward.isDefEq.respectTransparency false in
noncomputable def application {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (function : (legacyFamily D constants predicates scope (.pi body)).sections)
    (argument : ObjectTerm Constant n) :
    (legacyFamily D constants predicates scope (.substitute body (ObjectSubstitution.instantiate argument))).sections := by
  have applied := appDisplayed
    ((Functor.sectionsFunctor _).map (piComparison D constants predicates scope body).inv function)
    (objectSection D constants predicates scope argument)
  change (reindexDisplayed (tuple D constants predicates scope ≫
    ObjectInterpretation.substitution D constants (ObjectSubstitution.instantiate argument))
      (PresheafInterpretation.family D constants predicates body)).sections
  rw [← tuple_instantiate]
  exact applied

set_option backward.isDefEq.respectTransparency false in
theorem application_abstraction {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (branch : (legacyFamily D constants predicates (.object scope) body).sections)
    (argument : ObjectTerm Constant n) :
    application D constants predicates scope body (abstraction D constants predicates scope body branch) argument =
      opening D constants predicates scope body branch argument := by
  have cancel : (Functor.sectionsFunctor _).map (piComparison D constants predicates scope body).inv
      (abstraction D constants predicates scope body branch) = lamDisplayed branch := by
    change (Functor.sectionsFunctor _).map (piComparison D constants predicates scope body).inv
      ((Functor.sectionsFunctor _).map (piComparison D constants predicates scope body).hom
        (lamDisplayed branch)) = _
    exact ((Functor.sectionsFunctor _).mapIso
      (piComparison D constants predicates scope body)).hom_inv_id_apply (lamDisplayed branch)
  unfold application
  rw [cancel, pi_beta]
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def pairing {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) (first : ObjectTerm Constant n)
    (second : (legacyFamily D constants predicates scope
      (.substitute body (ObjectSubstitution.instantiate first))).sections) :
    (legacyFamily D constants predicates scope (.sigma body)).sections := by
  rw [legacy_sigma]
  apply sigmaDisplayedPair _ _ (objectSection D constants predicates scope first)
  change (reindexDisplayed
    (sectionLift _ (objectSection D constants predicates scope first) ≫ tuple D constants predicates (.object scope))
    (PresheafInterpretation.family D constants predicates body)).sections
  rw [tuple_instantiate]
  exact second

/-- Contextual evidence is interpreted rule by rule. Supplying primitive
declaration meanings does not supply a global soundness or substitution law. -/
noncomputable def evidence : {n : Nat} → {scope : Scope Constant Predicate n} →
    {formula : Formula Constant Predicate n} → ScopedEvidence Declaration scope formula →
      (legacyFamily D constants predicates scope formula).sections
  | _, _, _, .hypothesis assumption => hypothesis D constants predicates assumption
  | _, _, _, .authored scope term => reindexDisplayedSection (tuple D constants predicates scope)
      (PresheafInterpretation.family D constants predicates _) (PresheafInterpretation.proof D constants predicates declarations term)
  | _, scope, _, .lam branch => abstraction D constants predicates scope _ (evidence branch)
  | _, scope, _, .app function argument => application D constants predicates scope _ (evidence function) argument
  | _, scope, _, .instantiate branch argument => opening D constants predicates scope _ (evidence branch) argument
  | _, scope, _, .pair first second => pairing D constants predicates scope _ first (evidence second)

/-- Generated contextual beta and constructor congruence use the actual
native comparison and binder-opening map, with no assumed soundness field. -/
theorem evidence_equation_sound {n : Nat} {scope : Scope Constant Predicate n}
    {formula : Formula Constant Predicate n} {first second : ScopedEvidence Declaration scope formula}
    (equation : EvidenceEquation first second) :
    evidence D constants predicates declarations first = evidence D constants predicates declarations second := by
  induction equation with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | authored scope equality =>
      exact congrArg (reindexDisplayedSection (tuple D constants predicates scope) _)
        (PresheafInterpretation.equation_sound D constants predicates declarations equality)
  | lam _ ih => exact congrArg (abstraction D constants predicates _ _) ih
  | app _ argument ih => exact congrArg (fun function => application D constants predicates _ _ function argument) ih
  | instantiate _ argument ih => exact congrArg (fun branch => opening D constants predicates _ _ branch argument) ih
  | pair argument _ ih => exact congrArg (pairing D constants predicates _ _ argument) ih
  | beta branch argument => exact application_abstraction D constants predicates _ _ (evidence D constants predicates declarations branch) argument

end Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation
