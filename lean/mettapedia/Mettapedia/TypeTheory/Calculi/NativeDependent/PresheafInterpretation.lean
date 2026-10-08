import Mettapedia.TypeTheory.Calculi.NativeDependent.ObjectInterpretation
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafSigmaElimination

/-!
# Native interpretation of the scoped quantifier judgment presentation

Atomic predicates are arbitrary displayed families over an arbitrary object
presheaf. The independently authored object/formula/proof grammars are
interpreted by the existing dependent native Pi and Sigma constructions.
Only declaration meanings are supplied; the interpretation of every proof
constructor and soundness of the generated beta/congruence equations are
constructed here.

Products under substitution use their canonical comparison isomorphisms.
The formula presentation is the fixed-object-sort quantified fragment;
these theorems do not assert classifying initiality for a complete CwF.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafPi
open Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open ObjectInterpretation

universe u w
variable {C : Type u} [Category.{u} C]
variable {Constant Predicate : Type u}
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u, u, u, u} D)

/-- Dependent formula interpretation uses native families, retaining their
actual witness types and substitution action. -/
noncomputable def family : {n : Nat} → Formula Constant Predicate n →
    DisplayedFamily.{u, u, u, u} (context D n)
  | _, .atom name argument => reindexDisplayed (term D constants argument) (predicates name)
  | n, .pi body => piDisplayed (objectFamily D (context D n)) (family body)
  | n, .sigma body => sigmaDisplayed (objectFamily D (context D n)) (family body)
  | _, .substitute body replacements => reindexDisplayed (substitution D constants replacements)
      (family body)

set_option backward.isDefEq.respectTransparency false in
/-- Actual object substitution under a product binder uses the already
constructed native right-Kan base-change comparison. -/
noncomputable def piSubstitution {n m : Nat}
    (body : Formula Constant Predicate (m + 1)) (replacements : ObjectSubstitution Constant n m) :
    family D constants predicates (.pi (.substitute body (ObjectSubstitution.lift replacements))) ≅
      family D constants predicates (.substitute (.pi body) replacements) := by
  change piDisplayed (objectFamily D (context D n))
    (reindexDisplayed (substitution D constants (ObjectSubstitution.lift replacements))
      (family D constants predicates body)) ≅ _
  rw [substitution_lift]
  exact piSubstitutionIso (substitution D constants replacements)
    (objectFamily D (context D m)) (family D constants predicates body)

set_option backward.isDefEq.respectTransparency false in
/-- The sum's concrete native representative is strictly stable under
object substitution; neither coordinate is discarded. -/
theorem sigmaSubstitution {n m : Nat}
    (body : Formula Constant Predicate (m + 1)) (replacements : ObjectSubstitution Constant n m) :
    family D constants predicates (.sigma (.substitute body (ObjectSubstitution.lift replacements))) =
      family D constants predicates (.substitute (.sigma body) replacements) := by
  change sigmaDisplayed (objectFamily D (context D n))
    (reindexDisplayed (substitution D constants (ObjectSubstitution.lift replacements))
      (family D constants predicates body)) = _
  rw [substitution_lift]
  exact (sigmaDisplayed_reindex (substitution D constants replacements)
    (objectFamily D (context D m)) (family D constants predicates body)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Native application has exactly the authored opening-substitution type. -/
noncomputable def application {n : Nat} (body : Formula Constant Predicate (n + 1))
    (function : (family D constants predicates (.pi body)).sections)
    (argument : ObjectTerm Constant n) :
    (family D constants predicates (.substitute body
      (ObjectSubstitution.instantiate argument))).sections := by
  change (reindexDisplayed (substitution D constants (ObjectSubstitution.instantiate argument))
    (family D constants predicates body)).sections
  rw [substitution_instantiate]
  exact appDisplayed function (objectSection D constants argument)

set_option backward.isDefEq.respectTransparency false in
/-- Pair introduction retains a second proof in the type indexed by the
exact supplied first object. -/
noncomputable def pairing {n : Nat} (body : Formula Constant Predicate (n + 1))
    (first : ObjectTerm Constant n)
    (second : (family D constants predicates (.substitute body
      (ObjectSubstitution.instantiate first))).sections) :
    (family D constants predicates (.sigma body)).sections :=
  sigmaDisplayedPair (objectFamily D (context D n)) (family D constants predicates body)
    (objectSection D constants first) (by
      rw [← substitution_instantiate]
      exact second)

private theorem reindex_section_heq {P Q : Cᵒᵖ ⥤ Type u}
    {first second : P ⟶ Q} (same : first = second)
    (A : DisplayedFamily.{u, u, u, u} Q) (sectionValue : A.sections) :
    HEq (reindexDisplayedSection first A sectionValue)
      (reindexDisplayedSection second A sectionValue) := by
  cases same
  rfl

variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (family D constants predicates formula).sections)

/-- The interpreter is constructed recursively from individual rule
premises; whole-proof soundness is not an interpretation field. -/
noncomputable def proof : {n : Nat} → {formula : Formula Constant Predicate n} →
    Proof Declaration n formula → (family D constants predicates formula).sections
  | _, _, .declaration name => declarations name
  | _, _, .substitute body replacements => reindexDisplayedSection
      (substitution D constants replacements) (family D constants predicates _) (proof body)
  | _, _, .lam body => lamDisplayed (proof body)
  | _, _, .app function argument => application D constants predicates _ (proof function) argument
  | _, _, .pair first second => pairing D constants predicates _ first (proof second)

set_option backward.isDefEq.respectTransparency false in
/-- Beta on generated proof terms recovers the actual supplied natural
body after the same authored substitution is interpreted. -/
theorem beta {n : Nat} {body : Formula Constant Predicate (n + 1)}
    (bodyProof : Proof Declaration (n + 1) body) (argument : ObjectTerm Constant n) :
    proof D constants predicates declarations (.app (.lam bodyProof) argument) =
      proof D constants predicates declarations
        (.substitute bodyProof (ObjectSubstitution.instantiate argument)) := by
  change application D constants predicates body (lamDisplayed
    (proof D constants predicates declarations bodyProof)) argument = _
  unfold application
  rw [pi_beta]
  simp only [proof]
  apply eq_of_heq
  exact (cast_heq _ _).trans ((reindex_section_heq
    (substitution_instantiate D constants argument)
    (family D constants predicates body)
    (proof D constants predicates declarations bodyProof)).symm)

/-- Every generated equation is respected by the independently constructed
native interpreter. Congruence uses the actual constructor operations. -/
theorem equation_sound {n : Nat} {formula : Formula Constant Predicate n}
    {first second : Proof Declaration n formula} (equation : ProofEquation first second) :
    proof D constants predicates declarations first =
      proof D constants predicates declarations second := by
  induction equation with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | beta body argument => exact beta D constants predicates declarations body argument
  | substitute _ replacements ih =>
      exact congrArg (reindexDisplayedSection (substitution D constants replacements) _) ih
  | lam _ ih => exact congrArg lamDisplayed ih
  | app _ argument ih =>
      exact congrArg (fun function => application D constants predicates _ function argument) ih
  | pair argument _ ih => exact congrArg (pairing D constants predicates _ argument) ih

set_option backward.isDefEq.respectTransparency false in
/-- Eliminating the first coordinate of an interpreted pair returns its
exact authored object expression. -/
theorem pair_first {n : Nat} {body : Formula Constant Predicate (n + 1)}
    (first : ObjectTerm Constant n)
    (second : Proof Declaration n (.substitute body (ObjectSubstitution.instantiate first))) :
    sigmaDisplayedFst (proof D constants predicates declarations (.pair first second)) =
      objectSection D constants first := by
  exact sigmaDisplayedFst_pair _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Dependent second elimination preserves the supplied proof, with only
its explicit opening-substitution transport accounted for. -/
theorem pair_second {n : Nat} {body : Formula Constant Predicate (n + 1)}
    (first : ObjectTerm Constant n)
    (second : Proof Declaration n (.substitute body (ObjectSubstitution.instantiate first))) :
    HEq (sigmaDisplayedSnd (proof D constants predicates declarations (.pair first second)))
      (proof D constants predicates declarations second) := by
  have exactSecond := sigmaDisplayedSnd_pair_heq (objectFamily D (context D n))
    (family D constants predicates body) (objectSection D constants first)
    (by
      rw [← substitution_instantiate]
      exact proof D constants predicates declarations second)
  refine exactSecond.trans ?_
  exact cast_heq _ _

end Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation
