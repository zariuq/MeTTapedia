import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Comparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Settler
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PurePackages
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvObject

/-!
# The hypotheses at the tree's qualified packages

The general theorems need, besides qualification, two things of a package and its executable normalizer:
strong normalization of typed terms (`TypedSN`) and a complete root evaluator (`RootComplete`).

* **The vectors package**: its root evaluator, the first of its fourteen rows that matches (`vecRoot`), is
  complete (`vecRoot_complete`): every root step of the package is an instance of a row (`vector_cover`), the
  rows have supported left sides whose variables cover their right sides (`vectors_admitted`, checked by the
  kernel), and for such a table the source-ordered selection finds a target exactly when a row has an
  instance (`first_has_target_iff_step`). So for the normalizer the settler, the converting step and the
  definition checker call (`vecReducer`), items 1, 2 and 4 hold under `TypedSN` of the package alone
  (`vectors_normalize_eventually`, `vectors_compare_eventually`, `vectors_types_eventually`). Strong
  normalization of the package's typed terms is not proved in the tree.
* **The executable package of the certified-transform program** has strongly normalizing typed terms
  (`executable_typedSN`): it is a sub-package of the object package, whose typed terms are strongly
  normalizing by the transport value model (`objectRules_sn`), and strong normalization descends to a
  package with fewer root steps. The tree has no root evaluator for it; with any complete one, items 1, 2
  and 4 hold (`executable_compare_eventually`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion AlgebraicSchema

/-! ## The vectors package -/

section Vectors

open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1)

/-- **The fourteen rows are admitted**: supported left sides, right variables covered by left ones. -/
theorem vectors_admitted : ExecutableSchemaSelection.Admitted Vectors.vectorEquations := by
  unfold ExecutableSchemaSelection.Admitted ExecutableSchemaSelection.GoodEntry
  decide

/-- **The vectors package's root evaluator is complete.** -/
theorem vecRoot_complete (lv : LevelExpr Nat) :
    RootComplete (TowerVectorsModel.rules lv) (Vectors.vecRoot lv) := by
  intro n t none' u step
  obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := Vectors.vector_cover lv step
  have found := (ExecutableSchemaSelection.first_has_target_iff_step vectors_admitted
    (Presentation.subst σ left)).mpr ⟨_, SchemaTable.step_of_mem _ rule σ⟩
  unfold Vectors.vecRoot at none'
  cases h : ExecutableSchemaSelection.first Vectors.vectorEquations (Presentation.subst σ left) with
  | fired receipt assigned => simp [h] at none'
  | unassigned receipt unassigned => simp [h, ExecutableSchemaSelection.Outcome.target?] at found
  | missed => simp [h, ExecutableSchemaSelection.Outcome.target?] at found

/-- **Item 2 for the vectors package**: under strong normalization of its typed terms, the normalizer the
tree calls returns the unique normal form of every typed term at some budget and at every larger one. -/
theorem vectors_normalize_eventually (sn : TypedSN Vectors.vecS.R) {n : Nat} {Γ : Ctx Tower.Head n}
    {t A : Tower.Tm n} (formed : CtxFormed Vectors.vecS.R Γ) (typed : Typed Vectors.vecS.R Γ t A) :
    ∃ fuel result, ContextualDependentExecutableJoin.Normal Vectors.vecS.R result.val ∧
      (∀ v, StrongNormalization.ReducesStar Vectors.vecS.R t v →
        ContextualDependentExecutableJoin.Normal Vectors.vecS.R v → v = result.val) ∧
      Typed Vectors.vecS.R Γ result.val A ∧ Equal Vectors.vecS.R Γ t result.val A ∧
      ∀ larger, fuel ≤ larger → Vectors.vecReducer level1 larger t = some result :=
  qualified_normalize_eventually (Vectors.vq level1) sn (Vectors.vecRoot level1) (vecRoot_complete level1)
    formed typed

/-- **Items 1 and 4 for the vectors package**: under strong normalization of its typed terms, the
executable comparison over the tree's normalizer accepts every pair of equal typed terms at some budget and
keeps its certificate at every larger one. -/
theorem vectors_compare_eventually (sn : TypedSN Vectors.vecS.R) {n : Nat} {Γ : Ctx Tower.Head n}
    {t u A : Tower.Tm n} (formed : CtxFormed Vectors.vecS.R Γ) (equal : Equal Vectors.vecS.R Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare Vectors.vecS.R (Vectors.vecReducer level1) larger Γ t u A = some certificate :=
  normalize_compare_eventually (Vectors.vq level1) sn (Vectors.vecRoot level1) (vecRoot_complete level1)
    formed equal

/-- **Type comparison for the vectors package**, under the same hypothesis. -/
theorem vectors_types_eventually (sn : TypedSN Vectors.vecS.R) {n : Nat} {Γ : Ctx Tower.Head n}
    {A B : Tower.Tm n} (formed : CtxFormed Vectors.vecS.R Γ) (equal : TypeEq Vectors.vecS.R Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types Vectors.vecS.R (Vectors.vecReducer level1) larger Γ A B = some certificate :=
  normalize_types_eventually (Vectors.vq level1) sn (Vectors.vecRoot level1) (vecRoot_complete level1)
    formed equal

end Vectors

/-! ## Strong normalization descends to sub-packages -/

/-- **Strong normalization of typed terms descends to a sub-package**: typings and formed contexts lift
along the inclusion, and a package with fewer root steps has fewer reductions. -/
theorem typedSN_of_sub {Head : Type} {R R' : Rules Head} (sub : RulesSub R R') (sn : TypedSN R') :
    TypedSN R := fun formed typed =>
  StrongNormalization.SN.of_rootSub (R' := R') (fun step => sub.computation step)
    (sn (formed.mono sub) (Derivable.mono sub typed))

/-! ## The executable package of the certified-transform program -/

section Executable

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram

/-- **The executable package's typed terms are strongly normalizing**: it is a sub-package of the object
package, whose typed terms are strongly normalizing by the transport value model. -/
theorem executable_typedSN : TypedSN ExecutableModel.rules :=
  typedSN_of_sub ExecutableModel.CodeModel.ConvRules.rules_sub_objectRules fun formed typed =>
    (ExecutableModel.objectRules_sn formed typed).1

/-- **Items 1 and 4 for the executable package**, for every complete root evaluator: the comparison over the
tree's normalizer accepts every pair of equal typed terms at some budget and at every larger one. -/
theorem executable_compare_eventually [DecidableRel (ExecutableModel.setting fun _ => 0).R.headEq]
    [∀ head, Decidable ((ExecutableModel.setting fun _ => 0).R.isUniverse head)]
    (root : RootEvaluator ExecutableModel.rules) (complete : RootComplete ExecutableModel.rules root)
    {n : Nat} {Γ : Ctx Tower.Head n} {t u A : Tower.Tm n}
    (formed : CtxFormed ExecutableModel.rules Γ) (equal : Equal ExecutableModel.rules Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare (ExecutableModel.setting fun _ => 0).R (normalize ExecutableModel.rules root) larger Γ t u A =
        some certificate :=
  normalize_compare_eventually executable_qualified executable_typedSN root complete formed equal

end Executable

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms vectors_admitted
#print axioms vecRoot_complete
#print axioms vectors_normalize_eventually
#print axioms vectors_compare_eventually
#print axioms vectors_types_eventually
#print axioms typedSN_of_sub
#print axioms executable_typedSN
#print axioms executable_compare_eventually
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
