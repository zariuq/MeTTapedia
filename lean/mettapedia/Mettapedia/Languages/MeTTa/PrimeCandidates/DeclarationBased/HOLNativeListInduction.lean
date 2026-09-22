import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListDeclarationInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedHOLProofRules

/-!
# Native elimination discharges the HOL predicate-induction input

The predicate is a native function from actual Lists to the retained HOL
proposition carrier. Its decoded family is the motive of the actual native
List eliminator. The induction input is constructed from that eliminator;
no induction-shaped declaration is promoted to a recursion principle.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListInduction

open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.SchemaElaboration NativeIndexedFamilies IntrinsicMaps RussellTarski
open HOLNativeListConstantBodies
open FormationSensitiveHOLProofFamily (proof universalProposition implicationFamily)
open FormationSensitiveHOLUniformList (rawImp)

namespace ProofRules
export FormationSensitiveMixedHOLProofRules
  (proof_formed implication_proposition implication_conversion universal_lambda_proposition
   universal_lambda_conversion universal_intro implication_intro)
end ProofRules

def motive {n : Nat} (predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (proof (.app (rename wk predicate) (.var 0)))

def stepFormula {n : Nat} (element predicate : Tower.Tm n) : Tower.Tm n :=
  universalProposition element (.lam
    (universalProposition (Intrinsic.listApp (rename wk element)) (.lam
      (rawImp (.app (rename wk (rename wk predicate)) (.var 0))
        (.app (rename wk (rename wk predicate))
          (Intrinsic.consApp (rename wk (rename wk element)) (.var (Fin.succ 0)) (.var 0)))))))

def allFormula {n : Nat} (element predicate : Tower.Tm n) : Tower.Tm n :=
  universalProposition (Intrinsic.listApp element)
    (.lam (.app (rename wk predicate) (.var 0)))

def bodyFormula {n : Nat} (element predicate : Tower.Tm n) : Tower.Tm n :=
  rawImp (.app predicate (Intrinsic.nilApp element))
    (rawImp (stepFormula element predicate) (allFormula element predicate))

def inductionFormula {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  universalProposition (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))
    (.lam (bodyFormula (rename wk element) (.var 0)))

theorem predicate_application {n : Nat} {Γ : Tower.Ctx n} {element predicate list : Tower.Tm n}
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop)))
    (listTyped : Typing Γ list (Intrinsic.listApp element)) :
    Typing Γ (.app predicate list) (.const `HOLUniformList.prop) := by
  simpa only [arrow, inst0_rename_wk] using FormationSensitive.Typing.appElim predicateTyped listTyped

theorem cons_application {n : Nat} {Γ : Tower.Ctx n} {element head tail : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (headTyped : Typing Γ head element) (tailTyped : Typing Γ tail (Intrinsic.listApp element)) :
    Typing Γ (Intrinsic.consApp element head tail) (Intrinsic.listApp element) := by
  have constant := FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.consConstant_typed Γ)
  have bodyAsArrows : Intrinsic.consBodyType =
      arrow (.var 0) (arrow (Intrinsic.listApp (.var 0)) (Intrinsic.listApp (.var 0))) := by decide
  have first := FormationSensitive.Typing.appElim constant elementTyped
  change Typing Γ (.app (.const Intrinsic.consName) element)
    (inst0 element (rename (liftRen Fin.elim0) Intrinsic.consBodyType)) at first
  have firstNormalized : Typing Γ (.app (.const Intrinsic.consName) element)
      (arrow element (arrow (Intrinsic.listApp element) (Intrinsic.listApp element))) := by
    simpa [bodyAsArrows, liftClosed, inst0, subst0] using first
  have second := FormationSensitive.Typing.appElim firstNormalized headTyped
  rw [inst0_rename_wk] at second
  simpa only [Intrinsic.consApp, arrow, inst0_rename_wk] using
    FormationSensitive.Typing.appElim second tailTyped

theorem motive_typed {n : Nat} {Γ : Tower.Ctx n} {element predicate : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing Γ (motive predicate) (.pi (Intrinsic.listApp element) (sortTm Tower.zero)) := by
  apply FormationSensitive.Typing.lamIntro
    (.piForm (list_typed elementTyped) (.sort Tower.zero) (.headType (.sort Tower.zero))
      (.sort (.succ Tower.zero)) (.sorts Tower.zero (.succ Tower.zero))) (.sort _)
  apply ProofRules.proof_formed
  exact predicate_application predicateTyped.weaken (.var 0)

theorem motive_beta {n : Nat} (predicate list : Tower.Tm n) :
    Conv rules.headEq (.app (motive predicate) list) (proof (.app predicate list))
      rules.computation := by
  have opened : inst0 list (proof (.app (rename wk predicate) (.var 0))) =
      proof (.app predicate list) := by
    change proof (.app (inst0 list (rename wk predicate)) list) = _
    rw [inst0_rename_wk]
  simpa only [motive, opened] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation)
      (headEq := rules.headEq) (proof (.app (rename wk predicate) (.var 0))) list))

@[simp] theorem motive_rename {n m : Nat} (rho : Ren n m) (predicate : Tower.Tm n) :
    rename rho (motive predicate) = motive (rename rho predicate) := by
  simp [motive, rename, rename_comp, liftRen, wk]

theorem step_decodes {n : Nat} (element predicate : Tower.Tm n) :
    Conv rules.headEq (proof (stepFormula element predicate))
      (FormationSensitiveMixedListElimination.consCaseType element (motive predicate)) rules.computation := by
  refine .trans _ _ _ (ProofRules.universal_lambda_conversion _ _) ?_
  apply Conv.congPi (.refl _)
  refine .trans _ _ _ (ProofRules.universal_lambda_conversion _ _) ?_
  apply Conv.congPi (.refl _)
  refine .trans _ _ _ (ProofRules.implication_conversion _ _) ?_
  simp only [implicationFamily, motive_rename]
  apply Conv.congPi
  · exact (motive_beta (rename wk (rename wk predicate)) (.var 0)).symm
  · have one : Fin.succ (0 : Fin (n + 2)) = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : 1 < n + 3)]
    have two : Fin.succ (Fin.succ (0 : Fin (n + 1))) = (2 : Fin (n + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
    simpa only [FormationSensitiveHOLProofFamily.proof_rename, Intrinsic.consApp,
      rename, motive_rename, wk, one, two]
      using (motive_beta (rename wk (rename wk (rename wk predicate)))
        (Intrinsic.consApp (rename wk (rename wk (rename wk element))) (.var 2) (.var 1))).symm

@[simp] theorem stepFormula_rename {n m : Nat} (rho : Ren n m) (element predicate : Tower.Tm n) :
    rename rho (stepFormula element predicate) =
      stepFormula (rename rho element) (rename rho predicate) := by
  simp only [stepFormula, universalProposition, rawImp, Intrinsic.consApp, Intrinsic.listApp,
    rename, rename_comp, liftRen, wk, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem allFormula_rename {n m : Nat} (rho : Ren n m) (element predicate : Tower.Tm n) :
    rename rho (allFormula element predicate) =
      allFormula (rename rho element) (rename rho predicate) := by
  simp [allFormula, universalProposition, Intrinsic.listApp, rename, rename_comp, liftRen, wk]

@[simp] theorem bodyFormula_rename {n m : Nat} (rho : Ren n m) (element predicate : Tower.Tm n) :
    rename rho (bodyFormula element predicate) =
      bodyFormula (rename rho element) (rename rho predicate) := by
  simp only [bodyFormula, rawImp, rename, stepFormula_rename, allFormula_rename, Intrinsic.nilApp]

theorem stepFormula_typed {n : Nat} {Γ : Tower.Ctx n} {element predicate : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing Γ (stepFormula element predicate) (.const `HOLUniformList.prop) := by
  apply ProofRules.universal_lambda_proposition elementTyped
  apply ProofRules.universal_lambda_proposition (list_typed elementTyped.weaken)
  have ep := elementTyped.weaken (extension := element)
  have epp := ep.weaken (extension := Intrinsic.listApp (rename wk element))
  have pp := predicateTyped.weaken (extension := element)
  have ppp := pp.weaken (extension := Intrinsic.listApp (rename wk element))
  apply ProofRules.implication_proposition
  · exact predicate_application ppp (.var 0)
  · exact predicate_application ppp (cons_application epp (.var 1) (.var 0))

theorem allFormula_typed {n : Nat} {Γ : Tower.Ctx n} {element predicate : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing Γ (allFormula element predicate) (.const `HOLUniformList.prop) := by
  apply ProofRules.universal_lambda_proposition (list_typed elementTyped)
  exact predicate_application predicateTyped.weaken (.var 0)

theorem bodyFormula_typed {n : Nat} {Γ : Tower.Ctx n} {element predicate : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing Γ (bodyFormula element predicate) (.const `HOLUniformList.prop) :=
  ProofRules.implication_proposition (predicate_application predicateTyped (nil_typed elementTyped))
    (ProofRules.implication_proposition (stepFormula_typed elementTyped predicateTyped)
      (allFormula_typed elementTyped predicateTyped))

theorem inductionFormula_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyped : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ (inductionFormula element) (.const `HOLUniformList.prop) := by
  apply ProofRules.universal_lambda_proposition (pi_zero (list_typed elementTyped) (proposition_typed _))
  exact bodyFormula_typed elementTyped.weaken (.var 0)

/-- Native List elimination uses the decoded predicate as its actual dependent
motive. The step input is converted through the two established decoder rules. -/
theorem eliminate_typed {n : Nat} {Γ : Tower.Ctx n}
    {element predicate base step list : Tower.Tm n}
    (contextFormed : ContextFormation rules Γ)
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop)))
    (baseTyped : Typing Γ base (proof (.app predicate (Intrinsic.nilApp element))))
    (stepTyped : Typing Γ step (proof (stepFormula element predicate)))
    (listTyped : Typing Γ list (Intrinsic.listApp element)) :
    Typing Γ (Intrinsic.eliminateApp element (motive predicate) base step list)
      (proof (.app predicate list)) := by
  have motiveTyped := motive_typed elementTyped predicateTyped
  have baseAtMotive : Typing Γ base (.app (motive predicate) (Intrinsic.nilApp element)) :=
    .conv baseTyped
      (FormationSensitiveMixedListElimination.result_formed motiveTyped (nil_typed elementTyped))
      (.sort Tower.zero) (motive_beta _ _).symm
  obtain ⟨u, universeWitness, consFormed⟩ :=
    HOLNativeListLength.consType_formed contextFormed elementTyped motiveTyped baseAtMotive
  have stepAtMotive : Typing Γ step
      (FormationSensitiveMixedListElimination.consCaseType element (motive predicate)) :=
    .conv stepTyped consFormed universeWitness (step_decodes _ _)
  have eliminated := FormationSensitiveMixedListElimination.eliminateApp_typed
    elementTyped motiveTyped baseAtMotive stepAtMotive listTyped
  exact .conv eliminated (ProofRules.proof_formed (predicate_application predicateTyped listTyped))
    (.sort Tower.zero) (motive_beta _ _)

def bodyWitness {n : Nat} (element predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam
    (Intrinsic.eliminateApp (rename wk (rename wk (rename wk element)))
      (motive (rename wk (rename wk (rename wk predicate))))
      (.var (Fin.succ (Fin.succ 0))) (.var (Fin.succ 0)) (.var 0))))

theorem bodyWitness_typed {n : Nat} {Γ : Tower.Ctx n} {element predicate : Tower.Tm n}
    (contextFormed : ContextFormation rules Γ)
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (predicateTyped : Typing Γ predicate (arrow (Intrinsic.listApp element) (.const `HOLUniformList.prop))) :
    Typing Γ (bodyWitness element predicate) (proof (bodyFormula element predicate)) := by
  have baseFormed := predicate_application predicateTyped (nil_typed elementTyped)
  have stepFormed := stepFormula_typed elementTyped predicateTyped
  have allFormed := allFormula_typed elementTyped predicateTyped
  apply ProofRules.implication_intro baseFormed (ProofRules.implication_proposition stepFormed allFormed)
  simp only [FormationSensitiveHOLProofFamily.proof_rename, rawImp, rename,
    stepFormula_rename, allFormula_rename]
  let Γz := Ctx.snoc Γ (proof (.app predicate (Intrinsic.nilApp element)))
  have ez : Typing Γz (rename wk element) (sortTm Tower.zero) := elementTyped.weaken
  have pz : Typing Γz (rename wk predicate)
      (arrow (Intrinsic.listApp (rename wk element)) (.const `HOLUniformList.prop)) := predicateTyped.weaken
  have ΓzFormed : ContextFormation rules Γz :=
    .snoc contextFormed (ProofRules.proof_formed baseFormed) (.sort Tower.zero)
  apply ProofRules.implication_intro (stepFormula_typed ez pz) (allFormula_typed ez pz)
  simp only [FormationSensitiveHOLProofFamily.proof_rename, allFormula_rename]
  let Γzs := Ctx.snoc Γz (proof (stepFormula (rename wk element) (rename wk predicate)))
  have ezs : Typing Γzs (rename wk (rename wk element)) (sortTm Tower.zero) := ez.weaken
  have pzs : Typing Γzs (rename wk (rename wk predicate))
      (arrow (Intrinsic.listApp (rename wk (rename wk element))) (.const `HOLUniformList.prop)) := pz.weaken
  have ΓzsFormed : ContextFormation rules Γzs :=
    .snoc ΓzFormed (ProofRules.proof_formed (stepFormula_typed ez pz)) (.sort Tower.zero)
  apply ProofRules.universal_intro (list_typed ezs)
    (predicate_application pzs.weaken (.var 0))
  let Γzsx := Ctx.snoc Γzs (Intrinsic.listApp (rename wk (rename wk element)))
  have ex : Typing Γzsx (rename wk (rename wk (rename wk element))) (sortTm Tower.zero) := ezs.weaken
  have px : Typing Γzsx (rename wk (rename wk (rename wk predicate)))
      (arrow (Intrinsic.listApp (rename wk (rename wk (rename wk element))))
        (.const `HOLUniformList.prop)) := pzs.weaken
  have ΓzsxFormed : ContextFormation rules Γzsx :=
    .snoc ΓzsFormed (list_typed ezs) (.sort Tower.zero)
  apply eliminate_typed ΓzsxFormed ex px
  · have baseVar := FormationSensitive.Typing.var (R := rules) (Γ := Γzsx)
      (Fin.succ (Fin.succ (0 : Fin (n + 1))))
    simpa only [Γzsx, Γzs, Γz, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_zero,
      FormationSensitiveHOLProofFamily.proof, Intrinsic.nilApp, rename] using baseVar
  · have stepVar := FormationSensitive.Typing.var (R := rules) (Γ := Γzsx)
      (Fin.succ (0 : Fin (n + 2)))
    simpa only [Γzsx, Γzs, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_zero,
      FormationSensitiveHOLProofFamily.proof_rename, stepFormula_rename] using stepVar
  · exact .var 0

def inductionWitness {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .lam (bodyWitness (rename wk element) (.var 0))

theorem inductionWitness_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (contextFormed : ContextFormation rules Γ)
    (elementTyped : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ (inductionWitness element) (proof (inductionFormula element)) := by
  have predicateFormed := pi_zero (list_typed elementTyped) (proposition_typed _)
  apply ProofRules.universal_intro predicateFormed
    (bodyFormula_typed elementTyped.weaken (.var 0))
  exact bodyWitness_typed (.snoc contextFormed predicateFormed (.sort Tower.zero))
    elementTyped.weaken (.var 0)

theorem source_induction_represented :
    HOLLeibnizNativeProofTranslation.represent
      (Mettapedia.Logic.HOL.UniformListInduction.inductionPrinciple (Γ := [])) =
      some (FormationSensitiveHOLUniformList.rawInductionPrinciple : Tower.Tm 0) := rfl

theorem expand_rawAll {n : Nat} (element : Tower.Tm 0)
    (type : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (body : Tower.Tm (n + 1)) :
    ConstantExpansion.expand (bodies element) (FormationSensitiveHOLUniformList.rawAll type body) =
      universalProposition (FormationSensitiveHOLInterface.typeAt (types element) n type)
        (.lam (ConstantExpansion.expand (bodies element) body)) := by
  unfold FormationSensitiveHOLUniformList.rawAll
  simp only [ConstantExpansion.expand,
    FormationSensitiveHOLUniformList.universal, expand_typeAt, bodies_universal,
    universalProposition, liftClosed, rename, FormationSensitiveHOLInterface.typeAt_rename]

theorem source_induction_expanded {n : Nat} (element : Tower.Tm 0) :
    ConstantExpansion.expand (bodies element)
      (FormationSensitiveHOLUniformList.rawInductionPrinciple : Tower.Tm n) =
      inductionFormula (liftClosed element) := by
  simp [FormationSensitiveHOLUniformList.rawInductionPrinciple,
    FormationSensitiveHOLUniformList.rawInductionStep, expand_rawAll,
    FormationSensitiveHOLUniformList.rawImp, FormationSensitiveHOLUniformList.rawNil,
    FormationSensitiveHOLUniformList.rawCons, ConstantExpansion.expand, bodies_nil, bodies_cons,
    FormationSensitiveHOLInterface.typeAt, types, consBody,
    inductionFormula, bodyFormula, stepFormula, allFormula, universalProposition,
    Intrinsic.consApp, Intrinsic.nilApp, Intrinsic.listApp, arrow,
    liftClosed, rename, rename_comp, wk]
  repeat' constructor
  all_goals
    apply rename_ext
    intro index
    exact Fin.elim0 index

theorem original_induction_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ proposition : Tower.Tm 0,
      HOLLeibnizNativeProofTranslation.represent
        (Mettapedia.Logic.HOL.UniformListInduction.inductionPrinciple (Γ := [])) = some proposition ∧
      Typing .nil (inductionWitness (liftClosed element))
        (ConstantExpansion.expand (bodies element) (proof proposition)) := by
  refine ⟨_, source_induction_represented, ?_⟩
  have lifted : Typing .nil (liftClosed element) (sortTm Tower.zero) :=
    FormationSensitiveHOLInterface.closed_typed elementTyped .nil
  have admitted := inductionWitness_typed .nil lifted
  simpa only [proof, ConstantExpansion.expand, bodies_proof, liftClosed, rename,
    source_induction_expanded] using admitted

/-- The base branch is selected by the actual native List computation. -/
theorem native_nil_step {n : Nat} (element predicate base step : Tower.Tm n) :
    Step rules.headEq
      (Intrinsic.eliminateApp element (motive predicate) base step (Intrinsic.nilApp element))
      base rules.computation :=
  .root (.inherited (.declared ⟨.list (.nil element (motive predicate) base step)⟩))

/-- The cons branch receives the actual recursively computed predicate proof. -/
theorem native_cons_step {n : Nat} (element predicate base step head tail : Tower.Tm n) :
    Step rules.headEq
      (Intrinsic.eliminateApp element (motive predicate) base step (Intrinsic.consApp element head tail))
      (.app (.app (.app step head) tail)
        (Intrinsic.eliminateApp element (motive predicate) base step tail)) rules.computation :=
  .root (.inherited (.declared ⟨.list (.cons element (motive predicate) base step head tail)⟩))

#print axioms motive_typed
#print axioms motive_beta
#print axioms step_decodes
#print axioms inductionFormula_typed
#print axioms eliminate_typed
#print axioms bodyWitness_typed
#print axioms inductionWitness_typed
#print axioms source_induction_expanded
#print axioms original_induction_input
#print axioms native_nil_step
#print axioms native_cons_step

end HOLNativeListInduction
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
