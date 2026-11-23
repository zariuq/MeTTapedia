import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
import Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend

/-!
# A root-only execution plan compiled to the transform step

Accepting a language is not accepting its plan: the plan also says where rules
may fire. `compilePlan` takes the same snapshot and permissions as
`GeneralExecutionAdmission.compile`. It admits them only when

* rules fire at the root alone, every authored rule is selected and no reflection
  profile is declared;
* there are no ambient names and no provider rows;
* the root profile of `GeneralCanonicalAgreement` holds at the sort;
* the authored language lowers (`RootRewritesOnTheStep.compile`).

For what it admits, the plan's own typed step from a well-sorted source is one
firing of the compiled program, in both directions (`planCorrespondence`). It is
the composite of that agreement with the root lowering. The observation is which
successors are possible.

A plan's step depends only on its snapshot, rules, equations, sites and reflection
profile (`gslt_eq_of_parts`), so the remaining permissions, and refining a plan by
structural descent, do not change it (`descentCorrespondence`).

Negative control: a language whose rules lower, under permissions that allow
rewriting inside a constructor, is refused (`Controls.inner_sites_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.RootPlansOnTheStep

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission (Snapshot Permissions)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (step_iff_mem_rootReducts)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan checkRootProfile RootProfile)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RootRewritesOnTheStep (encode rootStep_encode_iff rootStep_image rootStep_of_step compile_closed)

/-- Why a plan is not compiled by this lowering. -/
inductive Refusal where
  | sitesOtherThanRoot
  | rulesNotAllSelected
  | reflectionProfile
  | ambientNames
  | providerRows
  | outsideRootProfile
  | rules (reason : RootRewritesOnTheStep.Refusal)
  deriving DecidableEq, Repr

/-- **Compile what a plan executes**, or say why not. -/
def compilePlan (snapshot : Snapshot) (permissions : Permissions) (type : TypeExpr) :
    Except Refusal (List (Tm × Tm)) :=
  if permissions.sites = .rootOnly then
    if permissions.ruleIndices = none then
      if permissions.reflection = .empty then
        if snapshot.freeTypes = [] then
          if snapshot.provider = { signatures := [], rows := [] } then
            if checkRootProfile snapshot.language type then
              match RootRewritesOnTheStep.compile snapshot.language with
              | .ok schemas => .ok schemas
              | .error reason => .error (.rules reason)
            else .error .outsideRootProfile
          else .error .providerRows
        else .error .ambientNames
      else .error .reflectionProfile
    else .error .rulesNotAllSelected
  else .error .sitesOtherThanRoot

/-- The five parts of a plan that its step reads. -/
structure SameParts (first second : GeneralExecutionAdmission.Plan) : Prop where
  snapshots : first.snapshot = second.snapshot
  rules : first.rules = second.rules
  equations : first.equations = second.equations
  sites : first.permissions.sites = second.permissions.sites
  reflections : first.permissions.reflection = second.permissions.reflection

theorem SameParts.symm {first second : GeneralExecutionAdmission.Plan} (same : SameParts first second) :
    SameParts second first :=
  ⟨same.snapshots.symm, same.rules.symm, same.equations.symm, same.sites.symm, same.reflections.symm⟩

theorem SameParts.equation {first second : GeneralExecutionAdmission.Plan} (same : SameParts first second)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (converted : GeneralOccurrenceSemantics.Equation first bound type source target) :
    GeneralOccurrenceSemantics.Equation second bound type source target := by
  obtain ⟨snapshot, ⟨site, _, _, _, _, reflection⟩, rule, equation, _⟩ := first
  obtain ⟨snapshot', ⟨site', _, _, _, _, reflection'⟩, rule', equation', _⟩ := second
  obtain ⟨snapshots, rules, equations, sites, reflections⟩ := same
  simp only at snapshots rules equations sites reflections
  subst snapshots rules equations sites reflections
  obtain ⟨receipt, h, endpoint⟩ := converted
  exact ⟨receipt, ⟨h.job, h.sourceTyped, h.matched, h.capturedTyped, h.premises, h.completedTyped, h.reduct,
    h.accepted, h.endpoint⟩, endpoint⟩

theorem SameParts.primitive {first second : GeneralExecutionAdmission.Plan} (same : SameParts first second)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive first bound type source receipt) :
    GeneralOccurrenceSemantics.Primitive second bound type source receipt := by
  obtain ⟨snapshot, ⟨site, _, _, _, _, reflection⟩, rule, equation, _⟩ := first
  obtain ⟨snapshot', ⟨site', _, _, _, _, reflection'⟩, rule', equation', _⟩ := second
  obtain ⟨snapshots, rules, equations, sites, reflections⟩ := same
  simp only at snapshots rules equations sites reflections
  subst snapshots rules equations sites reflections
  exact fired

/-- **A plan's step depends only on five of its parts.** -/
theorem gslt_eq_of_parts {first second : GeneralExecutionAdmission.Plan} (same : SameParts first second)
    (bound : List TypeExpr) (type : TypeExpr) :
    GeneralOccurrenceSemantics.gslt first bound type = GeneralOccurrenceSemantics.gslt second bound type := by
  refine congrArg₂ (fun conversion primitive =>
    Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT conversion primitive GeneralRuleJobs.Receipt.target)
    ?_ ?_
  · funext source target
    exact propext ⟨same.equation, same.symm.equation⟩
  · funext source receipt
    exact propext ⟨same.primitive, same.symm.primitive⟩

/-- The same fact, read on single steps. -/
theorem SameParts.step {first second : GeneralExecutionAdmission.Plan} (same : SameParts first second)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (stepped : (GeneralOccurrenceSemantics.gslt first bound type).Step source target) :
    (GeneralOccurrenceSemantics.gslt second bound type).Step source target := by
  obtain ⟨representative, receipt, before, fired, after⟩ := stepped
  have lift : ∀ {left right : Pattern},
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation first bound type) left right →
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation second bound type) left right := by
    intro left right related
    induction related with
    | rel left right converted => exact .rel left right (same.equation converted)
    | refl term => exact .refl term
    | symm left right _ ih => exact .symm left right ih
    | trans left middle right _ _ first second => exact .trans left middle right first second
  exact ⟨representative, receipt, lift before, same.primitive fired, lift after⟩

variable {snapshot : Snapshot} {permissions : Permissions} {type : TypeExpr} {schemas : List (Tm × Tm)}

/-- What admission establishes: the plan steps as the root plan of its language
does, over the same snapshot, in the profile, and the language lowers. -/
theorem compilePlan_admitted (compiled : compilePlan snapshot permissions type = .ok schemas) :
    SameParts (GeneralExecutionAdmission.compile snapshot permissions) (rootPlan snapshot.language) ∧
      (GeneralExecutionAdmission.compile snapshot permissions).snapshot = (rootPlan snapshot.language).snapshot ∧
      RootProfile snapshot.language type ∧
      RootRewritesOnTheStep.compile snapshot.language = .ok schemas := by
  unfold compilePlan at compiled
  split at compiled
  · rename_i root
    split at compiled
    · rename_i everyRule
      split at compiled
      · rename_i unreflected
        split at compiled
        · rename_i unnamed
          split at compiled
          · rename_i unprovided
            split at compiled
            · rename_i checked
              split at compiled
              · rename_i lowered loweredIs
                cases compiled
                obtain ⟨language, freeTypes, provider⟩ := snapshot
                simp only at unnamed unprovided
                subst unnamed unprovided
                refine ⟨⟨rfl, ?_, ?_, root, unreflected⟩, rfl, RootProfile.of_check checked, loweredIs⟩
                · obtain ⟨_, _, _, _, _, _⟩ := permissions
                  simp only at everyRule
                  subst everyRule
                  rfl
                · have none_ : language.equations = [] := by
                    unfold RootRewritesOnTheStep.compile at loweredIs
                    split at loweredIs
                    · rename_i static
                      simp only [Bool.and_eq_true, List.isEmpty_iff] at static
                      exact static.1
                    · cases loweredIs
                  simp [rootPlan, GeneralExecutionAdmission.compile, GeneralExecutionAdmission.equations,
                    GeneralExecutionAdmission.selectedEquations, none_]
              · cases compiled
            · cases compiled
          · cases compiled
        · cases compiled
      · cases compiled
    · cases compiled
  · cases compiled

/-- A source the plan admits: well sorted in its own signature, at its sort. -/
def Admitted (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) : Prop :=
  OpenPatternWellSorted (GeneralExecutionAdmission.compile snapshot permissions).snapshot.language
    (GeneralExecutionAdmission.compile snapshot permissions).snapshot.free bound type source

/-- The plan's own step. -/
def planSystem (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr) (type : TypeExpr) : GSLT :=
  GeneralOccurrenceSemantics.gslt (GeneralExecutionAdmission.compile snapshot permissions) bound type

/-- **The plan's step is a root rewrite of the compiled schemas.** -/
theorem planStep_iff_rootStep (compiled : compilePlan snapshot permissions type = .ok schemas)
    (bound : List TypeExpr) {source target : Pattern}
    (admitted : Admitted snapshot permissions bound type source) :
    (planSystem snapshot permissions bound type).Step source target ↔
      RootStep schemas (encode source) (encode target) := by
  obtain ⟨same, snapshotSame, profile, lowered⟩ := compilePlan_admitted compiled
  unfold Admitted at admitted
  unfold planSystem
  rw [snapshotSame] at admitted
  refine Iff.trans ⟨same.step, same.symm.step⟩ ?_
  exact (profile.general_step_iff_rootReducts bound admitted).trans
    ((step_iff_mem_rootReducts (engineBasePremises Engine.RelationEnv.empty) snapshot.language
        profile.unconditional source target).symm.trans
      (rootStep_encode_iff lowered source target).symm)

/-- A step of an admitted plan keeps its sources admitted. -/
theorem admitted_of_planStep (compiled : compilePlan snapshot permissions type = .ok schemas)
    (bound : List TypeExpr) {source target : Pattern}
    (stepped : (planSystem snapshot permissions bound type).Step source target) :
    Admitted snapshot permissions bound type target := by
  obtain ⟨same, snapshotSame, profile, _⟩ := compilePlan_admitted compiled
  unfold planSystem at stepped
  unfold Admitted
  rw [snapshotSame]
  obtain ⟨representative, receipt, _, fired, after⟩ := same.step stepped
  have targetSame := profile.equivalence_is_equality bound after
  rw [← targetSame]
  exact (GeneralPlanEnvironment.typing_iff _ bound type receipt.target).mp fired.2.2.2.2

/-- **No firing leaves the plan.** A root rewrite of an admitted source is a step of the plan. -/
theorem rootStep_image_plan (compiled : compilePlan snapshot permissions type = .ok schemas)
    (bound : List TypeExpr) {source : Pattern} {row : Expr}
    (admitted : Admitted snapshot permissions bound type source)
    (stepped : RootStep schemas (encode source) row) :
    ∃ target, (planSystem snapshot permissions bound type).Step source target ∧ row = encode target := by
  obtain ⟨target, sourceStep, same⟩ :=
    rootStep_image (relEnv := Engine.RelationEnv.empty) (compilePlan_admitted compiled).2.2.2 stepped
  exact ⟨target, (planStep_iff_rootStep compiled bound admitted).mpr
    (rootStep_of_step (compilePlan_admitted compiled).2.2.2 sourceStep), same⟩

/-- An admitted source is hosted by its row. -/
def Hosted (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (row : Expr) : Prop :=
  Admitted snapshot permissions bound type source ∧ row = encode source

/-- The plan and root rewriting of rows. -/
def rowCorrespondence (bound : List TypeExpr) (compiled : compilePlan snapshot permissions type = .ok schemas) :
    OperationalCorrespondence (planSystem snapshot permissions bound type) (rootSystem schemas) where
  related := Hosted snapshot permissions bound type
  readStep := by
    rintro source row next ⟨admitted, same⟩ stepped
    have isRow : row = encode source := same
    subst isRow
    obtain ⟨target, planStep, targetRow⟩ := rootStep_image_plan compiled bound admitted stepped
    exact Or.inr ⟨target, planStep, admitted_of_planStep compiled bound planStep, targetRow⟩
  forward := by
    rintro source target row ⟨admitted, same⟩ stepped
    have isRow : row = encode source := same
    subst isRow
    exact ⟨encode target, (executionPath_nonempty_iff_multiStep (rootSystem schemas) _ _).mpr
      (.step ((planStep_iff_rootStep compiled bound admitted).mp stepped) (.refl _)),
      admitted_of_planStep compiled bound stepped, rfl⟩

/-- **An admitted execution plan and the transform step of its program**, in both directions. -/
def planCorrespondence {O : Type} [DecidableEq O] [Infinite O] (bound : List TypeExpr)
    (compiled : compilePlan snapshot permissions type = .ok schemas) :
    OperationalCorrespondence (planSystem snapshot permissions bound type) (stepSystem O (rootRules schemas)) :=
  (rowCorrespondence bound compiled).comp (rootCorrespondence (compile_closed (compilePlan_admitted compiled).2.2.2))

/-- **Refining a plan by structural descent does not change its step.** -/
theorem descent_system_eq (snapshot : Snapshot) (permissions : Permissions) (bound : List TypeExpr) (type : TypeExpr) :
    GeneralOccurrenceSemantics.gslt (StructuralDescent.Plan.compile snapshot permissions) bound type =
      planSystem snapshot permissions bound type := by
  unfold planSystem StructuralDescent.Plan.compile
  refine gslt_eq_of_parts ⟨StructuralDescent.Plan.snapshot_preserved _, StructuralDescent.Plan.rules_preserved _,
    StructuralDescent.Plan.equations_preserved _, ?_, ?_⟩ bound type
  · exact congrArg Permissions.sites (StructuralDescent.Plan.permissions_preserved _)
  · exact congrArg Permissions.reflection (StructuralDescent.Plan.permissions_preserved _)

/-- **An admitted plan refined by structural descent, and the transform step of its program.** -/
def descentCorrespondence {O : Type} [DecidableEq O] [Infinite O] (bound : List TypeExpr)
    (compiled : compilePlan snapshot permissions type = .ok schemas) :
    OperationalCorrespondence
      (GeneralOccurrenceSemantics.gslt (StructuralDescent.Plan.compile snapshot permissions) bound type)
      (stepSystem O (rootRules schemas)) :=
  descent_system_eq snapshot permissions bound type ▸ planCorrespondence bound compiled

/-! ## Controls -/

namespace Controls

/-- Whether a compilation succeeded. -/
def succeeds {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

theorem exists_of_succeeds {ε α : Type} {result : Except ε α} (success : succeeds result = true) :
    ∃ value, result = .ok value := by
  cases result with
  | ok value => exact ⟨value, rfl⟩
  | error => cases success

/-- **Positive**: the partial-recursive machine's plan, with its nineteen rules. -/
theorem partrec_admitted :
    ∃ schemas, compilePlan Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.permissions (.base "Cfg") = .ok schemas :=
  exists_of_succeeds (by cbv)

/-- **Positive**: the gate's branching plan, which is refined by structural descent
and omits the derived equations. -/
theorem branching_admitted :
    Complete.ClassesControls.branchingPlan = StructuralDescent.Plan.compile
        ⟨Complete.ClassesControls.branching, [], { signatures := [], rows := [] }⟩
        StructuralDescent.Controls.rootPermissions ∧
      ∃ schemas, compilePlan ⟨Complete.ClassesControls.branching, [], { signatures := [], rows := [] }⟩
        StructuralDescent.Controls.rootPermissions (.base "T") = .ok schemas :=
  ⟨rfl, exists_of_succeeds (by cbv)⟩

/-- The sum of two numerals, by two root rules. -/
def sum : LanguageDef where
  name := "Sum"
  types := ["Nat"]
  terms :=
    [{ label := "Zero", category := "Nat", params := [], syntaxPattern := [] },
     { label := "Succ", category := "Nat", params := [.simple "n" (.base "Nat")],
       syntaxPattern := [.nonTerminal "n"] },
     { label := "Add", category := "Nat", params := [.simple "m" (.base "Nat"), .simple "n" (.base "Nat")],
       syntaxPattern := [.nonTerminal "m", .nonTerminal "n"] }]
  equations := []
  rewrites :=
    [{ name := "add-zero", typeContext := [("y", .base "Nat")], premises := [],
       left := .apply "Add" [.apply "Zero" [], .fvar "y"], right := .fvar "y" },
     { name := "add-succ", typeContext := [("x", .base "Nat"), ("y", .base "Nat")], premises := [],
       left := .apply "Add" [.apply "Succ" [.fvar "x"], .fvar "y"],
       right := .apply "Succ" [.apply "Add" [.fvar "x", .fvar "y"]] }]

/-- `Succ(Add(Zero, Zero))`: its only redex is inside. -/
def innerRedex : Pattern := .apply "Succ" [.apply "Add" [.apply "Zero" [], .apply "Zero" []]]

/-- **Positive**: at the root alone, the plan is admitted. -/
theorem root_sum_admitted :
    ∃ schemas, compilePlan ⟨sum, [], { signatures := [], rows := [] }⟩ {sites := .rootOnly} (.base "Nat") =
      .ok schemas :=
  exists_of_succeeds (by cbv)

/-- **Negative**: the same language lowers, and its plan that rewrites at every
position is refused. -/
theorem inner_sites_refused :
    (∃ schemas, RootRewritesOnTheStep.compile sum = .ok schemas) ∧
      compilePlan ⟨sum, [], { signatures := [], rows := [] }⟩ {} (.base "Nat") =
        .error .sitesOtherThanRoot :=
  ⟨exists_of_succeeds (by cbv), rfl⟩

/-- **Why**: that plan has a site at the inner redex, which is stuck at the root. -/
theorem inner_site_lost :
    (GeneralTypedSites.generate sum (fun _ => none) .all [] (.base "Nat") innerRedex).any
        (fun site => site.address == [0]) = true ∧
      Match.rewriteStep sum innerRedex = [] := by
  decide +kernel

end Controls

#print axioms compilePlan_admitted
#print axioms planStep_iff_rootStep
#print axioms rootStep_image_plan
#print axioms planCorrespondence
#print axioms gslt_eq_of_parts
#print axioms descentCorrespondence
#print axioms Controls.branching_admitted
#print axioms Controls.partrec_admitted
#print axioms Controls.inner_sites_refused
#print axioms Controls.inner_site_lost

end Mettapedia.GSLT.Compilation.RootPlansOnTheStep
