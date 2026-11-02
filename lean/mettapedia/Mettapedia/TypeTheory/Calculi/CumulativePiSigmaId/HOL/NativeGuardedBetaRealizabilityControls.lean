import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateBetaRealizability
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedRealizabilityControls

/-!
# Guarded beta on an open value-dependent family

The context contains `A`, a family `F : A → U`, a point `x : A`, and
`f : Π y : A, F y`. The represented contraction `(λ y : A, f y) x`
retains the actual result guard `F x`. A separate annotation contraction
erases to no HOL step, distinguishing guarded root beta from unrestricted
strict simulation of annotated reduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedBetaRealizability.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading NativeNaturalVectorFamilies
open NativeGuardedRealizability.Controls
  (BaseSort Const raw profile lex roots number predicateType baseContext universeHead nextHead)
local infixr:60 " ⇒ " => HOL.Ty.arr

def levels := Programs.Annotated.levelModel profile
abbrev familyCarrier := number ⇒ predicateType

theorem universe_formed {n : Nat} (source : CCtx Tower.Head n) :
    CIsType (Programs.Annotated.church profile) source (.head universeHead) :=
  ⟨nextHead,by decide +kernel,.headType (by decide +kernel)⟩

def familyType : CTm Tower.Head 1 := .pi (.var 0) (.head universeHead)
def familyPredicate : HOL.Term Const [predicateType] (familyCarrier ⇒ .prop) :=
  HOL.PredicateProducts.pi (.var .vz) (HOL.PredicateProducts.full predicateType)
theorem familyType_read : Reads lex (Γ := [predicateType]) familyType familyPredicate := by
  have universeRead : Reads lex (Γ := [number,predicateType]) (.head universeHead)
      (HOL.PredicateProducts.full predicateType) :=
    Reads.head (lex := lex) (Γ := [number,predicateType]) (head := universeHead)
      (type := predicateType ⇒ .prop) (closed := HOL.PredicateProducts.full predicateType) (by decide +kernel)
  exact .product NativeGuardedRealizability.Controls.domain_read universeRead
theorem familyType_formed : CIsType (Programs.Annotated.church profile) baseContext.source familyType :=
  CIsType.pi levels NativeGuardedRealizability.Controls.domain_formed (universe_formed _)
def familyContext := baseContext.snoc familyPredicate familyType_read familyType_formed

def familyDomain : CTm Tower.Head 2 := .var 1
def familyDomainPredicate : HOL.Term Const [familyCarrier,predicateType] predicateType := .var (.vs .vz)
theorem familyDomain_read : Reads lex (Γ := [familyCarrier,predicateType]) familyDomain familyDomainPredicate :=
  Reads.var (lex := lex) (.vs .vz : HOL.Var [familyCarrier,predicateType] predicateType)
theorem familyDomain_formed : CIsType (Programs.Annotated.church profile) familyContext.source familyDomain :=
  ⟨universeHead,by decide +kernel,.var 1⟩
def argumentContext := familyContext.snoc familyDomainPredicate familyDomain_read familyDomain_formed

def functionType : CTm Tower.Head 3 := .pi (.var 2) (.app (.var 2) (.var 0))
def functionPredicate : HOL.Term Const [number,familyCarrier,predicateType] ((number ⇒ number) ⇒ .prop) :=
  HOL.PredicateProducts.pi (.var (.vs (.vs .vz))) (.app (.var (.vs (.vs .vz))) (.var .vz))
theorem functionType_read : Reads lex (Γ := [number,familyCarrier,predicateType]) functionType functionPredicate :=
  .product (Reads.var (lex := lex) (.vs (.vs .vz) : HOL.Var [number,familyCarrier,predicateType] predicateType))
    (.application (Reads.var (lex := lex) (.vs (.vs .vz) : HOL.Var [number,number,familyCarrier,predicateType] familyCarrier))
      (Reads.var (lex := lex) (.vz : HOL.Var [number,number,familyCarrier,predicateType] number)))
theorem functionDomain_formed : CIsType (Programs.Annotated.church profile) argumentContext.source (.var 2) :=
  ⟨universeHead,by decide +kernel,.var 2⟩
theorem functionFamily_formed : CIsType (Programs.Annotated.church profile)
    (.snoc argumentContext.source (.var 2)) (.app (.var 2) (.var 0)) := by
  have functionTyped : CTyped (Programs.Annotated.church profile) (.snoc argumentContext.source (.var 2))
      (.var 2) (.pi (.var 3) (.head universeHead)) := .var 2
  have argumentTyped : CTyped (Programs.Annotated.church profile) (.snoc argumentContext.source (.var 2))
      (.var 0) (.var 3) := .var 0
  exact ⟨universeHead,by decide +kernel,.appElim functionTyped argumentTyped⟩
theorem functionType_formed : CIsType (Programs.Annotated.church profile) argumentContext.source functionType :=
  CIsType.pi levels functionDomain_formed functionFamily_formed
def functionContext := argumentContext.snoc functionPredicate functionType_read functionType_formed

def domain : CTm Tower.Head 4 := .var 3
def domainPredicate : HOL.Term Const [number ⇒ number,number,familyCarrier,predicateType] predicateType :=
  .var (.vs (.vs (.vs .vz)))
theorem domain_read : Reads lex (Γ := [number ⇒ number,number,familyCarrier,predicateType]) domain domainPredicate :=
  Reads.var (lex := lex) (.vs (.vs (.vs .vz)) : HOL.Var [number ⇒ number,number,familyCarrier,predicateType] predicateType)
theorem domain_formed : CIsType (Programs.Annotated.church profile) functionContext.source domain :=
  ⟨universeHead,by decide +kernel,.var 3⟩
def bodyContext := functionContext.snoc domainPredicate domain_read domain_formed
def bodyFunction := GuardedRealizer.ofVariable roots bodyContext
  (.vs .vz : HOL.Var [number,number ⇒ number,number,familyCarrier,predicateType] (number ⇒ number))
def bodyArgument := GuardedRealizer.ofVariable roots bodyContext
  (.vz : HOL.Var [number,number ⇒ number,number,familyCarrier,predicateType] number)
def bodyValue := bodyFunction.application bodyArgument
def argumentValue := GuardedRealizer.ofVariable roots functionContext
  (.vs .vz : HOL.Var [number ⇒ number,number,familyCarrier,predicateType] number)
theorem family_formed : CIsType (Programs.Annotated.church profile) (.snoc functionContext.source domain)
    (.app (.var 3) (.var 0)) := by
  have functionTyped : CTyped (Programs.Annotated.church profile) (.snoc functionContext.source domain)
      (.var 3) (.pi (.var 4) (.head universeHead)) := .var 3
  have argumentTyped : CTyped (Programs.Annotated.church profile) (.snoc functionContext.source domain)
      (.var 0) (.var 4) := .var 0
  exact ⟨universeHead,by decide +kernel,.appElim functionTyped argumentTyped⟩

def redex := GuardedBeta.redex levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue
def reduct := GuardedBeta.reduct levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue
def targetStep := GuardedBeta.targetStep levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue
def targetExecution := GuardedBeta.targetExecution levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue

theorem redex_source_typed : CTyped (Programs.Annotated.church profile) functionContext.source
    (.app (.lam (.var 3) (.app (.var 1) (.var 0))) (.var 1)) (.app (.var 2) (.var 1)) := redex.typed
theorem reduct_source_typed : CTyped (Programs.Annotated.church profile) functionContext.source
    (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1)) := reduct.typed
theorem source_beta : CEqual (Programs.Annotated.church profile) functionContext.source
    (.app (.lam (.var 3) (.app (.var 1) (.var 0))) (.var 1))
    (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1)) :=
  GuardedBeta.sourceEquality levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue

def sourceBetaCertificate : Programs.Annotated.JudgmentReplay.Certificate profile := by
  annotated_certificate 8000 source_beta

theorem source_beta_checked : Programs.Annotated.JudgmentReplay.check profile sourceBetaCertificate
    (.equality functionContext.source (.app (.lam (.var 3) (.app (.var 1) (.var 0))) (.var 1))
      (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1))) = true := by decide +kernel

theorem changed_source_result_guard_refused : Programs.Annotated.JudgmentReplay.check profile sourceBetaCertificate
    (.equality functionContext.source (.app (.lam (.var 3) (.app (.var 1) (.var 0))) (.var 1))
      (.app (.var 0) (.var 1)) (.var 3)) = false := by decide +kernel

def resultPredicate : HOL.Term Const [number ⇒ number,number,familyCarrier,predicateType] predicateType :=
  .app (.var (.vs (.vs .vz))) (.var (.vs .vz))
theorem redex_guard : redex.predicate = resultPredicate := by
  have familyRead : Reads lex (Γ := [number,number ⇒ number,number,familyCarrier,predicateType])
      (.app (.var 3) (.var 0)) (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) :=
    .application (Reads.var (lex := lex)
      (.vs (.vs (.vs .vz)) : HOL.Var [number,number ⇒ number,number,familyCarrier,predicateType] familyCarrier))
      (Reads.var (lex := lex) (.vz : HOL.Var [number,number ⇒ number,number,familyCarrier,predicateType] number))
  have same := Reader.term_unique bodyValue.typeRead familyRead
  exact (GuardedBeta.guard levels domainPredicate domain_read domain_formed family_formed bodyValue argumentValue).trans
    ((congrArg (HOL.instantiate argumentValue.term) same).trans rfl)
theorem reduct_guard : reduct.predicate = resultPredicate := redex_guard
theorem execution_length : targetExecution.length = 1 := rfl

theorem body_free : bodyValue.Free :=
  GuardedRealizer.application_free bodyFunction bodyArgument
    (GuardedRealizer.ofVariable_free _ _ _) (GuardedRealizer.ofVariable_free _ _ _)
theorem argument_free : argumentValue.Free := GuardedRealizer.ofVariable_free _ _ _
theorem redex_free : redex.Free :=
  GuardedBeta.redex_free _ _ _ _ _ _ _ body_free argument_free
theorem reduct_free : reduct.Free :=
  GuardedBeta.reduct_free _ _ _ _ _ _ _ body_free argument_free

def weakening := GuardedSubstitution.weakening roots functionContext domainPredicate domain_read domain_formed
def substitutedStep := GuardedBeta.substitutedTargetStep levels domainPredicate domain_read domain_formed
  family_formed bodyValue argumentValue weakening
def substitutedExecution := targetExecution.subst (HOL.Subst.ofRename (HOL.Rename.weaken (σ := number)))
theorem substituted_execution_length : substitutedExecution.length = 1 := rfl
theorem substituted_redex_source_typed :
    CTyped (Programs.Annotated.church profile) bodyContext.source
      (.app (.lam (.var 4) (.app (.var 2) (.var 0))) (.var 2)) (.app (.var 3) (.var 2)) :=
  (redex.substitute weakening).typed
theorem substituted_reduct_source_typed :
    CTyped (Programs.Annotated.church profile) bodyContext.source
      (.app (.var 1) (.var 2)) (.app (.var 3) (.var 2)) :=
  (reduct.substitute weakening).typed

def annotationBefore : CTm Tower.Head 2 := .lam NativeGuardedRealizability.Controls.expandedType (.var 0)
def annotationAfter : CTm Tower.Head 2 := .lam (.var 1) (.var 0)
def annotationCode : HOL.Term Const [number,predicateType] (number ⇒ number) := .lam (.var .vz)

theorem annotation_source_step (root : CRootComputation Tower.Head) (headEq : Tower.Head → Tower.Head → Prop) :
    CStepCore root headEq annotationBefore annotationAfter :=
  .congLamDom (.betaPi (.var 1) (.var 2) (.var 0))

theorem annotation_before_read : Reads lex (Γ := [number,predicateType]) annotationBefore annotationCode :=
  .abstraction NativeGuardedRealizability.Controls.semanticTypeExpansion.rightRead
    (Reads.var (lex := lex) (.vz : HOL.Var [number,number,predicateType] number))
theorem annotation_after_read : Reads lex (Γ := [number,predicateType]) annotationAfter annotationCode :=
  .abstraction NativeGuardedRealizability.Controls.variableValue.typeRead
    (Reads.var (lex := lex) (.vz : HOL.Var [number,number,predicateType] number))

theorem annotation_before_source_typed : CTyped (Programs.Annotated.church profile)
    NativeGuardedRealizability.Controls.valueContext.source annotationBefore
    (.pi NativeGuardedRealizability.Controls.expandedType
      (NativeGuardedRealizability.Controls.expandedType.rename wk)) := by
  have formed := (CTypeEq.isType levels NativeGuardedRealizability.Controls.source_type_expansion
    NativeGuardedRealizability.Controls.valueContext.formed).2
  exact CTyped.abstractTerm levels formed
    (formed.rename (CCtxRen.wk _ _)) (.var 0)
theorem annotation_after_source_typed : CTyped (Programs.Annotated.church profile)
    NativeGuardedRealizability.Controls.valueContext.source annotationAfter (.pi (.var 1) (.var 2)) :=
  CTyped.abstractTerm levels NativeGuardedRealizability.Controls.family_formed
    (NativeGuardedRealizability.Controls.family_formed.rename (CCtxRen.wk _ _)) (.var 0)

theorem annotation_endpoints_differ : annotationBefore ≠ annotationAfter := by decide +kernel

theorem no_annotation_target_step : ¬ Nonempty (HOL.ContextualTrinity.BetaStep annotationCode annotationCode) := by
  rintro ⟨step⟩
  cases step with
  | lam inside => cases inside

theorem annotation_strict_step_refused (root : CRootComputation Tower.Head) (headEq : Tower.Head → Tower.Head → Prop) :
    CStepCore root headEq annotationBefore annotationAfter ∧
    Reads lex (Γ := [number,predicateType]) annotationBefore annotationCode ∧
    Reads lex (Γ := [number,predicateType]) annotationAfter annotationCode ∧
    ¬ Nonempty (HOL.ContextualTrinity.BetaStep annotationCode annotationCode) :=
  ⟨annotation_source_step root headEq,annotation_before_read,annotation_after_read,no_annotation_target_step⟩

noncomputable def model := NativeGuardedRealizability.Controls.model
noncomputable def familyValues (chosen : Nat) : model.Valuation [familyCarrier,predicateType] :=
  model.extend (σ := familyCarrier) (NativeGuardedRealizability.Controls.predicateValues chosen)
    (fun index value => ULift.up (value.down = index.down))
noncomputable def argumentValues (chosen : Nat) : model.Valuation [number,familyCarrier,predicateType] :=
  model.extend (σ := number) (familyValues chosen) (ULift.up chosen)
noncomputable def values (chosen : Nat) : model.Valuation [number ⇒ number,number,familyCarrier,predicateType] :=
  model.extend (σ := number ⇒ number) (argumentValues chosen) (fun point => point)

theorem base_guards_hold (chosen : Nat) : baseContext.telescope.Satisfies model
    (NativeGuardedRealizability.Controls.predicateValues chosen) := by
  change (HOL.PredicateContexts.Telescope.snoc .nil (HOL.PredicateProducts.full predicateType)).Satisfies model
    (model.extend (σ := predicateType) NativeGuardedRealizability.Controls.emptyValues
      (fun value => ULift.up (value.down = chosen)))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  exact ⟨(fun _ absent => nomatch absent),True.intro⟩

theorem family_guards_hold (chosen : Nat) : familyContext.telescope.Satisfies model (familyValues chosen) := by
  change (HOL.PredicateContexts.Telescope.snoc baseContext.telescope familyPredicate).Satisfies model
    (model.extend (σ := familyCarrier) (NativeGuardedRealizability.Controls.predicateValues chosen)
      (fun index value => ULift.up (value.down = index.down)))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  refine ⟨base_guards_hold chosen,?_⟩
  intro point _ _
  trivial

theorem argument_guards_hold (chosen : Nat) : argumentContext.telescope.Satisfies model (argumentValues chosen) := by
  change (HOL.PredicateContexts.Telescope.snoc familyContext.telescope familyDomainPredicate).Satisfies model
    (model.extend (σ := number) (familyValues chosen) (ULift.up chosen))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  exact ⟨family_guards_hold chosen,rfl⟩

theorem guards_hold (chosen : Nat) : functionContext.telescope.Satisfies model (values chosen) := by
  change (HOL.PredicateContexts.Telescope.snoc argumentContext.telescope functionPredicate).Satisfies model
    (model.extend (σ := number ⇒ number) (argumentValues chosen) (fun point => point))
  rw [HOL.PredicateContexts.Telescope.satisfies_snoc]
  refine ⟨argument_guards_hold chosen,?_⟩
  intro point _ _
  rfl

theorem background_holds (chosen : Nat) : HOL.Soundness.SatisfiesHyps model (values chosen) (functionContext.hypotheses roots) := by
  intro formula present
  change formula ∈ assumptions roots [number ⇒ number,number,familyCarrier,predicateType] ++ functionContext.telescope.hypotheses at present
  rcases List.mem_append.mp present with root | guard
  · change formula ∈ roots.map (HOL.weakenCtx [number ⇒ number,number,familyCarrier,predicateType]) at root
    obtain ⟨closed,inside,rfl⟩ := List.mem_map.mp root
    change (model.denote (HOL.weakenCtx _ closed) (values chosen)).down
    rw [model.denote_weakenCtx]
    exact NativeNaturalVectorProfile.Controls.root_background_realizable closed inside
  · exact guards_hold chosen formula guard

theorem redex_member_valid (chosen : Nat) :
    (model.denote (.app redex.predicate redex.term) (values chosen)).down :=
  redex.satisfies model (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values chosen) (fun _ => trivial) (background_holds chosen)
theorem reduct_member_valid (chosen : Nat) :
    (model.denote (.app reduct.predicate reduct.term) (values chosen)).down :=
  reduct.satisfies model (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values chosen) (fun _ => trivial) (background_holds chosen)

theorem redex_denotes (chosen : Nat) : model.denote redex.term (values chosen) = ULift.up chosen := rfl
theorem reduct_denotes (chosen : Nat) : model.denote reduct.term (values chosen) = ULift.up chosen := rfl
theorem result_guard_denotes (chosen point : Nat) :
    (model.denote resultPredicate (values chosen) (ULift.up point)).down ↔ point = chosen := Iff.rfl
theorem result_guard_at_two_refuses_three :
    ¬ (model.denote reduct.predicate (values 2) (ULift.up 3)).down := by
  rw [reduct_guard]
  change ¬ (3 : Nat) = 2
  decide +kernel
theorem result_guard_at_three_accepts_three :
    (model.denote reduct.predicate (values 3) (ULift.up 3)).down := by
  rw [reduct_guard]
  rfl

#print axioms redex_source_typed
#print axioms source_beta
#print axioms redex_guard
#print axioms reduct_free
#print axioms annotation_strict_step_refused
#print axioms reduct_member_valid
#print axioms result_guard_at_two_refuses_three
#print axioms source_beta_checked
#print axioms changed_source_result_guard_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedBetaRealizability.Controls
