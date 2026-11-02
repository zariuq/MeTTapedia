import Mettapedia.GSLT.LanguageDef.AdmittedContainerProofs
import Mettapedia.Logic.HOL.IndexedConstructorInduction

/-!
# Original admitted constructor cases in retained indexed induction

Each case uses the original code's ordered fields, field guard and computed
source index. The source-occurrence correspondence is `codeAt_source`.
Compilation changes the field telescope by its existing equality and derives
the result-index equation with `Reading.resultProof`; it does not assume a
layer-closure theorem. Primitive constructor injectivity is discharged by the
selected representation profile separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ Ξ : Ctx Base}
  (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
  {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
  (guards : FieldGuards reading)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)

def sourceArguments (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (((codes block registered).map reading.fields).get occurrence)) :
    Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence)) :=
  fields_get reading (codes block registered) occurrence ▸ arguments

private theorem cast_back {first second : List (Ty Base)} (same : first = second)
    (arguments : Arguments Const Ξ first) :
    same.symm ▸ (same ▸ arguments) = arguments := by
  cases same
  rfl

theorem inventoryArguments_sourceArguments
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (((codes block registered).map reading.fields).get occurrence)) :
    inventoryArguments reading (codes block registered) occurrence
      (sourceArguments block registered occurrence arguments) = arguments :=
  cast_back (fields_get reading (codes block registered) occurrence) arguments

private theorem subst_field_transport (family : List (Ty Base) → Ty Base)
    {first second : List (Ty Base)} (same : first = second) (images : Subst Const Γ Ξ)
    (term : Term Const Γ (family second)) :
    HOL.subst images (same.symm ▸ term) = same.symm ▸ HOL.subst images term := by
  cases same
  rfl

private theorem applyArguments_transport {first second : List (Ty Base)} (same : first = second)
    (condition : Term Const Ξ (handlerType second)) (arguments : Arguments Const Ξ first) :
    applyArguments first (same.symm ▸ condition) arguments =
      applyArguments second condition (same ▸ arguments) := by
  cases same
  rfl

private theorem applyFields_transport {first second : List (Ty Base)} (same : first = second)
    {result : Ty Base} (function : Term Const Ξ (FunctionType second result))
    (arguments : Arguments Const Ξ first) :
    applyFields first (same.symm ▸ function) arguments =
      applyFields second function (same ▸ arguments) := by
  cases same
  rfl

variable {space : Ty Base}
  (constructorCode : Term Const Γ (reading.number ⇒
    payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  (children : Term Const Γ (reading.number ⇒ space))
  (childCondition : Term Const Γ (payloadType ((codes block registered).map reading.fields) ⇒ .prop))
  (property : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
  {assumptions : List (Formula Const Γ)}

def SourceIndexedCases (assumptions : List (Formula Const Γ)) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))),
    ProofSyntax Const
      (applyArguments _ (guards.compile (codeAt reading (codes block registered) occurrence)
          (Subst.comp images rho)) arguments ::
        .app (HOL.subst images childCondition) (payloadTerm reading (codes block registered) occurrence arguments) ::
        assumptions.map (HOL.subst images))
      (.app (.app (HOL.subst images property)
        (((inventory block registered guards rho numeral).subst images).constructorValue
          (HOL.subst images constructorCode) occurrence
          (inventoryArguments reading (codes block registered) occurrence arguments)
          (HOL.subst images children)))
        (reading.indexTerm (codeAt reading (codes block registered) occurrence) (Subst.comp images rho) arguments))

def compileSourceCases
    (cases : SourceIndexedCases block registered guards rho numeral constructorCode children childCondition property assumptions) :
    (inventory block registered guards rho numeral).IndexedCases
      constructorCode children childCondition property assumptions := by
  intro Ξ images occurrence arguments
  let sourceArgs := sourceArguments block registered occurrence arguments
  let shifted := (inventory block registered guards rho numeral).subst images
  let value := shifted.constructorValue (HOL.subst images constructorCode) occurrence arguments (HOL.subst images children)
  let hypotheses := applyArguments _ (shifted.allowed occurrence) arguments ::
    .app (HOL.subst images childCondition)
      (encode ((codes block registered).map reading.fields) occurrence arguments) ::
      assumptions.map (HOL.subst images)
  have argsBack := inventoryArguments_sourceArguments block registered occurrence arguments
  have allowed : applyArguments _ (guards.compile (codeAt reading (codes block registered) occurrence)
      (Subst.comp images rho)) sourceArgs = applyArguments _ (shifted.allowed occurrence) arguments := by
    symm
    dsimp only [shifted, inventory, FieldGuards.constructors, IndexedConstructorGuards.ConstructorPrograms.subst]
    rw [subst_field_transport handlerType (fields_get reading (codes block registered) occurrence) images,
      guards.compile_subst]
    exact applyArguments_transport (fields_get reading (codes block registered) occurrence) _ arguments
  have payload : payloadTerm reading (codes block registered) occurrence sourceArgs =
      encode ((codes block registered).map reading.fields) occurrence arguments := by
    unfold payloadTerm
    rw [argsBack]
  have sourceProof : ProofSyntax Const hypotheses (.app (.app (HOL.subst images property) value)
      (reading.indexTerm (codeAt reading (codes block registered) occurrence) (Subst.comp images rho) sourceArgs)) := by
    apply ProofSyntax.castIndices ?_ ?_ (cases images occurrence sourceArgs)
    · simp only [hypotheses, allowed, payload]
    · simp only [value, argsBack, sourceArgs, shifted]
  have result : applyFields _ (shifted.result occurrence) arguments =
      applyFields _ (reading.resultProgram (codeAt reading (codes block registered) occurrence)
        (Subst.comp images rho)) sourceArgs := by
    dsimp only [shifted, inventory, FieldGuards.constructors, IndexedConstructorGuards.ConstructorPrograms.subst]
    rw [subst_field_transport (fun fields => FunctionType fields reading.indices.index)
      (fields_get reading (codes block registered) occurrence) images, reading.resultProgram_subst]
    exact applyFields_transport (fields_get reading (codes block registered) occurrence) _ arguments
  have resultProof : ProofSyntax Const hypotheses (.eq (applyFields _ (shifted.result occurrence) arguments)
      (reading.indexTerm (codeAt reading (codes block registered) occurrence) (Subst.comp images rho) sourceArgs)) :=
    ProofSyntax.castIndices rfl
      (congrArg (fun term => Term.eq term
        (reading.indexTerm (codeAt reading (codes block registered) occurrence) (Subst.comp images rho) sourceArgs)) result.symm)
      (reading.resultProof (codeAt reading (codes block registered) occurrence) (Subst.comp images rho) sourceArgs)
  exact .impE (.eqPropER (.eqAppArg (.app (HOL.subst images property) value) resultProof)) sourceProof

theorem compileSourceCases_free
    (cases : SourceIndexedCases block registered guards rho numeral constructorCode children childCondition property assumptions)
    (casesFree : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) occurrence arguments,
      (cases images occurrence arguments).FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
      (occurrence : Fin ((codes block registered).map reading.fields).length)
      (arguments : Arguments Const Ξ (((codes block registered).map reading.fields).get occurrence)),
      (compileSourceCases block registered guards rho numeral constructorCode children childCondition property cases
        images occurrence arguments).FunctionExtensionalityFree := by
  intro Ξ images occurrence arguments
  unfold compileSourceCases
  refine ⟨?_, ?_⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact reading.resultProof_free _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact casesFree images occurrence _

private theorem comp_assoc {Φ Ψ Θ Ω : Ctx Base}
    (third : Subst Const Θ Ω) (second : Subst Const Ψ Θ) (first : Subst Const Φ Ψ) :
    @Subst.comp Base Const Θ Ω Φ third (Subst.comp second first) =
      @Subst.comp Base Const Ψ Ω Φ (Subst.comp third second) first := by
  funext type entry
  exact HOL.subst_comp third second (first entry)

private theorem allowed_after_recompile {Ω : Ctx Base}
    (images0 : Subst Const Γ Ξ) (images : Subst Const Ξ Ω)
    (occurrence : Fin ((codes block registered).map reading.fields).length) :
    (((inventory block registered guards rho numeral).subst images0).subst images).allowed occurrence =
      ((inventory block registered guards (Subst.comp images0 rho)
        (fun n => HOL.subst images0 (numeral n))).subst images).allowed occurrence := by
  dsimp only [inventory, FieldGuards.constructors, IndexedConstructorGuards.ConstructorPrograms.subst]
  rw [HOL.subst_comp,
    subst_field_transport handlerType (fields_get reading (codes block registered) occurrence) (Subst.comp images images0),
    subst_field_transport handlerType (fields_get reading (codes block registered) occurrence) images,
    guards.compile_subst, guards.compile_subst, comp_assoc]

private theorem result_after_recompile {Ω : Ctx Base}
    (images0 : Subst Const Γ Ξ) (images : Subst Const Ξ Ω)
    (occurrence : Fin ((codes block registered).map reading.fields).length) :
    (((inventory block registered guards rho numeral).subst images0).subst images).result occurrence =
      ((inventory block registered guards (Subst.comp images0 rho)
        (fun n => HOL.subst images0 (numeral n))).subst images).result occurrence := by
  dsimp only [inventory, FieldGuards.constructors, IndexedConstructorGuards.ConstructorPrograms.subst]
  rw [HOL.subst_comp,
    subst_field_transport (fun fields => FunctionType fields reading.indices.index)
      (fields_get reading (codes block registered) occurrence) (Subst.comp images images0),
    subst_field_transport (fun fields => FunctionType fields reading.indices.index)
      (fields_get reading (codes block registered) occurrence) images,
    reading.resultProgram_subst, reading.resultProgram_subst, comp_assoc]

def retainParameterCases (images0 : Subst Const Γ Ξ)
    (constructor : Term Const Ξ (reading.number ⇒
      payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (descendants : Term Const Ξ (reading.number ⇒ space))
    (condition : Term Const Ξ (payloadType ((codes block registered).map reading.fields) ⇒ .prop))
    (motive : Term Const Ξ (space ⇒ reading.indices.index ⇒ .prop))
    {hypotheses : List (Formula Const Ξ)}
    (cases : (inventory block registered guards (Subst.comp images0 rho)
      (fun n => HOL.subst images0 (numeral n))).IndexedCases constructor descendants condition motive hypotheses) :
    ((inventory block registered guards rho numeral).subst images0).IndexedCases
      constructor descendants condition motive hypotheses := by
  intro Ω images occurrence arguments
  apply ProofSyntax.castIndices ?_ ?_ (cases images occurrence arguments)
  · rw [allowed_after_recompile block registered guards rho numeral images0 images occurrence]
    rfl
  · rw [result_after_recompile block registered guards rho numeral images0 images occurrence]
    rfl

theorem retainParameterCases_free (images0 : Subst Const Γ Ξ)
    (constructor : Term Const Ξ (reading.number ⇒
      payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (descendants : Term Const Ξ (reading.number ⇒ space))
    (condition : Term Const Ξ (payloadType ((codes block registered).map reading.fields) ⇒ .prop))
    (motive : Term Const Ξ (space ⇒ reading.indices.index ⇒ .prop))
    {hypotheses : List (Formula Const Ξ)}
    (cases : (inventory block registered guards (Subst.comp images0 rho)
      (fun n => HOL.subst images0 (numeral n))).IndexedCases constructor descendants condition motive hypotheses)
    (casesFree : ∀ {Ω : Ctx Base} (images : Subst Const Ξ Ω) occurrence arguments,
      (cases images occurrence arguments).FunctionExtensionalityFree) :
    ∀ {Ω : Ctx Base} (images : Subst Const Ξ Ω) occurrence arguments,
      (retainParameterCases block registered guards rho numeral images0 constructor descendants condition motive cases
        images occurrence arguments).FunctionExtensionalityFree := by
  intro Ω images occurrence arguments
  unfold retainParameterCases
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact casesFree images occurrence arguments

def ScopedSourceIndexedCases (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) (bottomCode : Term Const Γ space)
    (predicate : Term Const Γ (space ⇒ .prop))
    (motive : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (assumptions : List (Formula Const Γ)) :=
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let images0 : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  SourceIndexedCases block registered guards (Subst.comp images0 rho) (fun n => HOL.subst images0 (numeral n))
    (HOL.subst images0 constructorCode) signature.constructorChildren
    (signature.constructorScope.childPredicate (weaken (weaken (weaken predicate))) signature.constructorChildren)
    (weaken (weaken (weaken motive))) (signature.methodAssumptions (assumptions := assumptions) predicate)

def compileScopedSourceCases (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) (bottomCode : Term Const Γ space)
    (predicate : Term Const Γ (space ⇒ .prop))
    (motive : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (cases : ScopedSourceIndexedCases block registered guards rho numeral constructorCode
      zero successor bottomCode predicate motive assumptions) :
    (guards.positions (codes block registered) rho numeral zero successor).ScopedIndexedCases
      bottomCode constructorCode predicate motive assumptions := by
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let images0 : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  let predicate3 : Term Const signature.constructorContext (space ⇒ .prop) := weaken (weaken (weaken predicate))
  let motive3 : Term Const signature.constructorContext (space ⇒ reading.indices.index ⇒ .prop) :=
    weaken (weaken (weaken motive))
  let condition := signature.constructorScope.childPredicate predicate3 signature.constructorChildren
  intro Ω images occurrence arguments
  exact retainParameterCases block registered guards rho numeral images0 (HOL.subst images0 constructorCode)
    signature.constructorChildren condition motive3
    (compileSourceCases block registered guards (Subst.comp images0 rho) (fun n => HOL.subst images0 (numeral n))
      (HOL.subst images0 constructorCode) signature.constructorChildren condition motive3 cases)
    images occurrence arguments

theorem compileScopedSourceCases_free (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) (bottomCode : Term Const Γ space)
    (predicate : Term Const Γ (space ⇒ .prop))
    (motive : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (cases : ScopedSourceIndexedCases block registered guards rho numeral constructorCode
      zero successor bottomCode predicate motive assumptions)
    (casesFree :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
      ∀ {Ξ : Ctx Base} (images : Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree) :
    let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
    ∀ {Ξ : Ctx Base} (images : Subst Const signature.constructorContext Ξ) occurrence arguments,
      (compileScopedSourceCases block registered guards rho numeral constructorCode zero successor bottomCode
        predicate motive cases images occurrence arguments).FunctionExtensionalityFree := by
  intro Ξ images occurrence arguments
  unfold compileScopedSourceCases
  apply retainParameterCases_free
  exact compileSourceCases_free _ _ _ _ _ _ _ _ _ _ casesFree

def memberInductionFromSourceCases (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) (bottomCode : Term Const Γ space)
    (motive : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement constructorCode))
    (cases : ScopedSourceIndexedCases block registered guards rho numeral constructorCode zero successor bottomCode
      (PredicateFixedPoint.intersection
        (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
        (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) motive))
      motive assumptions)
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions (.app
      (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions (.app (.app motive value) target) := by
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let lifted := IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) motive
  let predicate := PredicateFixedPoint.intersection signature.least lifted
  let compiled : (guards.positions (codes block registered) rho numeral zero successor).ScopedIndexedCases
      bottomCode constructorCode predicate motive assumptions :=
    fun {Ξ} images occurrence arguments =>
      compileScopedSourceCases block registered guards rho numeral constructorCode zero successor bottomCode
        predicate motive cases images occurrence arguments
  let method := (guards.positions (codes block registered) rho numeral zero successor).constructorMethod_of_cases
    bottomCode constructorCode predicate motive injectivity compiled
  exact memberInduction block registered guards rho numeral zero successor bottomCode constructorCode motive value target
    (signature.constructor_closure predicate lifted method) member

theorem memberInductionFromSourceCases_free (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) (bottomCode : Term Const Γ space)
    (motive : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement constructorCode))
    (cases : ScopedSourceIndexedCases block registered guards rho numeral constructorCode zero successor bottomCode
      (PredicateFixedPoint.intersection
        (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
        (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) motive))
      motive assumptions)
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions (.app
      (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (casesFree :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
      ∀ {Ξ : Ctx Base} (images : Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (memberInductionFromSourceCases block registered guards rho numeral constructorCode zero successor bottomCode
      motive injectivity cases value target member).FunctionExtensionalityFree := by
  unfold memberInductionFromSourceCases
  apply memberInduction_free
  · apply RecursiveSpacePredicate.Contextual.constructor_closure_free
    apply IndexedConstructorGuards.PositionPrograms.constructorMethod_of_cases_free
    · exact injectivityFree
    · exact compileScopedSourceCases_free _ _ _ _ _ _ _ _ _ _ _ cases casesFree
  · exact memberFree

#print axioms inventoryArguments_sourceArguments
#print axioms compileSourceCases
#print axioms compileSourceCases_free
#print axioms retainParameterCases
#print axioms retainParameterCases_free
#print axioms compileScopedSourceCases
#print axioms compileScopedSourceCases_free
#print axioms memberInductionFromSourceCases
#print axioms memberInductionFromSourceCases_free
end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
