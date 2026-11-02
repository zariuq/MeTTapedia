import Mettapedia.Logic.HOL.ConstructorShapeDataGuard
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
import Mettapedia.Logic.HOL.VectorTreePayloadRecovery
import Mettapedia.Logic.HOL.IndexedContainerFieldReadback

/-!
# Stored-field guards for the complete parsed Vector-tree inventory

The original solved/branch order is retained. The solved field has the direct
image of its original source predicate. The branch fields are the source
arity and a separate Vector shape code; their guard keeps the numeric
predicate and requires the shape code to equal the source zero. Position
counts read the arity, rather than the shape code.

The retained application equivalence commutes with typed substitution and
preserves freedom from function extensionality. It asserts no semantic field
image completeness or complete source-context/native-consumer qualification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuards
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerPositionTerms
open CurriedPredicates FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {N A E : Ty Base}
abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry

def codes : List (Code I registry 0 []) :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.map (fun c => c.body.erase)
theorem solved_code : ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase =
    (.data .payload (.result ()) : Code I registry 0 []) := rfl
theorem branch_code : ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase =
    (.data .length (.nested "Vector" VectorControl.entry (by simp [registry,VectorControl.registry])
      .here () (.result ())) : Code I registry 0 []) := rfl

def dataType (N E : Ty Base) : I.SortCode → Ty Base
  | .length => N
  | .payload => E

def indices (Const : Ty Base → Type v) (Γ : Ctx Base) (N E : Ty Base) :
    IndexedConstructorTerms.Reading I Const where
  sort := dataType N E
  index := .prop
  parameters := Γ
  term _ := .top

def lengthVariable : {context : List I.SortCode} → VectorControl.LengthExpr context →
    Var (context.map (dataType N E) ++ Γ) N
  | _,.here => .vz
  | _,.there expression => .vs (lengthVariable expression)

theorem registered_entry {name : String} {entry : Entry I}
    (found : registry.lookup name = some entry) : entry = VectorControl.entry := by
  by_cases same : name = "Vector"
  · simpa [registry,VectorControl.registry,same] using found.symm
  · simp [registry,VectorControl.registry,same] at found

def reading (one : ClosedTerm Const N) : Reading I registry Const where
  indices := indices Const Γ N E
  number := N
  one := one
  shapeType _ _ _ := N
  count := by
    intro context name entry found output
    obtain rfl := registered_entry found
    exact .lam (weaken (.var (lengthVariable output)))

def shapePredicate (zero : ClosedTerm Const N) (Θ : Ctx Base) : Term Const Θ (N ⇒ .prop) :=
  .lam (.eq (.var .vz) (weakenCtx (N :: Θ) zero))

theorem shapePredicate_subst (zero : ClosedTerm Const N) {Θ Ω : Ctx Base} (rho : Subst Const Θ Ω) :
    HOL.subst rho (shapePredicate zero Θ) = shapePredicate zero Ω := by
  simp only [shapePredicate,HOL.subst,subst_weakenCtx,Subst.lift]

def guards (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) : FieldGuards (reading (Γ := Γ) (E := E) one) where
  value
    | .length => numbers
    | .payload => given.predicate source
  shape := fun {context} _ _ _ _ => shapePredicate zero (context.map (dataType N E) ++ Γ)

def branch (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N) :
    Term Const Γ (handlerType [N,N]) :=
  .lam (.lam (.and (.app (weaken (weaken numbers)) (.var (.vs .vz)))
    (.and (.eq (.var .vz) (weakenCtx (N :: N :: Γ) zero)) .top)))

def conditions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N) :=
  VectorTreePayloadMaps.conditions given source (branch numbers zero)

theorem fields_source (one : ClosedTerm Const N) : codes.map (reading (Γ := Γ) (E := E) one).fields =
    VectorTreeFieldEmbedding.storedSignature N E := rfl

def compiledConditions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop)) (zero one : ClosedTerm Const N) :
    ConstructorDataPredicates.Conditions Const Γ (VectorTreeFieldEmbedding.storedSignature N E)
  | ⟨0,_⟩ => (guards given source numbers zero one).compile
      ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase Subst.id
  | ⟨1,_⟩ => (guards given source numbers zero one).compile
      ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase Subst.id


variable {Δ : List (Formula Const Γ)}

def shape_beta (zero : ClosedTerm Const N) {Θ : Ctx Base} (rho : Subst Const Θ Γ) (q : Term Const Γ N) :
    ProofSyntax Const Δ (.eq (.app (HOL.subst rho (shapePredicate zero Θ)) q) (.eq q (weakenCtx Γ zero))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta (Δ := Δ) q (.eq (.var .vz) (weakenCtx (N :: Γ) zero)))
  rw [shapePredicate_subst]
  simp only [shapePredicate,instantiate,HOL.subst,Subst.single,subst_weakenCtx]

theorem shape_beta_free (zero : ClosedTerm Const N) {Θ : Ctx Base} (rho : Subst Const Θ Γ) (q : Term Const Γ N) :
    (shape_beta (Δ := Δ) zero rho q).FunctionExtensionalityFree := by
  unfold shape_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def branch_beta (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N)
    (n q : Term Const Γ N) :
    ProofSyntax Const Δ (.eq (applyArguments [N,N] (branch numbers zero) (n,q,PUnit.unit))
      (.and (.app numbers n) (.and (.eq q (weakenCtx Γ zero)) .top))) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
    (.and (.app (weaken (weaken numbers)) (.var (.vs .vz)))
      (.and (.eq (.var .vz) (weakenCtx (N :: N :: Γ) zero)) .top)) n q)
  simp only [branch,applyArguments,instantiate,HOL.subst,subst_weaken,Subst.single,Subst.lift,
    subst_weakenCtx]
  rw [← weaken]
  simp only [PredicateFixedPoint.subst_single_weaken]

theorem branch_beta_free (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N) (n q : Term Const Γ N) :
    (branch_beta (Δ := Δ) numbers zero n q).FunctionExtensionalityFree := by
  unfold branch_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _


theorem parameter_id (one : ClosedTerm Const N) {type : Ty Base} (index : Var Γ type) :
    (reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id index = Term.var index := rfl

theorem subst_parameter_id (one : ClosedTerm Const N) {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) term = term :=
  ProofSyntax.term_subst_of_identity (fun index => parameter_id one index) term

def solvedRead (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (e : Term Const Γ E)
    (present : ProofSyntax Const Δ (applyArguments [E]
      (compiledConditions given source numbers zero one ⟨0,by change 0 < 2; decide⟩) (e,PUnit.unit))) :
    ProofSyntax Const Δ (.app (given.predicate source) e) := by
  have extracted := ((guards given source numbers zero one).readEvidence
    ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase Subst.id
    (e,PUnit.unit) present).1
  change ProofSyntax Const Δ (.app (HOL.subst ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) (given.predicate source)) e) at extracted
  apply ProofSyntax.castIndices rfl ?_ extracted
  exact congrArg (fun predicate => Term.app predicate e) (subst_parameter_id one (given.predicate source))

def solvedIntroduce (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (e : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (given.predicate source) e)) :
    ProofSyntax Const Δ (applyArguments [E]
      (compiledConditions given source numbers zero one ⟨0,by change 0 < 2; decide⟩) (e,PUnit.unit)) := by
  apply (guards given source numbers zero one).introduce
    ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase Subst.id (e,PUnit.unit)
  refine ⟨?_,PUnit.unit⟩
  change ProofSyntax Const Δ (.app (HOL.subst ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) (given.predicate source)) e)
  apply ProofSyntax.castIndices rfl ?_ member
  exact (congrArg (fun predicate => Term.app predicate e) (subst_parameter_id one (given.predicate source))).symm

def branchRead (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (n q : Term Const Γ N)
    (present : ProofSyntax Const Δ (applyArguments [N,N]
      (compiledConditions given source numbers zero one ⟨1,by change 1 < 2; decide⟩) (n,q,PUnit.unit))) :
    ProofSyntax Const Δ (.and (.app numbers n) (.and (.eq q (weakenCtx Γ zero)) .top)) := by
  have extracted := (guards given source numbers zero one).readEvidence
    ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase Subst.id
    (n,q,PUnit.unit) present
  have numeric : ProofSyntax Const Δ (.app numbers n) := by
    have first := extracted.1
    change ProofSyntax Const Δ (.app (HOL.subst ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) numbers) n) at first
    apply ProofSyntax.castIndices rfl ?_ first
    exact congrArg (fun predicate => Term.app predicate n) (subst_parameter_id one numbers)
  have shape : ProofSyntax Const Δ (.app (HOL.subst (Subst.cons n Subst.id)
      (shapePredicate zero (N :: Γ))) q) := extracted.2.1
  exact .andI numeric (.andI (.impE (.eqPropEL (shape_beta zero (Subst.cons n Subst.id) q)) shape) .topI)

def branchIntroduce (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (n q : Term Const Γ N)
    (member : ProofSyntax Const Δ (.and (.app numbers n) (.and (.eq q (weakenCtx Γ zero)) .top))) :
    ProofSyntax Const Δ (applyArguments [N,N]
      (compiledConditions given source numbers zero one ⟨1,by change 1 < 2; decide⟩) (n,q,PUnit.unit)) := by
  apply (guards given source numbers zero one).introduce
    ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase Subst.id (n,q,PUnit.unit)
  refine ⟨?_,?_,PUnit.unit⟩
  · change ProofSyntax Const Δ (.app (HOL.subst ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) numbers) n)
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.andEL member)
    exact (congrArg (fun predicate => Term.app predicate n) (subst_parameter_id one numbers)).symm
  · exact .impE (.eqPropER (shape_beta zero (Subst.cons n Subst.id) q)) (.andEL (.andER member))


def toConditions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N)
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const Δ (applyArguments _ (compiledConditions given source numbers zero one i) arguments)) :
    ProofSyntax Const Δ (applyArguments _ (conditions given source numbers zero i) arguments) := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 =>
    rcases arguments with ⟨e,terminal⟩
    cases terminal
    exact solvedRead given source numbers zero one e present
  | 1 =>
    rcases arguments with ⟨n,q,terminal⟩
    cases terminal
    exact .impE (.eqPropER (branch_beta numbers zero n q)) (branchRead given source numbers zero one n q present)

def fromConditions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N)
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (member : ProofSyntax Const Δ (applyArguments _ (conditions given source numbers zero i) arguments)) :
    ProofSyntax Const Δ (applyArguments _ (compiledConditions given source numbers zero one i) arguments) := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 =>
    rcases arguments with ⟨e,terminal⟩
    cases terminal
    exact solvedIntroduce given source numbers zero one e member
  | 1 =>
    rcases arguments with ⟨n,q,terminal⟩
    cases terminal
    exact branchIntroduce given source numbers zero one n q (.impE (.eqPropEL (branch_beta numbers zero n q)) member)

def application_eq (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N)
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i)) :
    ProofSyntax Const Δ (.eq (applyArguments _ (compiledConditions given source numbers zero one i) arguments)
      (applyArguments _ (conditions given source numbers zero i) arguments)) :=
  .eqPropI (.impI (toConditions given source numbers zero one i arguments (.hyp 0)))
    (.impI (fromConditions given source numbers zero one i arguments (.hyp 0)))


theorem solvedRead_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (e : Term Const Γ E)
    (present : ProofSyntax Const Δ (applyArguments [E]
      (compiledConditions given source numbers zero one ⟨0,by change 0 < 2; decide⟩) (e,PUnit.unit)))
    (free : present.FunctionExtensionalityFree) :
    (solvedRead given source numbers zero one e present).FunctionExtensionalityFree := by
  unfold solvedRead
  dsimp only [id]
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ((guards given source numbers zero one).readEvidence_free
    ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase Subst.id (e,PUnit.unit) present free).1

theorem solvedIntroduce_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (e : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (given.predicate source) e))
    (free : member.FunctionExtensionalityFree) :
    (solvedIntroduce given source numbers zero one e member).FunctionExtensionalityFree := by
  unfold solvedIntroduce
  apply (guards given source numbers zero one).introduce_free
  simpa only [solved_code,FieldGuards.EvidenceFree,id_eq,ProofSyntax.functionExtensionalityFree_castIndices] using
    And.intro free True.intro

theorem branchRead_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (n q : Term Const Γ N)
    (present : ProofSyntax Const Δ (applyArguments [N,N]
      (compiledConditions given source numbers zero one ⟨1,by change 1 < 2; decide⟩) (n,q,PUnit.unit)))
    (free : present.FunctionExtensionalityFree) :
    (branchRead given source numbers zero one n q present).FunctionExtensionalityFree := by
  have extracted := (guards given source numbers zero one).readEvidence_free
    ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase Subst.id (n,q,PUnit.unit) present free
  unfold branchRead
  dsimp only [id]
  simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨extracted.1,⟨⟨shape_beta_free _ _ _,extracted.2.1⟩,True.intro⟩⟩

theorem branchIntroduce_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (n q : Term Const Γ N)
    (member : ProofSyntax Const Δ (.and (.app numbers n) (.and (.eq q (weakenCtx Γ zero)) .top)))
    (free : member.FunctionExtensionalityFree) :
    (branchIntroduce given source numbers zero one n q member).FunctionExtensionalityFree := by
  unfold branchIntroduce
  apply (guards given source numbers zero one).introduce_free
  simp only [branch_code,FieldGuards.EvidenceFree,id_eq,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree,shape_beta_free,free,and_self]


theorem branch_subst (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N)
    (images : Subst Const Γ Ξ) :
    HOL.subst images (branch numbers zero) = branch (HOL.subst images numbers) zero := by
  simp only [branch,HOL.subst,subst_weaken,subst_weakenCtx,Subst.lift,HOL.rename,Rename.weaken]

theorem conditions_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop)) (zero : ClosedTerm Const N)
    (images : Subst Const Γ Ξ) (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    HOL.subst images (conditions given source numbers zero i) =
      conditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) zero i := by
  rw [conditions,VectorTreePayloadMaps.conditions_subst,branch_subst]
  rfl

theorem substitute_parameter_id (one : ClosedTerm Const N)
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :
    given.substitute ((reading (Γ := Γ) (E := E) one).parameterSubst (context := []) Subst.id) = given := by
  cases given
  simp only [VectorTreeFieldEmbedding.Inputs.substitute,subst_parameter_id]

theorem compiledConditions_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (images : Subst Const Γ Ξ)
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    HOL.subst images (compiledConditions given source numbers zero one i) =
      compiledConditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) zero one i := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 =>
    simp only [compiledConditions,solved_code,guards,FieldGuards.compile,subst_parameter_id,HOL.subst,
      conjoin_subst,constant_subst,subst_weaken,Subst.lift,given.predicate_subst,substitute_parameter_id]
    rfl
  | 1 =>
    simp only [compiledConditions,branch_code,guards,FieldGuards.compile,subst_parameter_id,HOL.subst,
      conjoin_subst,constant_subst,subst_weaken,Subst.lift,shapePredicate]
    dsimp only [reading,indices,Reading.fields,dataType,List.map,List.append]
    simp only [subst_weakenCtx]


theorem toConditions_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const Δ (applyArguments _ (compiledConditions given source numbers zero one i) arguments))
    (free : present.FunctionExtensionalityFree) :
    (toConditions given source numbers zero one i arguments present).FunctionExtensionalityFree := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 =>
    rcases arguments with ⟨e,terminal⟩
    cases terminal
    exact solvedRead_free _ _ _ _ _ _ _ free
  | 1 =>
    rcases arguments with ⟨n,q,terminal⟩
    cases terminal
    exact ⟨branch_beta_free _ _ _ _,branchRead_free _ _ _ _ _ _ _ _ free⟩

theorem fromConditions_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (member : ProofSyntax Const Δ (applyArguments _ (conditions given source numbers zero i) arguments))
    (free : member.FunctionExtensionalityFree) :
    (fromConditions given source numbers zero one i arguments member).FunctionExtensionalityFree := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 =>
    rcases arguments with ⟨e,terminal⟩
    cases terminal
    exact solvedIntroduce_free _ _ _ _ _ _ _ free
  | 1 =>
    rcases arguments with ⟨n,q,terminal⟩
    cases terminal
    exact branchIntroduce_free _ _ _ _ _ _ _ _ ⟨branch_beta_free _ _ _ _,free⟩

theorem application_eq_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get i)) :
    (application_eq (Δ := Δ) given source numbers zero one i arguments).FunctionExtensionalityFree := by
  exact ⟨toConditions_free _ _ _ _ _ _ _ _ True.intro,fromConditions_free _ _ _ _ _ _ _ _ True.intro⟩

def toConditionsAt (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Ξ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const assumptions (applyArguments _ (HOL.subst images
      (compiledConditions given source numbers zero one i)) arguments)) :
    ProofSyntax Const assumptions (applyArguments _ (HOL.subst images (conditions given source numbers zero i)) arguments) := by
  have current : ProofSyntax Const assumptions (applyArguments _
      (compiledConditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) zero one i) arguments) :=
    .castIndices rfl (congrArg (fun condition => applyArguments _ condition arguments)
      (compiledConditions_subst given source numbers zero one images i)) present
  have converted := toConditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
    zero one i arguments current
  exact .castIndices rfl (congrArg (fun condition => applyArguments _ condition arguments)
    (conditions_subst given source numbers zero images i).symm) converted

theorem toConditionsAt_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Ξ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const assumptions (applyArguments _ (HOL.subst images
      (compiledConditions given source numbers zero one i)) arguments)) (free : present.FunctionExtensionalityFree) :
    (toConditionsAt given source numbers zero one images i arguments present).FunctionExtensionalityFree := by
  unfold toConditionsAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply toConditions_free
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free


def fromConditionsAt (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Ξ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const assumptions (applyArguments _ (HOL.subst images
      (conditions given source numbers zero i)) arguments)) :
    ProofSyntax Const assumptions (applyArguments _ (HOL.subst images (compiledConditions given source numbers zero one i)) arguments) := by
  have current : ProofSyntax Const assumptions (applyArguments _
      (conditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) zero i) arguments) :=
    .castIndices rfl (congrArg (fun condition => applyArguments _ condition arguments)
      (conditions_subst given source numbers zero images i)) present
  have converted := fromConditions (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
    zero one i arguments current
  exact .castIndices rfl (congrArg (fun condition => applyArguments _ condition arguments)
    (compiledConditions_subst given source numbers zero one images i).symm) converted

theorem fromConditionsAt_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Ξ ((VectorTreeFieldEmbedding.storedSignature N E).get i))
    (present : ProofSyntax Const assumptions (applyArguments _ (HOL.subst images
      (conditions given source numbers zero i)) arguments)) (free : present.FunctionExtensionalityFree) :
    (fromConditionsAt given source numbers zero one images i arguments present).FunctionExtensionalityFree := by
  unfold fromConditionsAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply fromConditions_free
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def inventory (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (tags : Nat → Term Const Γ N) :
    IndexedConstructorGuards.ConstructorPrograms Const Γ :=
  (guards given source numbers zero one).constructors codes Subst.id tags

theorem allowed_eq (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (tags : Nat → Term Const Γ N)
    (i : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    (inventory given source numbers zero one tags).allowed i = compiledConditions given source numbers zero one i := by
  rcases i with ⟨i,bound⟩
  match i with
  | 0 => rfl
  | 1 => rfl


def rowImplication (premises : List (Formula Const Γ))
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (tags : Nat → Term Const Γ N) :
    IndexedConstructorGuards.ConstructorPrograms.RowImplication premises
      (inventory given source numbers zero one tags) (conditions given source numbers zero) := by
  intro Ξ images assumptions _transport i arguments present
  apply toConditionsAt given source numbers zero one images i arguments
  exact .castIndices rfl (congrArg (fun condition => applyArguments _ (HOL.subst images condition) arguments)
    (allowed_eq given source numbers zero one tags i)) present

theorem rowImplication_free (premises : List (Formula Const Γ))
    (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (tags : Nat → Term Const Γ N) :
    IndexedConstructorGuards.ConstructorPrograms.RowImplication.Free
      (rowImplication premises given source numbers zero one tags) := by
  intro Ξ images assumptions transport i arguments present free
  unfold rowImplication
  apply toConditionsAt_free
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

#print axioms application_eq
#print axioms application_eq_free
#print axioms compiledConditions_subst
#print axioms rowImplication
#print axioms rowImplication_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuards
