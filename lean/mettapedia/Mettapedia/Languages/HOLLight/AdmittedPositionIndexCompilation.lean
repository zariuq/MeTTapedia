import Mettapedia.Languages.HOLLight.AdmittedNonbottomCompilation
import Mettapedia.Logic.HOL.OrderedPositionIndexComparisons

/-!
# Original admitted Vector child-index comparison

The selected cons plan is extracted from the original admitted declaration.
Its graph is compared with the retained source table. Explicit field beta
proofs identify the child index with the original open length variable;
the ordered-query compiler produces the guarded universal comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedPositionIndexCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.TypeTheory
open HOL FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms
open Mettapedia.GSLT.LanguageDef

abbrev Base := AdmittedContainerGeneratedControls.BaseCode
abbrev Const := AdmittedContainerGeneratedControls.Symbol
abbrev context := AdmittedNonbottomCompilation.inputContext
abbrev number := AdmittedContainerGeneratedControls.number
abbrev element := AdmittedContainerGeneratedControls.element

namespace Source

noncomputable def plan :=
  IndexedContainerPositionTerms.FieldGuards.plans (reading := AdmittedContainerGeneratedControls.reading)
    (AdmittedContainerHOL.codes AdmittedContainerGeneratedControls.block AdmittedContainerGeneratedControls.registered)
    (AdmittedContainerInductionControls.initial (Γ := context)) AdmittedContainerGeneratedControls.consOccurrence

end Source

local macro "stagePosition% " value:term : term =>
  `(stageValue% [Mettapedia.Languages.HOLLight.AdmittedPositionIndexCompilation.Source,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec,
    Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge,
    Mettapedia.Logic.HOL.IndexedContainerPositionTerms,
    Mettapedia.Logic.HOL.IndexedContainerFieldGuards,
    Mettapedia.Logic.HOL.IndexedConstructorTerms,
    Mettapedia.Logic.HOL.CurriedPredicates,
    Mettapedia.TypeTheory, List, Fin] $value)

def plan : FieldPlan Const context [number, element] number number :=
  stagedData% (stagePosition% Source.plan)

theorem plan_source : HEq plan Source.plan := stagedHEq% plan, Source.plan

def constructors := AdmittedNonbottomCompilation.constructors
def positions := AdmittedNonbottomCompilation.positions
def cons : Fin constructors.fields.length := ⟨1, by decide⟩
def nilRow : Fin constructors.fields.length := ⟨0, by decide⟩
def zero : ClosedTerm Const number := .const .zero
def successor : ClosedTerm Const (number ⇒ number) := .const .successor

def plans : (occurrence : Fin constructors.fields.length) →
    FieldPlan Const context (constructors.fields.get occurrence) number number :=
  Fin.cases [] (Fin.cases plan (fun impossible => Fin.elim0 impossible))

theorem positions_source : positions =
    IndexedConstructorGuards.PositionPrograms.ofSegments constructors zero successor plans := by
  apply congrArg IndexedConstructorGuards.PositionPrograms.mk
  funext occurrence
  refine Fin.cases ?_ (fun remaining => ?_) occurrence
  · rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
    exact eq_of_heq (stagedHEq% positions.graph cons,
      fieldGraph zero successor [number, element] plan)

def length : Term Const context number := .var .vz
def head : Term Const context element := .const .flagTrue
def arguments : Arguments Const context (constructors.fields.get cons) := (length, head, PUnit.unit)
def slot : Term Const context number := .const .zero

def indexBeta {assumptions : List (Formula Const context)} (position : Fin (plans cons).length) :
    ProofSyntax Const assumptions (.eq (applyFields _ ((plans cons).get position).2 arguments) length) := by
  have same : position = ⟨0, by decide⟩ := Fin.ext (by
    change position.val = 0
    have bound : position.val < 1 := position.isLt
    omega)
  subst position
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2 (.var (.vs .vz)) length head)
  apply congrArg₂ Term.eq
  · rfl
  ·
    simp only [instantiate, HOL.subst, Subst.single, Subst.lift]
    exact PredicateFixedPoint.subst_single_weaken head length

theorem indexBeta_free {assumptions : List (Formula Const context)} (position : Fin (plans cons).length) :
    (indexBeta (assumptions := assumptions) position).FunctionExtensionalityFree := by
  have same : position = ⟨0, by decide⟩ := Fin.ext (by
    change position.val = 0
    have bound : position.val < 1 := position.isLt
    omega)
  subst position
  unfold indexBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def conclusion : Formula Const context := positions.indexComparison cons arguments slot length

def proof : ProofSyntax Const [] conclusion :=
  ProofSyntax.castIndices rfl
    (congrArg (fun positions => positions.indexComparison cons arguments slot length) positions_source).symm
    (IndexedConstructorGuards.PositionPrograms.uniformIndexComparison constructors zero successor
      plans cons arguments slot length indexBeta)

theorem proof_free : proof.FunctionExtensionalityFree := by
  unfold proof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact IndexedConstructorGuards.PositionPrograms.uniformIndexComparison_free _ _ _ _ _ _ _ _ indexBeta indexBeta_free

def emptyComparison : Formula Const context :=
  positions.indexComparison nilRow PUnit.unit slot length

def emptyProof : ProofSyntax Const [] emptyComparison :=
  ProofSyntax.castIndices rfl
    (congrArg (fun positions => positions.indexComparison nilRow PUnit.unit slot length) positions_source).symm
    (IndexedConstructorGuards.PositionPrograms.uniformIndexComparison constructors zero successor
      plans nilRow PUnit.unit slot length (fun impossible => Fin.elim0 impossible))

theorem emptyProof_free : emptyProof.FunctionExtensionalityFree := by
  unfold emptyProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply IndexedConstructorGuards.PositionPrograms.uniformIndexComparison_free
  intro impossible
  exact Fin.elim0 impossible

def nilQuery : Formula Const context := .app (.app (positions.graph nilRow) slot) length

def nilRefutation : ProofSyntax Const [] (.not nilQuery) := by
  apply ProofSyntax.notI
  exact .impE (.eqPropEL (fieldGraph_beta zero successor [] [] slot length PUnit.unit)) (.hyp 0)

theorem nilRefutation_free : nilRefutation.FunctionExtensionalityFree := by
  unfold nilRefutation
  exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, trivial⟩

def compile (operations : AdmittedMembershipCompilation.Operations)
    (names : ReverseTranslation.Naming (context.map (HOL.Ty.substitute (AdmittedMembershipCompilation.types operations)))) :=
  InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
    proof proof_free names ("admitted-vector-child-index", 0)

#print axioms plan_source
#print axioms positions_source
#print axioms proof_free
#print axioms emptyProof_free
#print axioms nilRefutation_free

end Mettapedia.Languages.HOLLight.AdmittedPositionIndexCompilation
