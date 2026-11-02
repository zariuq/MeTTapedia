import Mettapedia.Languages.HOLLight.CachedSourceExpansion
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation

/-!
# Original Boolean definitions through checked cache expansion

The source conjunction body still contains the registered truth constant.
Its admitted defining equation and the truth defining equation supply the
actual cache premises. Expanding truth produces the independently authored
definition-erased conjunction body, preserving the conjunction identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceExpansionControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open StandardTheoryInterpretation CachedSourceExpansion ReverseTranslation GraphExpansion

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def truthEquation : Formula := .eq (.const Interpretation.Symbols.truth) HOL.HOLLightBooleanDefinitions.truth

def source : Formula := .eq (.const Interpretation.Symbols.conjunction) Raw.conjunction

def target : Formula := .eq (.const Interpretation.Symbols.conjunction) HOL.HOLLightBooleanDefinitions.conjunction

def theory : List Formula := [truthEquation]

structure Replacement {type : HOL.Ty AtomicTy} (symbol : Symbol type) where
  body : HOL.ClosedTerm Symbol type
  proof : HOL.ProofSyntax Symbol theory (.eq (.const symbol) body)
  free : proof.FunctionExtensionalityFree

def literal {type : HOL.Ty AtomicTy} (symbol : Symbol type) : Replacement symbol :=
  ⟨.const symbol, .eqRefl _, True.intro⟩

/-- This is an ordinary typed replacement table over complete declaration
identities. Free variables and every other constant retain their syntax. -/
def replacement : {type : HOL.Ty AtomicTy} → (symbol : Symbol type) → Replacement symbol
  | .prop, .constant constant annotation typed => by
      if same : Const.same constant Source.truthConstant = true then
        have identity := (Const.same_eq_true_iff _ _).mp same
        subst constant
        have annotationSame : annotation = Ty.bool :=
          Ty.toHOL_injective (typed.trans Ty.toHOL_bool.symm)
        subst annotation
        exact ⟨HOL.HOLLightBooleanDefinitions.truth, .hyp ⟨0, by decide⟩, by trivial⟩
      else exact literal (.constant constant annotation typed)
  | _, symbol => literal symbol

def replacements {type : HOL.Ty AtomicTy} (symbol : Symbol type) : Option (HOL.ClosedTerm Symbol type) :=
  some (replacement symbol).body

def equations {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (present : replacements symbol = some body) : HOL.ProofSyntax Symbol theory (.eq (.const symbol) body) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (HOL.Term.eq (.const symbol)) (Option.some.inj present))
    (replacement symbol).proof

theorem equations_free {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (present : replacements symbol = some body) : (equations symbol body present).FunctionExtensionalityFree := by
  unfold equations
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (replacement symbol).free

theorem traversal : HOL.substConst? replacements source = some target := by
  simp [source, target, Raw.conjunction, HOL.HOLLightBooleanDefinitions.conjunction,
    HOL.HOLLightBooleanDefinitions.truth, HOL.substConst?, replacements, replacement, literal,
    Interpretation.Symbols.conjunction]

def task : Task := ⟨source, target, theory, replacements, equations, equations_free, traversal⟩

def commands : List ProofExecution.Registered.Command := [
  .constant ("cached-source-truth", 0) (.global "T") Source.truthBody
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature),
  .constant ("cached-source-conjunction", 1) (.global "/\\") Source.conjunctionBody
    (ExportReplay.instanceCertificates Source.truthContext.signature)]

def received? := ProofExecution.Registered.replayFrom emptyAxiomPolicy
  (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands

theorem received_available : received?.isSome = true := by decide +kernel

def received := received?.get received_available

theorem received_replay : ProofExecution.Registered.replayFrom emptyAxiomPolicy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some received :=
  (Option.some_get received_available).symm

def before : ProofExecution.State := start received.cache.toList

theorem source_read : (read? before 1 source).isSome = true := by decide +kernel
theorem truth_read : (read? before 0 truthEquation).isSome = true := by decide +kernel

theorem all_read : (readAll? before (source :: theory) [1, 0]).isSome = true := by decide +kernel

def sources : Sources before (source :: theory) := (readAll? before (source :: theory) [1, 0]).get all_read

theorem sources_read : readAll? before (source :: theory) [1, 0] = some sources :=
  (Option.some_get all_read).symm

theorem before_checked : BuildChecked emptyAxiomPolicy received.cache.toList before :=
  start_checked _ _

theorem closed_available : ∃ after root,
    task.compileAndClose? ("cached-source-expansion", 0) before [1, 0] = some (after, root) ∧
    BuildChecked emptyAxiomPolicy received.cache.toList after := by
  obtain ⟨after, root, accepted, checked, _⟩ :=
    task.compileAndClose_checked ("cached-source-expansion", 0) [1, 0] sources sources_read before_checked
  exact ⟨after, root, accepted, checked⟩

theorem source_dependencies_empty :
    CachedHypothesisList.dependencies (sources.entries.map Prod.snd) = ∅ := by decide +kernel

theorem closed_result : ∃ (after : ProofExecution.State) (root : Nat) (fact : Theorem),
    task.compileAndClose? ("cached-source-expansion", 0) before [1, 0] = some (after, root) ∧
    after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
    fact.sequent.concl = encode target ∧ fact.axioms = ∅ := by
  obtain ⟨after, root, accepted, _, found, noHypotheses, conclusion, dependencies, _⟩ :=
    task.compileAndClose_checked ("cached-source-expansion", 0) [1, 0] sources sources_read before_checked
  exact ⟨after, root, _, accepted, found, noHypotheses, conclusion,
    dependencies.trans source_dependencies_empty⟩

/-- The already-inlined equation is not the original source cache entry. -/
theorem premature_inlining_refused : (read? before 1 target).isNone = true := by decide +kernel

theorem wrong_root_refused : (read? before 0 source).isNone = true := by decide +kernel

theorem missing_definition_refused : (readAll? before (source :: theory) [1, 2]).isNone = true := by decide +kernel

theorem missing_address_refused : (readAll? before (source :: theory) [1]).isNone = true := by decide +kernel

theorem duplicate_roots_preserved :
    (readAll? before [truthEquation, truthEquation] [0, 0]).map
      (fun inputs => inputs.entries.map Prod.fst) = some [0, 0] := by decide +kernel

#print axioms traversal
#print axioms received_replay
#print axioms source_read
#print axioms truth_read
#print axioms closed_available
#print axioms closed_result
#print axioms premature_inlining_refused
#print axioms wrong_root_refused
#print axioms missing_definition_refused
#print axioms duplicate_roots_preserved

end Mettapedia.Languages.HOLLight.CachedSourceExpansionControls
