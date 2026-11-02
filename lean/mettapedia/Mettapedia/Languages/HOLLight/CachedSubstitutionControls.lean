import Mettapedia.Languages.HOLLight.CachedParameterCompilationControls

/-!
# Cache provenance and physical-reference controls

The expected theorem check includes axiom dependencies. Equal theorem values
at different roots remain different receipt dependencies. These observations
do not identify derivations or recover ordered hypothesis multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedSubstitutionControls

open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open GraphExpansion RetainedCompilation ParameterSchemaCompilationControls

theorem expanded_parents (sourceRoot base : Nat) (substitution : TypeCorrectTermSubstitution)
    (source : Theorem) (origin : ProofExecution.Origin) :
    ((expandBlock [sourceRoot] base (PrimitiveTransport.substitutionBlock substitution source origin)).1.map
      (·.parents)) = [[sourceRoot], [base]] := by
  simp [expandBlock, Node.relocate, PrimitiveTransport.substitutionBlock, address]

theorem distinct_roots_remain_distinct (first second base : Nat) (different : first ≠ second)
    (substitution : TypeCorrectTermSubstitution) (source : Theorem) (origin : ProofExecution.Origin) :
    (expandBlock [first] base (PrimitiveTransport.substitutionBlock substitution source origin)).1 ≠
      (expandBlock [second] base (PrimitiveTransport.substitutionBlock substitution source origin)).1 := by
  intro equal
  have parents := congrArg (fun nodes => nodes.map (·.parents)) equal
  rw [expanded_parents, expanded_parents] at parents
  exact different (List.singleton_inj.mp (List.cons.inj parents).1)

theorem schema_axioms_empty : schema.proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy
    (derives_shared emptyAxiomPolicy
      ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ schema.proof.accepted))

def extraAxiom : Sequent := ⟨∅, CanonicalTerm.free ⟨.global "__extra_axiom", Ty.bool⟩⟩

theorem extraAxiom_boolean : extraAxiom.IsBool := by
  refine ⟨rfl, ?_⟩
  intro hypothesis member
  exact False.elim (Finset.notMem_empty _ member)

def tainted : Theorem := {schema.proof.result with
  axioms := {extraAxiom}
  axiomsBoolean := by
    intro entry member
    have same := Finset.mem_singleton.mp member
    subst entry
    exact extraAxiom_boolean}

theorem tainted_different : tainted ≠ schema.proof.result := by
  intro equal
  have dependencies := congrArg Theorem.axioms equal
  change ({extraAxiom} : Finset Sequent) = schema.proof.result.axioms at dependencies
  rw [schema_axioms_empty] at dependencies
  exact Finset.singleton_ne_empty _ dependencies

theorem changed_axiom_dependencies_refused :
    CachedSubstitution.applyExpected? emptyAxiomPolicy (start [tainted]) 0 schema.proof.result
      (ParameterSchemaCompilation.mapping types names targetNames theta) ("changed-axioms", 0) = none :=
  CachedSubstitution.applyExpected_mismatch emptyAxiomPolicy (start [tainted]) 0 tainted schema.proof.result
    (ParameterSchemaCompilation.mapping types names targetNames theta) ("changed-axioms", 0) rfl tainted_different

#print axioms expanded_parents
#print axioms distinct_roots_remain_distinct
#print axioms changed_axiom_dependencies_refused

end Mettapedia.Languages.HOLLight.CachedSubstitutionControls
