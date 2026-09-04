import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaLineageSafety

/-!
# Fixed-head structure for executable-schema lineage

Finite schema lineage and fixed expression heads are independent facts. This
module separates the latter from inventory membership so large compiler
inventories can establish their initial authorization structurally rather than
by one monolithic membership reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  /-- Every expression in an atom has a non-variable head. -/
  def fixedExpressionHeads : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | .expression children =>
        match children with
        | .var _ :: _ => false
        | _ => fixedExpressionHeadsList children

  /-- List companion of `fixedExpressionHeads`. -/
  def fixedExpressionHeadsList : List Atom → Bool
    | [] => true
    | atom :: atoms =>
        fixedExpressionHeads atom && fixedExpressionHeadsList atoms
end

mutual
  /-- Fixed expression heads plus recursive schema provenance imply the full
lineage authorization predicate. -/
  theorem fixedExpressionHeads_authorized
      (schemas : List RawExecFact) : ∀ atom,
      fixedExpressionHeads atom = true →
      ExecutableSubtermsFromSchemas schemas atom →
        ExecutableSchemaAtomAuthorized schemas atom
    | .var _, _, _ => trivial
    | .symbol _, _, _ => trivial
    | .grounded _, _, _ => trivial
    | .expression children, fixed, within => by
        cases children with
        | nil => exact ⟨trivial, trivial⟩
        | cons head tail =>
            cases head with
            | var name =>
                simp [fixedExpressionHeads] at fixed
            | symbol name =>
                have childrenFixed :
                    fixedExpressionHeadsList (.symbol name :: tail) = true := by
                  simpa [fixedExpressionHeads] using fixed
                have childrenAuthorized :=
                  fixedExpressionHeadsList_authorized schemas
                    (.symbol name :: tail) childrenFixed (by
                      intro child childMember
                      exact (executableSubtermsFromSchemas_hereditary schemas)
                        (.symbol name :: tail) within child childMember)
                refine ⟨childrenAuthorized, ?_⟩
                by_cases isExec : name = "exec"
                · subst name
                  cases extracted :
                      extractRawExecFact (.expression (.symbol "exec" :: tail)) with
                  | none => trivial
                  | some raw =>
                      simpa [ExecutableSchemaAtomAuthorized, extracted] using
                        within raw
                          (extractRawExecFact_mem_rawExecSubterms extracted)
                · simp [isExec]
            | grounded value =>
                have childrenFixed :
                    fixedExpressionHeadsList (.grounded value :: tail) = true := by
                  simpa [fixedExpressionHeads] using fixed
                have childrenAuthorized :=
                  fixedExpressionHeadsList_authorized schemas
                    (.grounded value :: tail) childrenFixed (by
                      intro child childMember
                      exact (executableSubtermsFromSchemas_hereditary schemas)
                        (.grounded value :: tail) within child childMember)
                exact ⟨childrenAuthorized, trivial⟩
            | expression inner =>
                have childrenFixed :
                    fixedExpressionHeadsList (.expression inner :: tail) = true := by
                  simpa [fixedExpressionHeads] using fixed
                have childrenAuthorized :=
                  fixedExpressionHeadsList_authorized schemas
                    (.expression inner :: tail) childrenFixed (by
                      intro child childMember
                      exact (executableSubtermsFromSchemas_hereditary schemas)
                        (.expression inner :: tail) within child childMember)
                exact ⟨childrenAuthorized, trivial⟩

  /-- List companion of `fixedExpressionHeads_authorized`. -/
  theorem fixedExpressionHeadsList_authorized
      (schemas : List RawExecFact) : ∀ atoms,
      fixedExpressionHeadsList atoms = true →
      (∀ atom ∈ atoms, ExecutableSubtermsFromSchemas schemas atom) →
        ExecutableSchemaAtomsAuthorized schemas atoms
    | [], _, _ => trivial
    | atom :: atoms, fixed, within => by
        have parts : fixedExpressionHeads atom = true ∧
            fixedExpressionHeadsList atoms = true := by
          simpa [fixedExpressionHeadsList, Bool.and_eq_true] using fixed
        refine ⟨fixedExpressionHeads_authorized schemas atom parts.1
          (within atom (by simp)), ?_⟩
        apply fixedExpressionHeadsList_authorized schemas atoms parts.2
        intro child childMember
        exact within child (List.mem_cons_of_mem atom childMember)
end

section AxiomAudit

#print axioms fixedExpressionHeads_authorized
#print axioms fixedExpressionHeadsList_authorized

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
