import Mettapedia.Languages.MM0.Presentation.SupportCorrespondence
import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalMembershipProgram

/-!
# Authored MM0 dependency checks

The formal binder determines which independence condition is required. The
target occurrence support determines whether the replacement preserves it.
These are different contexts. In particular, occurrence checking here retains
bound occurrences; definition admission uses a separate free-variable check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDependency

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def dependencyEquations : Program := [
  ⟨"depends-bound", "mm0:depends", [.list [.sym "MM0:Bound", v "sort"], v "position", v "index"],
    c "nik:nat-eq" [v "index", v "position"]⟩,
  ⟨"depends-regular", "mm0:depends",
    [.list [.sym "MM0:Regular", v "sort", v "dependencies"], v "position", v "index"],
    c "nik:nat-member" [v "index", v "dependencies"]⟩,
  ⟨"pair", "mm0:check-pair",
    [v "target", v "formal-bound", v "target-bound", v "binder", v "position", v "expression"],
    c "mm0:pair-depends" [c "mm0:depends" [v "binder", v "position", v "formal-bound"],
      v "target", v "target-bound", v "expression"]⟩,
  ⟨"pair-dependent", "mm0:pair-depends",
    [.sym "True", v "target", v "target-bound", v "expression"], .sym "True"⟩,
  ⟨"pair-independent", "mm0:pair-depends",
    [.sym "False", v "target", v "target-bound", v "expression"],
    c "mm0:support-disjoint" [c "mm0:support" [v "target", v "expression"], v "target-bound"]⟩,
  ⟨"pair-no-support", "mm0:support-disjoint", [.sym "None", v "target-bound"], .sym "False"⟩,
  ⟨"pair-support", "mm0:support-disjoint", [c "Some" [v "indices"], v "target-bound"],
    c "mm0:dependency-not" [c "nik:nat-member" [v "target-bound", v "indices"]]⟩,
  ⟨"not-true", "mm0:dependency-not", [.sym "True"], .sym "False"⟩,
  ⟨"not-false", "mm0:dependency-not", [.sym "False"], .sym "True"⟩]

def dependencyProgram : Program := ComputationalSupport.supportProgram ++
  (naturalMembershipProgram ++ dependencyEquations)

theorem dependencyProgram_leftLinear : LeftLinear dependencyProgram := by
  intro equation member
  rcases List.mem_append.mp member with old | new
  · exact ComputationalSupport.supportProgram_leftLinear equation old
  · rcases List.mem_append.mp new with shared | guest
    · exact naturalMembershipProgram_leftLinear equation shared
    · have all : LeftLinear dependencyEquations := by
        simp [LeftLinear, dependencyEquations, c, v, patternVarsList, patternVars]
      exact all equation guest

theorem dependencyProgram_dataSeparated : DataSeparated dependencyProgram computationalHost where
  undefined := by
    intro head member
    have prior := ComputationalSupport.supportProgram_dataSeparated.undefined head member
    simp only [dependencyProgram, Program.defines, List.any_append]
    change (ComputationalSupport.supportProgram.defines head ||
      (naturalMembershipProgram.defines head || dependencyEquations.defines head)) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := ComputationalSupport.supportProgram_dataSeparated.unhandled

end Mettapedia.Languages.MM0.Presentation.ComputationalDependency
