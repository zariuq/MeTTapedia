import Mettapedia.Languages.Agda.Structural.Rules
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCongruence

/-!
# The structural computation presentation

Computational roots are authored once. Congruences are generated from each
non-nullary operator's binding signature and argument positions. Named
constants, literal values, and projections have no arguments and therefore
need no congruence declarations.

This is the computation presentation of the raw fragment. Dependent typing,
conversion, and signature admission are subsequent judgment interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

/-- All operators possessing an argument, in signature declaration order. -/
def operatorsWithArguments : List (Sigma Op) :=
  [⟨.term, .lam⟩, ⟨.term, .lamNoAbs⟩, ⟨.term, .pi⟩, ⟨.term, .piNoAbs⟩,
   ⟨.term, .eliminate⟩, ⟨.term, .sortTerm⟩, ⟨.term, .levelTerm⟩,
   ⟨.type, .el⟩, ⟨.sort, .set⟩, ⟨.sort, .prop⟩,
   ⟨.level, .levelSuc⟩, ⟨.level, .levelMax⟩, ⟨.level, .levelNeutral⟩,
   ⟨.elim, .apply⟩, ⟨.spine, .cons⟩, ⟨.spine, .append⟩]

def generatedCongruences : List (LocalRule sig) :=
  operatorsWithArguments.flatMap fun ⟨_, op⟩ =>
    (List.finRange (sig.arity op).length).map fun position =>
      IntrinsicScopedLocalCongruence.rule op position

def computationRules : List (LocalRule sig) := roots ++ generatedCongruences

theorem congruence_inventory : generatedCongruences.length = 23 := rfl
theorem computation_inventory : computationRules.length = 29 := rfl

/-- The operator inventory is complete precisely where a congruence can fire. -/
theorem operator_inventory_complete {s : Srt} (op : Op s)
    (position : Fin (sig.arity op).length) :
    (⟨s, op⟩ : Sigma Op) ∈ operatorsWithArguments := by
  cases op <;> simp [sig] at position ⊢
  all_goals simp [operatorsWithArguments]
  all_goals exact Fin.elim0 position

theorem generated_congruence_present {s : Srt} (op : Op s)
    (position : Fin (sig.arity op).length) :
    IntrinsicScopedLocalCongruence.rule op position ∈ generatedCongruences := by
  apply List.mem_flatMap.mpr
  refine ⟨⟨s, op⟩, operator_inventory_complete op position, ?_⟩
  exact List.mem_map.mpr ⟨position, List.mem_finRange position, rfl⟩

/-- This invokes the generic indexed-polynomial construction for the exact
rule table, retaining ordered children and declaration addresses. -/
def computationPresentation := presentation computationRules (BindingCloneAlgebra.terms sig)

end Mettapedia.Languages.Agda.Structural.Authored
