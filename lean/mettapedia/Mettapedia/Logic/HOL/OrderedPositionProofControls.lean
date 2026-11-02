import Mettapedia.Logic.HOL.OrderedPositionIndexComparisons
import Mettapedia.Logic.HOL.Soundness

/-!
# Ordered-index proof controls

Repeated shared-index segments include zero counts. A field guard can justify
alignment which is false outside that guard. Standard natural-number models
separate heterogeneous active indices and an unaligned zero-count segment.
The latter is semantically dead, but does not satisfy uniform alignment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionProofControls

open OrderedPositionPrograms FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards

abbrev number : Ty Unit := .base ()
inductive Symbol : Ty Unit → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)

def zero : ClosedTerm Symbol number := .const .zero
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor
def one : ClosedTerm Symbol number := .app successor zero
def model : HenkinModel.{0,0,0} Unit Symbol := .standard (fun _ => ULift.{1} Nat)
  (fun symbol => match symbol with | .zero => .up 0 | .successor => fun value => .up (value.down + 1))
def values : model.Valuation [] := fun impossible => nomatch impossible
def numbers : Nat ≃ ULift.{1} Nat := (Equiv.ulift : ULift.{1} Nat ≃ Nat).symm
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _
theorem zero_preserved : model.denote zero values = numbers 0 := rfl
theorem successor_preserved (n : Nat) : model.denote successor values (numbers n) = numbers (n + 1) := rfl

def inventory : ConstructorPrograms Symbol [] where
  fields := [[.prop]]
  number := number
  index := .prop
  numeral := fun _ => zero
  allowed := Fin.cases (.lam (.var .vz)) (fun impossible => Fin.elim0 impossible)
  result := Fin.cases (.lam (.var .vz)) (fun impossible => Fin.elim0 impossible)

def only : Fin inventory.fields.length := ⟨0, by decide⟩
def plans : (occurrence : Fin inventory.fields.length) →
    FieldPlan Symbol [] (inventory.fields.get occurrence) number .prop :=
  Fin.cases [(.lam (weaken zero), .lam (.var .vz)), (.lam (weaken one), .lam (.var .vz)),
      (.lam (weaken zero), .lam (.var .vz))]
    (fun impossible => Fin.elim0 impossible)

def trueArguments : Arguments Symbol [] (inventory.fields.get only) := (.top, PUnit.unit)
def falseArguments : Arguments Symbol [] (inventory.fields.get only) := (.bot, PUnit.unit)

def alignedTrue {assumptions : List (ClosedFormula Symbol)} (position : Fin (plans only).length) :
    ProofSyntax Symbol assumptions (.eq (applyFields _ ((plans only).get position).2 trueArguments) .top) := by
  refine Fin.cases ?_ (fun next => Fin.cases ?_ (fun last => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) last) next) position
  all_goals exact .beta .top (.var .vz)

theorem alignedTrue_free {assumptions : List (ClosedFormula Symbol)} (position : Fin (plans only).length) :
    (alignedTrue (assumptions := assumptions) position).FunctionExtensionalityFree := by
  refine Fin.cases ?_ (fun next => Fin.cases ?_ (fun last => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) last) next) position
  all_goals trivial

def repeatedComparison : ProofSyntax Symbol []
    ((PositionPrograms.ofSegments inventory zero successor plans).indexComparison only trueArguments zero .top) :=
  PositionPrograms.uniformIndexComparison inventory zero successor plans only trueArguments zero .top alignedTrue

theorem repeatedComparison_free : repeatedComparison.FunctionExtensionalityFree :=
  PositionPrograms.uniformIndexComparison_free inventory zero successor plans only trueArguments zero .top alignedTrue alignedTrue_free

def falseAllowed : ClosedFormula Symbol := applyArguments _ (inventory.allowed only) falseArguments

def guardedFalseAlignment (position : Fin (plans only).length) :
    ProofSyntax Symbol [falseAllowed] (.eq (applyFields _ ((plans only).get position).2 falseArguments) .top) :=
  .botE (.impE (.eqPropEL (.beta .bot (.var .vz))) (.hyp 0))

theorem guardedFalseAlignment_free (position : Fin (plans only).length) :
    (guardedFalseAlignment position).FunctionExtensionalityFree := by
  unfold guardedFalseAlignment
  trivial

def guardedFalseComparison : ProofSyntax Symbol []
    ((PositionPrograms.ofSegments inventory zero successor plans).indexComparison only falseArguments zero .top) :=
  PositionPrograms.guardedUniformIndexComparison inventory zero successor plans only falseArguments zero .top guardedFalseAlignment

theorem guardedFalseComparison_free : guardedFalseComparison.FunctionExtensionalityFree :=
  PositionPrograms.guardedUniformIndexComparison_free inventory zero successor plans only falseArguments zero .top
    guardedFalseAlignment guardedFalseAlignment_free

theorem false_guard_cannot_supply_witness : ¬ Nonempty (ProofSyntax Symbol [] falseAllowed) := by
  rintro ⟨proof⟩
  have invalid := Soundness.extTheorem_sound proof.erase model (model.functionsRespectEqv_of_fullDomains full)
  change False at invalid
  exact invalid

def heterogeneous : Plan Symbol [] number .prop := [(zero, .top), (one, .bot)]
def deadUnaligned : Plan Symbol [] number .prop := [(one, .top), (zero, .bot)]
def heterogeneousQuery : ClosedFormula Symbol := .app (.app (graph zero successor heterogeneous) zero) .bot
def deadQuery : ClosedFormula Symbol := .app (.app (graph zero successor deadUnaligned) zero) .top

private theorem closedApplication (function : ClosedTerm Symbol (number ⇒ .prop ⇒ .prop))
    (argument : ClosedTerm Symbol number) (index : ClosedFormula Symbol) :
    (model.denote (.app (.app function argument) index) @values).down ↔
      (model.denote function @values (model.denote argument @values) (model.denote index @values)).down := Iff.rfl

theorem heterogeneous_valid : (model.denote heterogeneousQuery @values).down := by
  unfold heterogeneousQuery
  rw [closedApplication]
  rw [zero_preserved]
  apply (graph_denote zero successor model numbers full @values zero_preserved successor_preserved
    heterogeneous @values (.up 0) (.up False)).mpr
  rfl

theorem dead_unaligned_valid : (model.denote deadQuery @values).down := by
  unfold deadQuery
  rw [closedApplication]
  rw [zero_preserved]
  apply (graph_denote zero successor model numbers full @values zero_preserved successor_preserved
    deadUnaligned @values (.up 0) (.up True)).mpr
  rfl

theorem alignment_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol [heterogeneousQuery] (.eq .bot .top)) := by
  rintro ⟨proof⟩
  have invalid := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro type entry; nomatch entry)
    (by
      intro formula member
      have same := List.mem_singleton.mp member
      subst formula
      exact heterogeneous_valid)
  change False ↔ True at invalid
  exact invalid.mpr True.intro

theorem unaligned_dead_segment_is_outside_uniform_contract :
    ¬ Nonempty (ProofSyntax Symbol [] (.eq (deadUnaligned.get ⟨1, by decide⟩).2 .top)) := by
  rintro ⟨proof⟩
  have invalid := Soundness.extTheorem_sound proof.erase model (model.functionsRespectEqv_of_fullDomains full)
  change False ↔ True at invalid
  exact invalid.mpr True.intro

#print axioms repeatedComparison_free
#print axioms guardedFalseComparison_free
#print axioms alignment_cannot_be_dropped
#print axioms unaligned_dead_segment_is_outside_uniform_contract

end Mettapedia.Logic.HOL.OrderedPositionProofControls
