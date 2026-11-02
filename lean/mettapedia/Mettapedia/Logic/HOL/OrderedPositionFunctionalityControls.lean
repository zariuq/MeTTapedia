import Mettapedia.Logic.HOL.OrderedPositionFunctionality
import Mettapedia.Logic.HOL.OrderedPositionProofControls

/-!
# Realizable heterogeneous-position controls

Two live segments return distinct Boolean indices at different slots. Their
Peano premises hold in the existing standard natural-number model. This
separates functional lookup at one slot from uniform alignment of all slots.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls

open OrderedPositionPrograms SuccessorOrder
open OrderedPositionProofControls (number Symbol zero successor one model values full)

def assumptions : List (ClosedFormula Symbol) :=
  [NaturalNumeralProofs.separation zero successor, NaturalNumeralProofs.injectivity successor,
    NaturalRecursionProofs.inductionPrinciple zero successor]

def arithmetic : PeanoEvidence successor zero assumptions where
  separation := .hyp (Δ := assumptions) ⟨0, by decide⟩
  injectivity := .hyp (Δ := assumptions) ⟨1, by decide⟩
  induction := .hyp (Δ := assumptions) ⟨2, by decide⟩

theorem arithmetic_free : arithmetic.Free := by
  simp only [PeanoEvidence.Free, arithmetic, ProofSyntax.FunctionExtensionalityFree, and_self]

def plan : Plan Symbol [] number .prop := [(one, .top), (one, .bot)]

def firstRelation {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (compileAt zero successor plan Subst.id zero .top) :=
  compileAt_here zero successor (one, .top) [(one, .bot)] Subst.id zero .top
    (lessNext successor zero) (.eqRefl .top)

theorem firstRelation_free {hypotheses : List (ClosedFormula Symbol)} :
    (firstRelation (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  exact compileAt_here_free _ _ _ _ _ _ _ _ _ (lessNext_free _ _) True.intro

def secondRelation {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (compileAt zero successor plan Subst.id one .bot) :=
  compileAt_later zero successor (one, .top) [(one, .bot)] Subst.id one zero .bot
    (sumZero successor zero one)
    (compileAt_here zero successor (one, .bot) [] Subst.id zero .bot (lessNext successor zero) (.eqRefl .bot))

theorem secondRelation_free {hypotheses : List (ClosedFormula Symbol)} :
    (secondRelation (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  apply compileAt_later_free
  · exact sumZero_free _ _ _
  · apply compileAt_here_free
    · exact lessNext_free _ _
    · trivial

def firstQuery {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (.app (.app (graph zero successor plan) zero) .top) :=
  .impE (.eqPropER (graph_beta zero successor plan zero .top)) firstRelation

def secondQuery {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (.app (.app (graph zero successor plan) one) .bot) :=
  .impE (.eqPropER (graph_beta zero successor plan one .bot)) secondRelation

theorem firstQuery_free {hypotheses : List (ClosedFormula Symbol)} :
    (firstQuery (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  exact ⟨graph_beta_free _ _ _ _ _, firstRelation_free⟩

theorem secondQuery_free {hypotheses : List (ClosedFormula Symbol)} :
    (secondQuery (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  exact ⟨graph_beta_free _ _ _ _ _, secondRelation_free⟩

def firstUnique (target : ClosedFormula Symbol)
    (query : ProofSyntax Symbol assumptions (.app (.app (graph zero successor plan) zero) target)) :
    ProofSyntax Symbol assumptions (.eq target .top) :=
  graphFunctionality zero successor plan zero target .top arithmetic query firstQuery

def secondUnique (target : ClosedFormula Symbol)
    (query : ProofSyntax Symbol assumptions (.app (.app (graph zero successor plan) one) target)) :
    ProofSyntax Symbol assumptions (.eq target .bot) :=
  graphFunctionality zero successor plan one target .bot arithmetic query secondQuery

theorem secondUnique_free (target : ClosedFormula Symbol)
    (query : ProofSyntax Symbol assumptions (.app (.app (graph zero successor plan) one) target))
    (free : query.FunctionExtensionalityFree) :
    (secondUnique target query).FunctionExtensionalityFree := by
  apply graphFunctionality_free
  · exact arithmetic_free
  · exact free
  · exact secondQuery_free

theorem separation_valid :
    (model.denote (NaturalNumeralProofs.separation zero successor) @values).down := by
  change ∀ value : ULift.{1} Nat, True → ¬ ((ULift.up (value.down + 1) : ULift.{1} Nat) = ULift.up 0)
  intro value _ equal
  exact Nat.succ_ne_zero value.down (congrArg ULift.down equal)

theorem injectivity_valid :
    (model.denote (NaturalNumeralProofs.injectivity successor) @values).down := by
  change ∀ left : ULift.{1} Nat, True → ∀ right : ULift.{1} Nat, True →
    (((ULift.up (left.down + 1) : ULift.{1} Nat) = ULift.up (right.down + 1)) ↔ left = right)
  intro left _ right _
  constructor
  · intro equal
    apply ULift.ext
    exact Nat.succ.inj (congrArg ULift.down equal)
  · intro equal
    cases equal
    rfl

theorem induction_valid :
    (model.denote (NaturalRecursionProofs.inductionPrinciple zero successor) @values).down := by
  change ∀ predicate : Ty.denote model.Carrier (number ⇒ .prop), True →
    ((predicate (ULift.up 0)).down ∧
      (∀ value : ULift.{1} Nat, True → (predicate value).down → (predicate (ULift.up (value.down + 1))).down)) →
      ∀ value : ULift.{1} Nat, True → (predicate value).down
  intro predicate _ premises value _
  rcases value with ⟨n⟩
  induction n with
  | zero => exact premises.1
  | succ n previous => exact premises.2 (ULift.up n) trivial previous

theorem assumptions_realizable : ∀ formula ∈ assumptions, (model.denote formula @values).down := by
  intro formula member
  rcases List.mem_cons.mp member with same | member
  · subst formula
    exact separation_valid
  · rcases List.mem_cons.mp member with same | member
    · subst formula
      exact injectivity_valid
    · rcases List.mem_cons.mp member with same | member
      · subst formula
        exact induction_valid
      · exact False.elim (List.not_mem_nil member)

theorem distinct_live_indices :
    ¬ Nonempty (ProofSyntax Symbol assumptions (.eq (.top : ClosedFormula Symbol) .bot)) := by
  rintro ⟨proof⟩
  have impossible := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro type entry; nomatch entry) assumptions_realizable
  change True ↔ False at impossible
  exact impossible.mp True.intro

theorem first_wrong_index_refused :
    ¬ Nonempty (ProofSyntax Symbol assumptions (.app (.app (graph zero successor plan) zero) .bot)) := by
  rintro ⟨query⟩
  exact distinct_live_indices ⟨.eqSymm (firstUnique .bot query)⟩

theorem second_wrong_index_refused :
    ¬ Nonempty (ProofSyntax Symbol assumptions (.app (.app (graph zero successor plan) one) .top)) := by
  rintro ⟨query⟩
  exact distinct_live_indices ⟨secondUnique .top query⟩

open FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards

def fieldPlans : (occurrence : Fin OrderedPositionProofControls.inventory.fields.length) →
    FieldPlan Symbol [] (OrderedPositionProofControls.inventory.fields.get occurrence) number .prop :=
  Fin.cases [(.lam (weaken one), .lam (.var .vz)),
    (.lam (weaken one), .lam (.not (.var .vz)))] (fun impossible => Fin.elim0 impossible)

def fieldArguments : Arguments Symbol [] [Ty.prop] := (.top, PUnit.unit)
def fieldCount : ClosedTerm Symbol number := .app (.lam (weaken one)) .top
def fieldFirstIndex : ClosedFormula Symbol := .app (.lam (.var .vz)) .top
def fieldSecondIndex : ClosedFormula Symbol := .app (.lam (.not (.var .vz))) .top
def actualFieldPlan : Plan Symbol [] number .prop :=
  fieldTerms [Ty.prop] (fieldPlans OrderedPositionProofControls.only) Subst.id fieldArguments

def fieldCountBeta {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (.eq fieldCount one) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta (.top : ClosedFormula Symbol) (weaken one))
  rfl

theorem fieldCountBeta_free {hypotheses : List (ClosedFormula Symbol)} :
    (fieldCountBeta (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  unfold fieldCountBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def zeroBelowFieldCount {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (.app (.app (less successor) zero) fieldCount) :=
  .impE (.eqPropER (.eqAppArg (.app (less successor) zero) fieldCountBeta)) (lessNext successor zero)

theorem zeroBelowFieldCount_free {hypotheses : List (ClosedFormula Symbol)} :
    (zeroBelowFieldCount (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  exact ⟨fieldCountBeta_free, lessNext_free _ _⟩

def fieldSecondRelation {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses (compileAt zero successor actualFieldPlan Subst.id fieldCount fieldSecondIndex) :=
  compileAt_later zero successor (fieldCount, fieldFirstIndex) [(fieldCount, fieldSecondIndex)]
    Subst.id fieldCount zero fieldSecondIndex (sumZero successor zero fieldCount)
    (compileAt_here zero successor (fieldCount, fieldSecondIndex) [] Subst.id zero fieldSecondIndex
      zeroBelowFieldCount (.eqRefl fieldSecondIndex))

theorem fieldSecondRelation_free {hypotheses : List (ClosedFormula Symbol)} :
    (fieldSecondRelation (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  apply compileAt_later_free
  · exact sumZero_free _ _ _
  · apply compileAt_here_free
    · exact zeroBelowFieldCount_free
    · trivial

def fieldSecondQuery {hypotheses : List (ClosedFormula Symbol)} :
    ProofSyntax Symbol hypotheses
      (applyArguments [Ty.prop] (.app (.app (fieldGraph zero successor [Ty.prop]
        (fieldPlans OrderedPositionProofControls.only)) fieldCount) fieldSecondIndex) fieldArguments) :=
  .impE (.eqPropER (fieldGraph_beta zero successor [Ty.prop]
    (fieldPlans OrderedPositionProofControls.only) fieldCount fieldSecondIndex fieldArguments)) fieldSecondRelation

theorem fieldSecondQuery_free {hypotheses : List (ClosedFormula Symbol)} :
    (fieldSecondQuery (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, fieldSecondRelation_free⟩

def fieldComparison : ProofSyntax Symbol assumptions
    ((PositionPrograms.ofSegments OrderedPositionProofControls.inventory zero successor fieldPlans).indexComparison
      OrderedPositionProofControls.only fieldArguments fieldCount fieldSecondIndex) :=
  PositionPrograms.guardedIndexComparisonFromWitness OrderedPositionProofControls.inventory zero successor fieldPlans
    OrderedPositionProofControls.only fieldArguments fieldCount fieldSecondIndex arithmetic
    (fieldSecondQuery.prepend (applyArguments _
      (OrderedPositionProofControls.inventory.allowed OrderedPositionProofControls.only) fieldArguments))

theorem fieldComparison_free : fieldComparison.FunctionExtensionalityFree := by
  apply PositionPrograms.guardedIndexComparisonFromWitness_free
  · exact arithmetic_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr fieldSecondQuery_free

theorem original_field_indices_distinct :
    ¬ Nonempty (ProofSyntax Symbol assumptions (.eq fieldFirstIndex fieldSecondIndex)) := by
  rintro ⟨proof⟩
  have impossible := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro type entry; nomatch entry) assumptions_realizable
  change True ↔ ¬ True at impossible
  exact impossible.mp True.intro True.intro

#print axioms secondUnique_free
#print axioms assumptions_realizable
#print axioms distinct_live_indices
#print axioms first_wrong_index_refused
#print axioms second_wrong_index_refused
#print axioms fieldComparison_free
#print axioms original_field_indices_distinct

end Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls
