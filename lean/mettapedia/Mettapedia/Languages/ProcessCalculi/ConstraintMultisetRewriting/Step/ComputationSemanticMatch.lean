import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationVectorProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq

/-!
# A real typed take in rule syntax, and its semantic matching boundary

One fixed closed rule takes add zero zero and makes zero. It is admitted
both on the literal call and on an already stored zero, because the typed
frame matches modulo beta/eta and declared conversion. Both inputs use the
same singleton program and the same opening; no reduct is supplied by a
state-dependent rule generator.

The latter firing is a semantic stutter on a syntactically normal source
term. Thus this ordinary rule-syntax program is not an exact implementation
of syntactic source reduction through the identity representation. Quoted
code or a separately justified intensional execution discipline is needed
when that stronger contract is intended. This is a positive typed-program
control and a separating example, not a general compiler.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SemanticMatch

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (zeroC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D numType level1)

abbrev Γ := empty pkg
abbrev setting := Controls.setting
abbrev levels := setting.levels

def zeroRow : TotalTerm Γ := ⟨numType Γ, ⟨zeroC, D.zero_typed⟩⟩

def callRow : TotalTerm Γ :=
  ⟨numType Γ, ⟨addC zeroC zeroC, TowerVectorsPrograms.add_typed level1 D.zero_typed D.zero_typed⟩⟩

theorem call_equivalent_zero : (frames levels).E callRow zeroRow := by
  apply (equivalent_iff levels callRow zeroRow).mpr
  refine ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩, ?_⟩
  exact (Controls.qualified.subjectReduction Γ.formed (.single (Controls.zeroAction zeroC).sound)
    callRow.2.typed).2

def store (stored : TotalTerm Γ) : State pkg Nat := ⟨Γ, [], {0}, fun _ => stored⟩

def nativeFiring (stored : TotalTerm Γ) : Firing levels (store stored) :=
  ⟨.nil Γ, [0], [], [callRow], [], [(1, Make.ofRow zeroRow)], [], [], []⟩

theorem information_eq (stored : TotalTerm Γ) :
    (nativeFiring stored).information = [(callRow, stored)] := by
  change [(callRow, stored.reindex (𝟙 Γ))] = [(callRow, stored)]
  rw [reindex_id]

theorem native_admitted (stored : TotalTerm Γ) (matched : (frames levels).E callRow stored) :
    (step levels Nat).Admits (nativeFiring stored) := by
  apply (DependentFull.admits_iff (nativeFiring stored)).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [nativeFiring], by simp [nativeFiring, Firing.made], rfl, rfl, ?_⟩
    intro made member
    obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped zeroRow
  · simp [nativeFiring, store, Firing.made]
  · rw [information_eq]
    refine ⟨Γ, 𝟙 Γ, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change (frames levels).E (callRow.reindex (𝟙 Γ)) (stored.reindex (𝟙 Γ))
    rw [reindex_id, reindex_id]
    exact matched
  · exact fun _ _ _ => Frames.models_nil _
  · intro query member
    cases member

def rule : RuleSyntax.Rule (RuleSyntax.Dependent.Terms pkg) :=
  ⟨Γ, ⟨[callRow], [], [], [], [zeroRow]⟩, []⟩

def program : RuleSyntax.Program (RuleSyntax.Dependent.Terms pkg) := {rule}

theorem program_finite : program.Finite := Set.finite_singleton _

def opening : RuleSyntax.Firing Nat RuleSyntax.Dependent.helperExtensions program Γ :=
  ⟨rule, Set.mem_singleton _, .nil Γ, 𝟙 Γ, ⟨[0], [], [1]⟩, []⟩

theorem opening_fresh (stored : TotalTerm Γ) :
    opening.Fresh (frames levels) (RuleSyntax.Dependent.toState (store stored)) := by
  intro observer first second
  have same : first = second := (toEmpty_unique observer first).trans (toEmpty_unique observer second).symm
  subst second
  refine ⟨first, fun term _ => ?_, fun term _ => ?_⟩
  · exact RuleSyntax.Dependent.act_id_equiv (frames levels) first term
  · exact RuleSyntax.Dependent.act_id_equiv (frames levels) first term

theorem opening_native (stored : TotalTerm Γ) :
    RuleSyntax.Dependent.toDependent (s := store stored) levels opening = nativeFiring stored := by
  change (⟨.nil Γ, [0], [], [callRow.reindex (𝟙 Γ)], [],
    [(1, Make.ofRow (zeroRow.reindex (𝟙 Γ)))], [], [], []⟩ : Firing levels (store stored)) = nativeFiring stored
  rfl

theorem rule_admitted (stored : TotalTerm Γ) (matched : (frames levels).E callRow stored) :
    (RuleSyntax.step (frames levels) Nat RuleSyntax.Dependent.helperExtensions program).Admits
      (s := RuleSyntax.Dependent.toState (store stored)) opening := by
  apply (RuleSyntax.Dependent.admits_toDependent_iff (store stored) opening).mpr
  refine ⟨?_, opening_fresh stored, rfl, rfl⟩
  rw [opening_native]
  exact native_admitted stored matched

theorem literal_call_admitted :
    (RuleSyntax.step (frames levels) Nat RuleSyntax.Dependent.helperExtensions program).Admits
      (s := RuleSyntax.Dependent.toState (store callRow)) opening :=
  rule_admitted callRow (((frames levels).equivalence Γ).refl callRow)

theorem already_zero_admitted :
    (RuleSyntax.step (frames levels) Nat RuleSyntax.Dependent.helperExtensions program).Admits
      (s := RuleSyntax.Dependent.toState (store zeroRow)) opening :=
  rule_admitted zeroRow call_equivalent_zero

theorem already_zero_opened_native :
    (RuleSyntax.Dependent.dependentOn levels program).Admits (nativeFiring zeroRow) :=
  (RuleSyntax.Dependent.dependentOn_admits_iff (store zeroRow) (nativeFiring zeroRow)).mpr
    ⟨opening, opening_native zeroRow, already_zero_admitted⟩

theorem syntactic_source_already_normal : ConstructorSystem.Normal pkg zeroRow.2.code :=
  Vectors.const_normal level1 (by decide)

theorem literal_pattern_does_not_match : callRow.2.code ≠ zeroRow.2.code := by decide

theorem semantic_rule_can_fire_on_syntactic_normal_form :
    ConstructorSystem.Normal pkg zeroRow.2.code ∧
      (RuleSyntax.Dependent.dependentOn levels program).Admits (nativeFiring zeroRow) :=
  ⟨syntactic_source_already_normal, already_zero_opened_native⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SemanticMatch

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SemanticMatch.literal_call_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SemanticMatch.semantic_rule_can_fire_on_syntactic_normal_form
