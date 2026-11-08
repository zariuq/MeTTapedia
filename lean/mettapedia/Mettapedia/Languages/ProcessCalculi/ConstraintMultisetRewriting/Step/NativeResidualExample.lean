import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosing

/-!
# Examples of the native residual

A native state with one shared name `X`, no occurrences and no knowledge, and live firings that make
one occurrence each, optionally telling `X` a constant (`maker`).

* **Positive** (`clear_makers`, `makers_each_after`, `makers_closing`): two firings that make different
  occurrences and tell nothing are admitted, leave each other clear, stay admitted after each other,
  and their two orders close.
* **Negative: joint consistency is needed** (`tellers_alone`, `tellers_not_after`): a firing telling
  `X = true` and one telling `X = false` are each admitted, and neither is admitted after the other.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual

namespace NativeResidualExample

/-- One sort and two constants. -/
abbrev tiny : Signature := ⟨Unit, fun _ => Bool, fun _ => []⟩

/-- No private locals. -/
def noLocals : Empty → MetaArity tiny := fun impossible => nomatch impossible

/-- One parameterless shared name. -/
def oneName : Unit → MetaArity tiny := fun _ => ([], ())

/-- A constant, in any frame. -/
def bit {V : Type} (declaration : V → MetaArity tiny) (value : Bool) :
    Term (signature tiny declaration) ([] : Ctx tiny) () :=
  .op (.inl value) .nil

/-- **The state**: the shared name `X`, no occurrences, no knowledge. -/
def initial : NativeState tiny ℕ ([] : Ctx tiny) () :=
  ⟨Empty, inferInstance, noLocals,
    { Names := Unit
      equality := inferInstance
      declarations := oneName
      occupied := ∅
      equations := []
      present := ∅
      rows := fun _ => ContextualConditionalRows.ofStored noLocals oneName (.shared (bit oneName true)) }⟩

/-- The shared name, in a rule. -/
def shared : Term (signature tiny (ContextualActivatedStep.source noLocals oneName)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.source noLocals oneName) (.inr ())

/-- A live firing that makes the occurrence `port`, publishing `false`, and tells `X` a constant when
asked to. -/
def maker (port : ℕ) (told : Option Bool) : LiveFiring initial where
  rule := ⟨[], [], (match told with
    | none => []
    | some value => [(shared, bit (ContextualActivatedStep.source noLocals oneName) value)]), [],
    [bit (ContextualActivatedStep.source noLocals oneName) false]⟩
  selection := ⟨[], [], [port]⟩
  outputs _ := bit (ContextualActivatedStep.target noLocals oneName) false
  patterns := []
  fuel := 0

/-- The scope a maker's rule opens at. -/
abbrev ruleScope (port : ℕ) : ℕ :=
  ContextualActivationScopes.scopeAt (∅ : Finset ℕ) (ContextualActivationScopes.rulePort (⟨[], [], [port]⟩ : Selection ℕ))

theorem maker_information_none (port : ℕ) : (maker port none).toNative.information = [] := rfl

theorem maker_information_some (port : ℕ) (value : Bool) :
    (maker port (some value)).toNative.information =
      [(observe (ContextualFreshening.termAt noLocals oneName (ruleScope port) shared),
        observe (bit (ContextualActivatedStep.target noLocals oneName) value))] := rfl

theorem told_value {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals oneName) next) (port : ℕ) (value : Bool)
    (solved : ContextualResidual.Models σ (maker port (some value)).toNative.information) :
    σ (.inr ()) = bit next value := by
  rw [maker_information_some] at solved
  have told := observe_injective (solved _ List.mem_cons_self)
  have opened : ContextualFreshening.termAt noLocals oneName (ruleScope port) shared =
      generator (ContextualActivatedStep.target noLocals oneName) (.inr ()) :=
    instantiate_generator (ContextualFreshening.assignment noLocals oneName (ruleScope port)) (.inr ())
  exact (instantiate_generator σ (.inr ())).symm.trans ((congrArg (instantiate σ) opened).symm.trans told)

/-- A solution telling `X` a constant. -/
def telling (value : Bool) :
    Assignment (ContextualActivatedStep.target noLocals oneName) (ContextualActivatedStep.target noLocals oneName)
  | .inl name => nomatch name.name
  | .inr () => bit (ContextualActivatedStep.target noLocals oneName) value

/-- **Every maker is admitted.** -/
theorem maker_realized (port : ℕ) (told : Option Bool) : (maker port told).toNative.Realized := by
  apply (native_admits_iff (S := tiny) (maker port told).toNative).mpr
  refine ⟨⟨List.nodup_nil, List.nodup_singleton port, rfl, rfl, ?_⟩, ?_, ?_, ?_⟩
  · cases told <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, fun _ member => by simp [Selection.commit] at member⟩
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
      simp
    · show Disjoint [port].toFinset (∅ : Finset ℕ)
      simp
  · cases told with
    | none => exact ⟨initial.infoFrame, generator _, fun _ member => absurd member List.not_mem_nil⟩
    | some value =>
        refine ⟨initial.infoFrame, telling value, ?_⟩
        show ContextualResidual.Models (telling value) (maker port (some value)).toNative.information
        rw [maker_information_some]
        intro equation member
        rw [List.mem_singleton.mp member]
        show observe (instantiate (telling value) (ContextualFreshening.termAt noLocals oneName (ruleScope port) shared)) =
          observe (instantiate (telling value) (bit _ value))
        congr 1
  · intro b σ _
    refine ⟨fun check member => ?_, fun query member => absurd member List.not_mem_nil⟩
    cases told <;> exact absurd member List.not_mem_nil

/-! ## Positive: makers of different occurrences -/

theorem clear_makers (port other : ℕ) (different : port ≠ other) :
    Clear (maker port none) (maker other none).selection (maker other none).rule (maker other none).outputs where
  takes := by
    show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
    simp
  ports := by
    show Disjoint [port].toFinset [other].toFinset
    simp [different]
  keeps := by
    show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
    simp
  consistent := ⟨initial.infoFrame, ⟨⟨generator _, generator _,
    fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil, rfl⟩⟩⟩
  blindTakes _ _ _ taken := absurd taken List.not_mem_nil
  blindOutputs _ _ _ _ := ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **Each stays admitted after the other**, for two makers of different occurrences. -/
theorem makers_each_after :
    (LiveFiring.residual (maker_realized 1 none) (maker 0 none)).Realized ∧
      (LiveFiring.residual (maker_realized 0 none) (maker 1 none)).Realized :=
  LiveFiring.each_after (maker_realized 0 none) (maker_realized 1 none) (clear_makers 0 1 (by decide))
    (clear_makers 1 0 (by decide))

/-- **The two orders close**, for two makers of different occurrences. -/
theorem makers_closing :
    (rawTarget (LiveFiring.residualExecution (maker_realized 0 none) (maker_realized 1 none)
        (clear_makers 0 1 (by decide)))).state.present =
      (rawTarget (LiveFiring.residualExecution (maker_realized 1 none) (maker_realized 0 none)
        (clear_makers 1 0 (by decide)))).state.present :=
  (LiveFiring.closing (maker_realized 0 none) (maker_realized 1 none) (clear_makers 0 1 (by decide))
    (clear_makers 1 0 (by decide))).1

/-! ## Negative: joint consistency is needed -/

/-- **Each teller is admitted alone.** -/
theorem tellers_alone : (maker 0 (some true)).toNative.Realized ∧ (maker 1 (some false)).toNative.Realized :=
  ⟨maker_realized 0 (some true), maker_realized 1 (some false)⟩

/-- **Neither teller is admitted after the other**: every solution of the residual's information
restricts to a joint solution, which would tell `X` both constants. -/
theorem tellers_not_after :
    ¬ (LiveFiring.residual (maker_realized 1 (some false)) (maker 0 (some true))).Realized ∧
      ¬ (LiveFiring.residual (maker_realized 0 (some true)) (maker 1 (some false))).Realized := by
  have contradiction : ∀ (port other : ℕ) (first second : Bool), first ≠ second →
      ¬ (LiveFiring.residual (maker_realized other (some second)) (maker port (some first))).Realized := by
    intro port other first second different realized
    obtain ⟨_, _, ⟨b, ρ, solved⟩, _⟩ := (native_admits_iff (S := tiny) _).mp realized
    have unmade : ∀ o ∈ (maker port (some first)).selection.taken ++ (maker port (some first)).selection.read,
        o ∉ (LiveFiring.execution (maker_realized other (some second))).selection.made :=
      fun _ member => absurd member List.not_mem_nil
    have J := Joint.ofResidual (LiveFiring.execution (maker_realized other (some second))) (maker port (some first))
      unmade ρ solved
    have rule := (LiveFiring.execution_data (maker_realized other (some second))).1
    have selection := (LiveFiring.execution_data (maker_realized other (some second))).2.1
    have problem : problemOf initial (LiveFiring.execution (maker_realized other (some second))).selection
        (LiveFiring.execution (maker_realized other (some second))).rule =
        (maker other (some second)).toNative.information := by
      rw [rule, selection]
      rfl
    have rightModels : ContextualResidual.Models J.right (maker other (some second)).toNative.information :=
      Eq.mp (congrArg (ContextualResidual.Models J.right) problem) J.right_models
    have left := told_value J.left port first J.left_models
    have right := told_value J.right other second rightModels
    have clash := left.symm.trans ((J.agree_at ()).trans right)
    unfold bit at clash
    cases clash
    exact different rfl
  exact ⟨contradiction 0 1 true false (by decide), contradiction 1 0 false true (by decide)⟩

end NativeResidualExample

#print axioms NativeResidualExample.maker_realized
#print axioms NativeResidualExample.clear_makers
#print axioms NativeResidualExample.makers_each_after
#print axioms NativeResidualExample.makers_closing
#print axioms NativeResidualExample.tellers_alone
#print axioms NativeResidualExample.tellers_not_after

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
