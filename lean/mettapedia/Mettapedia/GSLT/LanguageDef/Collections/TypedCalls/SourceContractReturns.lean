import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundBindFacts
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingReturns

/-!
# Typed results earned from compound source return continuations

A variable-pattern protected argument is ground and uninterpreted at entry.
The actual source return-continuation theorem then derives every completed
result, including multiplicity and source effects. Its result flags and
delivered polymorphic guard discharge do not require an output-value oracle.

This is the supported source return grammar, not a claim that all native
plan annotations or constructor-pattern returns have been lowered to it.
Declaration currentness and physical native metadata remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open UnifyingFrames OpenFrameEffects SourceCallAliasTransport SourceGroundEntryFacts

theorem source_ground_of_support : ∀ value : Atom,
    support value = ∅ → MORK.isGroundAtom value = true := by
  intro value
  induction value using Atom.rec
      (motive_2 := fun values => (∀ value ∈ values, support value = ∅) →
        MORK.isGroundAtom.isGroundList values = true) with
  | var name => intro ground; simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at ground
  | symbol _ => intro _; rfl
  | grounded _ => intro _; rfl
  | expression values ih =>
      intro ground
      apply ih
      intro value member
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro name occurs
      have escapes := (support_expression values name).mpr ⟨value, member, occurs⟩
      rw [ground] at escapes
      exact Finset.notMem_empty _ escapes
  | nil all => rfl
  | cons first rest ihFirst ihRest all =>
      simp only [MORK.isGroundAtom.isGroundList]
      rw [ihFirst (all first (by simp)), ihRest (fun value member => all value (by simp [member]))]
      rfl

def protectedFlags : ContractBindingFacts.ValueFlags := ⟨⟨true, true⟩, false⟩

theorem protected_value_faithful {decls : Decls} (bindings : MORK.Subst) (value : Atom)
    (good : GroundData decls value) :
    GroundUninterpretedVersions.Faithful decls (value, readBindings bindings) protectedFlags := by
  refine ⟨rfl, fun _ => ?_⟩
  have fixed : substA (readBindings bindings) value = value := by
    rw [← resolve_eq_subst]
    exact resolve_ground bindings value good.1
  change support (substA (readBindings bindings) value) = ∅ ∧
    (true = true → Uninterp decls (substA (readBindings bindings) value))
  rw [fixed]
  exact ⟨good.1, fun _ => good.2⟩

/-- Faithful protected-result metadata follows from source syntax and its
actual completed run, not from an assumed faithful result service. -/
theorem completed_source_faithful {registry : SpaceSemantics.Program} {decls : Decls}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (name : String)
    (expression : Atom) (returns : Unifying.ReturnsVariable name expression)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (entry : GroundData decls (Unifying.resolve bindings (.var name)))
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) :
    (∀ value ∈ values, value = Unifying.resolve bindings (.var name)) ∧
    ∀ value ∈ values, ∀ deliveredBindings,
      GroundUninterpretedVersions.Faithful decls (value, readBindings deliveredBindings) protectedFlags := by
  obtain ⟨final, answers, steps, returned, frames, finalState, finalInput, finalOutput, packets, counted⟩ :=
    Unifying.completed_protected_return bindings valid name expression returns state input output use
      (source_ground_of_support _ entry.1) completed
  have each : ∀ value ∈ values, value = Unifying.resolve bindings (.var name) := by
    rw [counted]
    intro value member
    exact (List.mem_replicate.mp member).2
  refine ⟨each, ?_⟩
  intro value member deliveredBindings
  rw [each value member]
  exact protected_value_faithful deliveredBindings _ entry

/-- The delivered guard preserves exactly the ordered run's answer bag.
The source run and its effects are unchanged; this boundary theorem concerns
only the already delivered results and does not re-execute the body. -/
theorem completed_source_guard_exact {registry : SpaceSemantics.Program} {decls : Decls}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (name : String)
    (expression : Atom) (returns : Unifying.ReturnsVariable name expression)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (entry : GroundData decls (Unifying.resolve bindings (.var name)))
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) (kind : Atom → String) :
    chainCall decls kind (fun _ => (values : Multiset Atom)) pairRow [Unifying.resolve bindings (.var name)] =
      (values : Multiset Atom) := by
  have each := (completed_source_faithful bindings valid name expression returns state input output use entry completed).1
  have exactGuard := UninterpretedLocalMultiplicity.pair_protocol_clean kind [] [] "a"
    (fun _ => (values : Multiset Atom)) [] [] (Unifying.resolve bindings (.var name)) rfl entry.2 (by
      intro result member
      have same := each result member
      refine ⟨Atom.var, ?_, fun _ => trivial⟩
      rw [substA_var_self]
      exact same)
  simpa [argCount, one_nsmul] using exactGuard

theorem checked_source_guard_exact {registry : SpaceSemantics.Program} {decls : Decls}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (name : String)
    (expression : Atom) (inspectionFuel : Nat)
    (checked : Unifying.checksReturnVariable name inspectionFuel expression = true)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (entry : GroundData decls (Unifying.resolve bindings (.var name)))
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) (kind : Atom → String) :
    chainCall decls kind (fun _ => (values : Multiset Atom)) pairRow [Unifying.resolve bindings (.var name)] =
      (values : Multiset Atom) :=
  completed_source_guard_exact bindings valid name expression
    (Unifying.checksReturnVariable_sound name inspectionFuel expression checked)
    state input output use entry completed kind

namespace Controls

theorem print_entry_idempotent : Unifying.Idempotent Unifying.ReturnControls.bindings := by
  intro name value found other member
  simp [Unifying.ReturnControls.bindings, MORK.Subst.lookup] at found
  rcases found with ⟨rfl, rfl⟩
  simp [Unifying.ReturnControls.num, MORK.atomFreeVars] at member

theorem complete_print_run :
    ∃ after, Unifying.run Unifying.ReturnControls.registry 200
      { state := Effects.empty,
        control := .evaluate Unifying.ReturnControls.bindings Unifying.ReturnControls.branchAndPrint } =
      .complete after
        [Unifying.ReturnControls.num 7, Unifying.ReturnControls.num 7, Unifying.ReturnControls.num 7]
        [] [Unifying.ReturnControls.num 1, Unifying.ReturnControls.num 1, Unifying.ReturnControls.num 2] := by
  have checked := Unifying.ReturnControls.duplicate_answers_keep_effect_order
  generalize completed : Unifying.run Unifying.ReturnControls.registry 200
    { state := Effects.empty, control := .evaluate Unifying.ReturnControls.bindings Unifying.ReturnControls.branchAndPrint } = result at checked
  cases result with
  | exhausted => cases checked
  | fault => cases checked
  | complete after values input output =>
      cases input with
      | cons => cases checked
      | nil =>
          simp only [Unifying.shown, Unifying.Shown.printed.injEq] at checked
          obtain ⟨rfl, rfl⟩ := checked
          exact ⟨after, rfl⟩

theorem effectful_compound_guard_keeps_three_occurrences (decls : Decls) (kind : Atom → String) :
    chainCall decls kind
      (fun _ => ([Unifying.ReturnControls.num 7, Unifying.ReturnControls.num 7,
        Unifying.ReturnControls.num 7] : Multiset Atom)) pairRow [Unifying.ReturnControls.num 7] =
      [Unifying.ReturnControls.num 7, Unifying.ReturnControls.num 7, Unifying.ReturnControls.num 7] := by
  obtain ⟨after, completed⟩ := complete_print_run
  exact checked_source_guard_exact Unifying.ReturnControls.bindings print_entry_idempotent "protected"
    Unifying.ReturnControls.branchAndPrint 3 Unifying.ReturnControls.return_recognizer_controls.1
    Effects.empty [] [] 0 ⟨by decide +kernel, by trivial⟩ completed kind

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns
