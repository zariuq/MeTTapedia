import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderSchemaComprehension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBinding

/-!+# Existing programs recovered through finite schema arguments

All rules of the existing first-order program core have the same reduction
relation when their local variables are supplied as typed telescope tuples.
The consumers include actual admitted firings and the existing lexical
capture example. No ordered evaluator is identified with a single firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderSchemaComprehension.Controls

open ProgramRows ProgramTranslation

theorem program_step_eq (fallback : Nat → Sx) :
    Rewrites Program.schema fallback = Program.Step := by
  rw [rewrites_eq, ← Program.step_eq_rewrites]

theorem program_execution_iff (fallback : Nat → Sx) (initial : List Sx) (final : Multiset Sx) :
    Relation.ReflTransGen (Rewrites Program.schema fallback) (initial : Multiset Sx) final ↔
      ∃ target : Config × Nat,
        Relation.ReflTransGen (Translated Program.schema)
          (ProgramTranslation.initial initial, 1) target ∧
        Represents target.1 final target.2 :=
  execution_iff Program.schema fallback Program.schema_wellFormed initial final

theorem atom_has_typed_arguments (fallback : Nat → Sx) (value environment continuation : Sx)
    (rest : Multiset Sx) :
    Fires fallback (Program.schema .atom)
      (Program.ev (Program.atom value) environment continuation ::ₘ rest)
      (Program.ret (Program.atom value) continuation ::ₘ rest) := by
  apply (fires_iff fallback _ _ _).mpr
  exact ⟨Program.args [value, environment, continuation], rest, rfl, rfl⟩

/-- The resulting resource multiset is recovered through the original
occurrence compiler, not merely through equality of source reductions. -/
theorem atom_has_actual_firing (fallback : Nat → Sx) (value environment continuation : Sx)
    (rest : Multiset Sx) {state : Config} {scope : Nat}
    (rep : Represents state
      (Program.ev (Program.atom value) environment continuation ::ₘ rest) scope) :
    ∃ taken read : List Occ,
      ((Program.schema .atom).firing scope taken read).Valid A Occ.label state ∧
      Represents (((Program.schema .atom).firing scope taken read).result Occ.label state)
        (Program.ret (Program.atom value) continuation ::ₘ rest) (scope + 1) :=
  firing_sound fallback (Program.schema_wellFormed .atom) rep
    (atom_has_typed_arguments fallback value environment continuation rest)

/-- The entire existing capture-sensitive computation is a finite run of
schema-tuple applications, and every halted such run has the lexical result. -/
theorem lexical_binding_recovered (fallback : Nat → Sx) :
    Relation.ReflTransGen (Rewrites Program.schema fallback)
      ({Program.captureProgram} : Multiset Sx) {Program.ret (Program.atom Program.kz) Program.nil} ∧
    ∀ final, Relation.ReflTransGen (Rewrites Program.schema fallback)
        ({Program.captureProgram} : Multiset Sx) final →
      (∀ later, ¬ Rewrites Program.schema fallback final later) →
      final = {Program.ret (Program.atom Program.kz) Program.nil} := by
  rw [program_step_eq]
  exact ⟨Program.no_capture.2.1, Program.no_capture.2.2⟩

theorem captured_result_unreachable_when_halted (fallback : Nat → Sx) :
    ¬ (Relation.ReflTransGen (Rewrites Program.schema fallback)
        ({Program.captureProgram} : Multiset Sx)
        {Program.ret (Program.atom Program.kw) Program.nil} ∧
      ∀ later, ¬ Rewrites Program.schema fallback
        {Program.ret (Program.atom Program.kw) Program.nil} later) := by
  rintro ⟨path, halted⟩
  have same := (lexical_binding_recovered fallback).2 _ path halted
  have different : (Program.ret (Program.atom Program.kw) Program.nil : Sx) ≠
      Program.ret (Program.atom Program.kz) Program.nil := by decide
  exact different (Multiset.singleton_inj.mp same)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderSchemaComprehension.Controls
