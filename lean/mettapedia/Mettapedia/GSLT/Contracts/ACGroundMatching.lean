import Mettapedia.GSLT.Contracts.ACReplacement
import Mettapedia.GSLT.Contracts.ACUGroundMatching

/-!
# Open ground matching without a unit

The AC matcher reuses the bounded bag search, but each metavariable
must bind a nonempty bag. An empty *frame* is still a root redex.
These are different roles for emptiness. The correctness proof
reflects the frame back to a unit-free context of the AC source.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ACUReplacement.GroundMatching

universe u v
variable {Var : Type u} {Atom : Type v}

inductive Template.UnitFree : Template Var Atom → Prop where
  | hole (v : Var) : Template.UnitFree (.hole v)
  | atom (a : Atom) : Template.UnitFree (.atom a)
  | op {a b : Template Var Atom} : a.UnitFree → b.UnitFree → Template.UnitFree (.op a b)

theorem Template.UnitFree.instantiate {p : Template Var Atom} (fixed : p.UnitFree)
    {values : Var → Term Atom} (nonempty : ∀ v, AC.UnitFree (values v)) :
    AC.UnitFree (p.instantiate values) := by
  induction fixed with
  | hole v => exact nonempty v
  | atom a => exact .atom a
  | op _ _ first second => exact .op first second

section Search

variable [Fintype Var] [DecidableEq Var] [DecidableEq Atom]

def fitsAC (rule : Schema Var Atom) (subject : Multiset Atom) : Finset (Var → Multiset Atom) :=
  (fits rule subject).filter (fun values => ∀ var, values var ≠ 0)

def successorKeysAC (rule : Schema Var Atom) (subject : Multiset Atom) : Finset (Multiset Atom) :=
  (fitsAC rule subject).image fun values =>
    rule.rhs.evaluate values + (subject - rule.lhs.evaluate values)

theorem mem_successorKeysAC_iff (rule : Schema Var Atom) (before after : Multiset Atom) :
    after ∈ successorKeysAC rule before ↔
      ∃ values frame, (∀ v, values v ≠ 0) ∧ before = rule.lhs.evaluate values + frame ∧
        after = rule.rhs.evaluate values + frame := by
  simp only [successorKeysAC, fitsAC, Finset.mem_image, Finset.mem_filter, mem_fits_iff]
  constructor
  · rintro ⟨values, ⟨⟨frame, full⟩, nonempty⟩, result⟩
    refine ⟨values, frame, nonempty, full, ?_⟩
    rw [← result, full, Multiset.add_comm (rule.lhs.evaluate values) frame,
      Multiset.add_sub_cancel_right]
  · rintro ⟨values, frame, nonempty, full, result⟩
    refine ⟨values, ⟨⟨frame, full⟩, nonempty⟩, ?_⟩
    rw [full, Multiset.add_comm (rule.lhs.evaluate values) frame,
      Multiset.add_sub_cancel_right, result]

theorem canonical_AC_successors_exact (rule : Schema Var Atom) {before after : Term Atom}
    (lhs : rule.lhs.UnitFree) (rhs : rule.rhs.UnitFree)
    (beforeFree : AC.UnitFree before) (afterFree : AC.UnitFree after) :
    operands after ∈ successorKeysAC rule (operands before) ↔
      ∃ (values : Var → Term Atom) (context : Context Atom),
        (∀ v, AC.UnitFree (values v)) ∧ AC.UnitFreeContext context ∧
        AC.Equation before (context.plug (rule.lhs.instantiate values)) ∧
        AC.Equation (context.plug (rule.rhs.instantiate values)) after := by
  constructor
  · intro found
    obtain ⟨values, frame, nonempty, full, result⟩ := (mem_successorKeysAC_iff ..).mp found
    choose terms free same using fun v => AC.exists_unitFree_spelling (values v) (nonempty v)
    have equal : (fun v => operands (terms v)) = values := funext same
    let concrete := rule.instanceAt terms
    have listed : operands after ∈ successors [concrete] (operands before) := by
      apply (mem_successors_iff ..).mpr
      apply (reduces_iff_extension _ _ _).mpr
      refine ⟨concrete, by simp, frame, ?_, ?_⟩
      · simpa only [concrete, Schema.instanceAt, Template.operands_instantiate, equal] using full
      · simpa only [concrete, Schema.instanceAt, Template.operands_instantiate, equal] using result
    have rulesFree : ∀ r ∈ [concrete], AC.UnitFree r.lhs ∧ AC.UnitFree r.rhs := by
      intro r member
      have sameRule := List.mem_singleton.mp member
      subst r
      exact ⟨lhs.instantiate free, rhs.instantiate free⟩
    obtain ⟨r, declared, context, contextFree, first, last⟩ :=
      (AC.mem_successors_iff_ac_context [concrete] rulesFree beforeFree afterFree).mp listed
    have sameRule := List.mem_singleton.mp declared
    subst r
    exact ⟨terms, context, free, contextFree, first, last⟩
  · rintro ⟨terms, context, free, _, first, last⟩
    let concrete := rule.instanceAt terms
    have step : Reduces (· = concrete) before after :=
      (reduces_iff_context _ _ _).mpr
        ⟨concrete, rfl, context, first.toACU, last.toACU⟩
    obtain ⟨r, rfl, frame, full, result⟩ := (reduces_iff_extension _ _ _).mp step
    refine (mem_successorKeysAC_iff ..).mpr ⟨fun v => operands (terms v), frame, ?_, ?_, ?_⟩
    · intro v empty
      have positive := (free v).operands_pos
      simp [empty] at positive
    · simpa only [concrete, Schema.instanceAt, Template.operands_instantiate] using full
    · simpa only [concrete, Schema.instanceAt, Template.operands_instantiate] using result

end Search

namespace ACControls

private def project : Schema (Fin 1) Nat :=
  ⟨.op (.atom 0) (.hole 0), .hole 0, by intro v; right; exact Subsingleton.elim _ _⟩

theorem nonempty_binding_at_root :
    ({1} : Multiset Nat) ∈ successorKeysAC project (([0, 1] : List Nat) : Multiset Nat) :=
  (mem_successorKeysAC_iff ..).mpr ⟨fun _ => {1}, 0, by intro _; exact Multiset.singleton_ne_zero _,
    by decide, by decide⟩

theorem empty_binding_separates_ac_from_acu :
    (0 : Multiset Nat) ∈ successorKeys project {0} ∧
      (0 : Multiset Nat) ∉ successorKeysAC project {0} := by
  refine ⟨(mem_successorKeys_iff ..).mpr ⟨fun _ => 0, 0, by decide, by decide⟩, ?_⟩
  intro wrong
  obtain ⟨values, frame, nonempty, _, result⟩ := (mem_successorKeysAC_iff ..).mp wrong
  have count := congrArg Multiset.card result
  change (0 : Multiset Nat).card = (values 0 + frame).card at count
  simp only [Multiset.card_zero, Multiset.card_add] at count
  exact nonempty 0 (Multiset.card_eq_zero.mp (by omega))

end ACControls

#print axioms canonical_AC_successors_exact
#print axioms ACControls.nonempty_binding_at_root
#print axioms ACControls.empty_binding_separates_ac_from_acu

end Mettapedia.GSLT.Contracts.ACUReplacement.GroundMatching
