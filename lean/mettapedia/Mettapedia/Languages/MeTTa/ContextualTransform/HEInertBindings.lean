import Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts

/-!
# Erasing an inert HE chain binder

This is the local-substitution chain rule, not PeTTa's unifying let rule.
The operand must be data in the actual minimal source judgment, and the
template must not mention the bound name. Other template variables and their
caller bindings remain unrestricted. Semantic erasure hides administrative
chain work; it does not assert equal finite implementation fuel cutoffs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEInertBindings

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful
open Spec.Match.Merge (AtomOccurs)
open HEStatefulContexts

theorem substitute_fresh (policy : Policy) (name : String) (value template : Entry.Value)
    (absent : ¬AtomOccurs template.erase name) :
    substituteBinder policy name value template = template := by
  induction template using Entry.Value.rec
      (motive_2 := fun children =>
        (∀ child ∈ children, ¬AtomOccurs child.erase name) →
          children.map (Entry.Value.substitute policy.rebuilding
            (fun key => if key = name then value else .var key)) = children) with
  | symbol => simp [substituteBinder, Entry.Value.substitute]
  | var key =>
      have different : key ≠ name := by
        intro same
        subst key
        apply absent
        simpa only [Entry.Value.erase] using AtomOccurs.var name
      simp [substituteBinder, Entry.Value.substitute, different]
  | grounded => simp [substituteBinder, Entry.Value.substitute]
  | expression readiness children ih =>
      simp only [Entry.Value.erase] at absent
      have unchanged := ih (fun child member occurs =>
        absent (.expression (List.mem_map.mpr ⟨child, member, rfl⟩) occurs))
      simp only [substituteBinder, Entry.Value.substitute, unchanged]
      cases policy.rebuilding <;> simp [Entry.Value.rebuildStatus]
  | nil _ => rfl
  | cons child children first rest allAbsent =>
      exact congrArg₂ List.cons (first (allAbsent child List.mem_cons_self))
        (rest (fun other member => allAbsent other (List.mem_cons_of_mem _ member)))

theorem minimal_data_exact {Context World : Type}
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {value : Entry.Value} {frame : Frame} {before after : World} {results : List Result}
    (inert : Minimal.embeddedInstruction value.erase = false) :
    MinimalRel environment label before live scope caller value frame results after
        (policy := policy) ↔ results = [(value, frame)] ∧ after = before := by
  constructor
  · intro run
    cases run <;> simp_all [Minimal.embeddedInstruction, Entry.Value.erase]
  · rintro ⟨rfl, rfl⟩
    exact .data inert

/-- The template retains its actual evaluation judgment and can perform
effects. Only the inert operand and unused local substitution disappear. -/
theorem inert_chain_exact {Context World : Type}
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {source template : Entry.Value} {name : String} {frame : Frame}
    {before after : World} {results : List Result}
    (inert : Minimal.embeddedInstruction source.erase = false)
    (absent : ¬AtomOccurs template.erase name) :
    MinimalRel environment label before live scope caller (chain source name template)
        frame results after (policy := policy) ↔
      MinimalRel environment label before live scope caller template frame results after
        (policy := policy) := by
  rw [chain_exact]
  constructor
  · rintro ⟨middle, selected, initialized, continued⟩
    obtain ⟨rfl, rfl⟩ := (minimal_data_exact inert).mp initialized
    have one := BoundaryBatchRel.single_iff.mp continued
    cases one with
    | chain run =>
        rwa [substitute_fresh policy name _ template absent] at run
  · intro continued
    refine ⟨before, [(source, frame)], .data inert, ?_⟩
    apply BoundaryBatchRel.single_iff.mpr
    apply Stateful.BoundaryRel.chain
    rwa [substitute_fresh policy name _ template absent]

end Mettapedia.Languages.MeTTa.ContextualTransform.HEInertBindings
