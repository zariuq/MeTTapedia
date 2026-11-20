import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

/-!
# The no-escape condition for closing over first-order unknowns

The context consists of retained knowledge, surviving ordinary rows and the
arguments captured by held rules. Knowledge moved inside the new row is not
silently treated as retained ambient knowledge. Replacing private unknowns may
change the closing row, but preserves every term of this context.

This is scope safety. It is not an equivalence between a shared hypothesis and
a universally reusable schema: the repeated-use control remains different even
when the outside context is empty. Automatic logical generalization additionally
needs a derivation with the appropriate eigenvariable or parametricity licence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Generalization

open Mettapedia.Logic.LP
open OneFrame (Terms)
open RuleOccurrences SetStoreSyntax

universe uOcc uR uC uZ
variable {signature : LPSignature} [DecidableEq signature.vars]
  {O : Type uOcc} [DecidableEq O] {R : Type uR} {C : Type uC} {Z : Type uZ}

noncomputable def contextTerms (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O) : List (Term signature) :=
  retainedKnowledge.map Prod.fst ++ retainedKnowledge.map Prod.snd ++
    ((s.present \ closing).toList.map s.label) ++ s.rules.toList.flatMap (fun occurrence => (s.held occurrence).args)

def Safe (localVars : Finset signature.vars) (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O) : Prop :=
  Disjoint localVars (varsIn (contextTerms s retainedKnowledge closing))

def replaceLocals (localVars : Finset signature.vars) (caller privateValues : Subst signature) : Subst signature :=
  fun name => if name ∈ localVars then privateValues name else caller name

theorem context_term_fixed (localVars : Finset signature.vars)
    (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O)
    (safe : Safe localVars s retainedKnowledge closing) (caller privateValues : Subst signature)
    (term : Term signature) (mentioned : term ∈ contextTerms s retainedKnowledge closing) :
    (replaceLocals localVars caller privateValues).applyTerm term = caller.applyTerm term := by
  apply apply_eq_of_agree
  intro name inside
  have contextual : name ∈ varsIn (contextTerms s retainedKnowledge closing) :=
    (mem_variables _ _).mpr ⟨term, mentioned, inside⟩
  have outside : name ∉ localVars := fun selected => Finset.disjoint_left.mp safe selected contextual
  exact if_neg outside

theorem retained_row_fixed (localVars : Finset signature.vars)
    (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O)
    (safe : Safe localVars s retainedKnowledge closing) (caller privateValues : Subst signature)
    (occurrence : O) (survives : occurrence ∈ s.present \ closing) :
    (replaceLocals localVars caller privateValues).applyTerm (s.label occurrence) =
      caller.applyTerm (s.label occurrence) := by
  apply context_term_fixed localVars s retainedKnowledge closing safe caller privateValues
  have member : s.label occurrence ∈ (s.present \ closing).toList.map s.label :=
    List.mem_map.mpr ⟨occurrence, Finset.mem_toList.mpr survives, rfl⟩
  simp only [contextTerms, List.mem_append]
  exact Or.inl (Or.inr member)

theorem captured_argument_fixed (localVars : Finset signature.vars)
    (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O)
    (safe : Safe localVars s retainedKnowledge closing) (caller privateValues : Subst signature)
    (occurrence : R) (held : occurrence ∈ s.rules) (argument : Term signature)
    (captured : argument ∈ (s.held occurrence).args) :
    (replaceLocals localVars caller privateValues).applyTerm argument = caller.applyTerm argument := by
  apply context_term_fixed localVars s retainedKnowledge closing safe caller privateValues
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨occurrence, Finset.mem_toList.mpr held, captured⟩

theorem retained_knowledge_models_iff (localVars : Finset signature.vars)
    (s : RState (Terms (Term signature)) O R C Z)
    (retainedKnowledge : EquationStore (Term signature)) (closing : Finset O)
    (safe : Safe localVars s retainedKnowledge closing) (caller privateValues : Subst signature) :
    (FirstOrder.action signature).Models (replaceLocals localVars caller privateValues) retainedKnowledge ↔
      (FirstOrder.action signature).Models caller retainedKnowledge := by
  have left : ∀ equation ∈ retainedKnowledge,
      (replaceLocals localVars caller privateValues).applyTerm equation.1 = caller.applyTerm equation.1 := by
    intro equation member
    apply context_term_fixed localVars s retainedKnowledge closing safe caller privateValues
    simp only [contextTerms, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (List.mem_map_of_mem member)))
  have right : ∀ equation ∈ retainedKnowledge,
      (replaceLocals localVars caller privateValues).applyTerm equation.2 = caller.applyTerm equation.2 := by
    intro equation member
    apply context_term_fixed localVars s retainedKnowledge closing safe caller privateValues
    simp only [contextTerms, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem member)))
  constructor
  · intro solved equation member
    have equationSolved := solved equation member
    change (replaceLocals localVars caller privateValues).applyTerm equation.1 =
      (replaceLocals localVars caller privateValues).applyTerm equation.2 at equationSolved
    rw [left equation member, right equation member] at equationSolved
    exact equationSolved
  · intro solved equation member
    change (replaceLocals localVars caller privateValues).applyTerm equation.1 =
      (replaceLocals localVars caller privateValues).applyTerm equation.2
    rw [left equation member, right equation member]
    exact solved equation member

namespace Controls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def state (present : Finset Nat) : RState (Terms (Term atoms)) Nat Nat Unit Unit :=
  ⟨⟨PUnit.unit, [], present, fun _ => .var 0⟩, ∅, fun _ => ⟨(), [], .persistent, ()⟩⟩

theorem isolated_unknown_is_scope_safe : Safe {0} (state {0}) [] {0} := by
  simp [Safe, contextTerms, state, varsIn]

theorem an_unknown_in_another_row_escapes : ¬ Safe {0} (state {0, 1}) [] {0} := by
  intro safe
  have survives : (1 : Nat) ∈ (state {0, 1}).present \ {0} := by decide
  have fixed := retained_row_fixed {0} (state {0, 1}) [] {0} safe
    (QuantifierControls.point 5) (QuantifierControls.point 6) 1 survives
  have impossible : (6 : Nat) = 5 := Term.const.inj fixed
  omega

theorem scope_safety_does_not_change_the_quantifier :
    Safe {0} (state {0}) [] {0} ∧
      (∃ σ : Subst atoms,
        Row.ReadsAt QuantifierControls.X (b := PUnit.unit) σ (QuantifierControls.c 5) QuantifierControls.schematic ∧
        Row.ReadsAt QuantifierControls.X (b := PUnit.unit) σ (QuantifierControls.c 6) QuantifierControls.schematic) ∧
      ¬ ∃ σ : Subst atoms,
        Row.ReadsAt QuantifierControls.X (b := PUnit.unit) σ (QuantifierControls.c 5) QuantifierControls.shared ∧
        Row.ReadsAt QuantifierControls.X (b := PUnit.unit) σ (QuantifierControls.c 6) QuantifierControls.shared :=
  ⟨isolated_unknown_is_scope_safe, QuantifierControls.fresh_uses_do_not_preserve_shared_aliases⟩

end Controls

#print axioms context_term_fixed
#print axioms captured_argument_fixed
#print axioms retained_knowledge_models_iff
#print axioms Controls.an_unknown_in_another_row_escapes
#print axioms Controls.scope_safety_does_not_change_the_quantifier

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Generalization
