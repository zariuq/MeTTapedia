import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition
import Mettapedia.Logic.LP.TermEquality

/-!
# Ground, range-restricted rule instances as positive set propagation

Range restriction covers produced rows and equation guards. No existing
unknown is refined in the ground-store fragment. Rules retain their actual
syntax and substitutions; this is not a replacement unifier or match key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} [DecidableEq signature.vars]

def varsIn : List (Term signature) → Finset signature.vars
  | [] => ∅
  | term :: rest => term.freeVars ∪ varsIn rest

theorem mem_variables (terms : List (Term signature)) (v : signature.vars) :
    v ∈ varsIn terms ↔ ∃ term ∈ terms, v ∈ term.freeVars := by
  induction terms with
  | nil => simp [varsIn]
  | cons term rest ih => simp [varsIn, ih]

theorem apply_ground_iff (assignment : Subst signature) (term : Term signature) :
    (assignment.applyTerm term).isGround ↔ ∀ v ∈ term.freeVars, (assignment v).isGround := by
  induction term with
  | var v => simp [Subst.applyTerm, Term.freeVars]
  | const value => simp [Subst.applyTerm, Term.isGround, Term.freeVars]
  | app symbol terms ih =>
    simp only [Subst.applyTerm, Term.isGround, Term.freeVars]
    constructor
    · intro ground v member
      obtain ⟨i, _, inside⟩ := Finset.mem_biUnion.mp member
      exact (ih i).mp (ground i) v inside
    · intro ground i
      exact (ih i).mpr fun v member => ground v (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, member⟩)

theorem apply_eq_of_agree (first second : Subst signature) (term : Term signature)
    (agree : ∀ v ∈ term.freeVars, first v = second v) :
    first.applyTerm term = second.applyTerm term := by
  induction term with
  | var v => exact agree v (by simp [Term.freeVars])
  | const value => rfl
  | app symbol terms ih =>
    apply congrArg (Term.app symbol)
    funext i
    exact ih i fun v member => agree v (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, member⟩)

theorem agree_of_apply_eq (first second : Subst signature) (term : Term signature)
    (same : first.applyTerm term = second.applyTerm term) :
    ∀ v ∈ term.freeVars, first v = second v := by
  induction term with
  | var v =>
    intro w member
    obtain rfl := Finset.mem_singleton.mp member
    exact same
  | const value => intro v member; cases member
  | app symbol terms ih =>
    have fields := eq_of_heq (Term.app.inj same).2
    intro v member
    obtain ⟨i, _, inside⟩ := Finset.mem_biUnion.mp member
    exact ih i (congrFun fields i) v inside

structure Propagates (rule : Rule (Terms (Term signature))) : Prop where
  noTake : rule.body.take = []
  noTell : rule.body.tell = []
  positive : Scope.Positive rule
  madeScoped : varsIn rule.body.produce ⊆ varsIn rule.body.read
  checksScoped : varsIn (rule.body.checks.flatMap checkTerms) ⊆ varsIn rule.body.read

variable {P : Program (Terms (Term signature))}
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

structure GroundMatch (P : Program (Terms (Term signature))) where
  rule : Rule (Terms (Term signature))
  member : rule ∈ P
  propagates : Propagates rule
  assignment : Subst signature
  groundReads : ∀ term ∈ rule.body.read, (assignment.applyTerm term).isGround
  checked : ∀ left right, Check.equal left right ∈ rule.body.checks →
    assignment.applyTerm left = assignment.applyTerm right

def consequence (match_ : GroundMatch P) : SetStoreClosure.Instance (Term signature) :=
  ⟨(match_.rule.body.read.map match_.assignment.applyTerm).toFinset,
    (match_.rule.body.produce.map match_.assignment.applyTerm).toFinset⟩

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem ground_read_variables (match_ : GroundMatch P) :
    ∀ v ∈ varsIn match_.rule.body.read, (match_.assignment v).isGround := by
  intro v member
  obtain ⟨term, inside, mentions⟩ := (mem_variables _ _).mp member
  exact (apply_ground_iff _ _).mp (match_.groundReads term inside) v mentions

theorem instance_ground (match_ : GroundMatch P) :
    ∀ value ∈ (consequence match_).made, value.isGround := by
  intro value member
  obtain ⟨term, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  apply (apply_ground_iff _ _).mpr
  intro v mentions
  exact ground_read_variables match_ v
    (match_.propagates.madeScoped ((mem_variables _ _).mpr ⟨term, inside, mentions⟩))

def GroundRows (rows : Finset (Term signature)) : Prop := ∀ term ∈ rows, term.isGround

theorem step_preserves_ground {seed after : Finset (Term signature)}
    (ground : GroundRows seed) (step : SetStoreClosure.Step (consequence (P := P)) seed after) :
    GroundRows after := by
  obtain ⟨match_, _, rfl, _⟩ := step
  intro term member
  simp only [SetStore.update, Finset.sdiff_empty, Finset.image_id, Finset.mem_union] at member
  exact member.elim (ground term) (instance_ground match_ term)

theorem reachable_ground {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) seed after) :
    GroundRows after := by
  induction run with
  | refl => exact ground
  | tail _ step ih => exact step_preserves_ground ih step

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem matches_determine_scoped_terms (match_ : GroundMatch P) (other : Subst signature)
    (matched : ∀ term ∈ match_.rule.body.read,
      other.applyTerm term = match_.assignment.applyTerm term)
    (terms : List (Term signature)) (bounded : varsIn terms ⊆ varsIn match_.rule.body.read) :
    terms.map other.applyTerm = terms.map match_.assignment.applyTerm := by
  apply List.map_congr_left
  intro term inside
  apply apply_eq_of_agree
  intro v mentions
  obtain ⟨read, inRead, readMentions⟩ := (mem_variables _ _).mp
    (bounded ((mem_variables _ _).mpr ⟨term, inside, mentions⟩))
  exact agree_of_apply_eq _ _ read (matched read inRead) v readMentions

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem checks_of_matches (match_ : GroundMatch P) (other : Subst signature)
    (matched : ∀ term ∈ match_.rule.body.read,
      other.applyTerm term = match_.assignment.applyTerm term)
    (left right : Term signature) (check : Check.equal left right ∈ match_.rule.body.checks) :
    other.applyTerm left = other.applyTerm right := by
  have agree : ∀ term ∈ [left, right], other.applyTerm term = match_.assignment.applyTerm term := by
    intro term inside
    apply apply_eq_of_agree
    intro v mentions
    have inCheck : term ∈ match_.rule.body.checks.flatMap checkTerms :=
      List.mem_flatMap.mpr ⟨Check.equal left right, check, inside⟩
    obtain ⟨read, inRead, readMentions⟩ := (mem_variables _ _).mp
      (match_.propagates.checksScoped ((mem_variables _ _).mpr ⟨term, inCheck, mentions⟩))
    exact agree_of_apply_eq _ _ read (matched read inRead) v readMentions
  exact (agree left List.mem_cons_self).trans
    ((match_.checked left right check).trans (agree right (by simp)).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
