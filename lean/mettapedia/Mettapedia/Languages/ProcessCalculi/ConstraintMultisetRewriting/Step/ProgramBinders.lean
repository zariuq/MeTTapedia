import Mettapedia.OSLF.Syntax.ContextualRigidReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Pattern equations under binders: the reference semantics

Equations `(= lhs rhs)` over the intrinsically scoped terms of any binding signature.
- **Constants:** the ambient context `Γ` holds the program's rigid heads (`f`, `g`, ...), as a
  signature is a context of constants.
- **Holes:** each hole `$M` has a parameter context and a sort. Its solution may mention exactly
  those object variables, so a hole cannot capture a bound variable it does not list. An occurrence
  `$M x` is the hole applied to object variables, `M[x, …]`; it is a Miller pattern when they are
  distinct.
- **Answers:** a ground call matches an equation when some ground solution of the holes makes the
  left-hand side equal to the call. The answer is that solution applied to the right-hand side. Each
  equation that matches gives one branch.

Equality of terms is syntactic (α is built in by intrinsic scoping). Instantiating a hole performs
the substitution of its arguments, so the matching problem `lhs ≐ call` is exactly
higher-order pattern unification with a ground side.

`principal_answers`: for a Miller-pattern left-hand side, the actual worklist solves the problem
completely, and the answers of the branch are exactly the ground instances of one open answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature}

/-- The empty declaration family: terms over it have no holes. -/
abbrev ground (S : Signature) : Empty → MetaArity S := fun impossible => nomatch impossible

/-! ## Terms without holes -/

mutual
def decode : {Γ : Ctx S} → {sort : S.Srt} → Term (signature S (ground S)) Γ sort → Term S Γ sort
  | _, _, .var position => .var position
  | _, _, .op (.inl operator) arguments => .op operator (decodeArgs arguments)
  | _, _, .op (.inr (.mk impossible)) _ => nomatch impossible

def decodeArgs : {arities : List (MetaArity S)} → {Γ : Ctx S} →
    Args (signature S (ground S)) arities Γ → Args S arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (decode head) (decodeArgs tail)
end

mutual
theorem include_decode : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S (ground S)) Γ sort),
    Rigid.includeTerm (ground S) (decode term) = term
  | _, _, .var _ => rfl
  | _, _, .op (.inl operator) arguments => by
      change Term.op (S := signature S (ground S)) (Sum.inl operator)
        (Rigid.includeArgs (ground S) (decodeArgs arguments)) = _
      rw [includeArgs_decodeArgs arguments]
  | _, _, .op (.inr (.mk impossible)) _ => nomatch impossible

theorem includeArgs_decodeArgs : ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S (ground S)) arities Γ),
      Rigid.includeArgs (ground S) (decodeArgs arguments) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change Args.cons (Rigid.includeTerm (ground S) (decode head))
        (Rigid.includeArgs (ground S) (decodeArgs tail)) = _
      rw [include_decode head, includeArgs_decodeArgs tail]
end

/-- A term without holes is the inclusion of a source term. -/
theorem holeFree {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S (ground S)) Γ sort) :
    ∃ source : Term S Γ sort, term = Rigid.includeTerm (ground S) source :=
  ⟨decode term, (include_decode term).symm⟩

/-- The unique assignment out of the empty family. -/
def fromGround {W : Type} (target : W → MetaArity S) : Assignment (ground S) target :=
  fun impossible => nomatch impossible

/-- A closed term of every sort, to fill holes that a reading does not constrain. -/
class ClosedTerms (S : Signature) where
  closed : (sort : S.Srt) → Term S [] sort

/-- A closed term of a sort in any context. -/
def closedAt [ClosedTerms S] (Δ : Ctx S) (sort : S.Srt) : Term S Δ sort :=
  rename (Γ := []) (fun _ impossible => nomatch impossible) (ClosedTerms.closed sort)

/-- Fill every hole of a frame with a closed term. -/
def close [ClosedTerms S] {W : Type} (frame : W → MetaArity S) : Assignment frame (ground S) :=
  fun name => Rigid.includeTerm (ground S) (closedAt (frame name).1 (frame name).2)

/-! ## Equations -/

/-- A pattern equation `(= lhs rhs)` of sort `sort` in the ambient context `Γ` of constants. -/
structure Equation (S : Signature) (Γ : Ctx S) (sort : S.Srt) where
  Holes : Type
  holesEq : DecidableEq Holes
  arity : Holes → MetaArity S
  lhs : Term (signature S arity) Γ sort
  rhs : Term (signature S arity) Γ sort

variable {Γ : Ctx S} {sort : S.Srt}

instance (e : Equation S Γ sort) : DecidableEq e.Holes := e.holesEq

/-- A ground solution of the holes: each hole gets a source term over its parameters. -/
abbrev Equation.Ground (e : Equation S Γ sort) := (hole : e.Holes) → Term S (e.arity hole).1 (e.arity hole).2

/-- A ground solution as a contextual assignment into any frame. -/
def Equation.assign (e : Equation S Γ sort) (θ : e.Ground) {W : Type} (target : W → MetaArity S) :
    Assignment e.arity target := fun hole => Rigid.includeTerm target (θ hole)

theorem Equation.assign_ground (e : Equation S Γ sort) (θ : e.Ground) {W : Type} (target : W → MetaArity S) :
    Assignment.compose (fromGround target) (e.assign θ (ground S)) = e.assign θ target := by
  funext hole
  exact Rigid.instantiate_include (fromGround target) (θ hole)

/-- Every assignment into the empty family is a ground solution. -/
theorem Equation.ground_assignment (e : Equation S Γ sort) (change : Assignment e.arity (ground S)) :
    e.assign (fun hole => decode (change hole)) (ground S) = change := by
  funext hole
  exact include_decode (change hole)

/-- Reading a term through a ground solution does not depend on the frame it is read in. -/
theorem Equation.reads_in_frame (e : Equation S Γ sort) (θ : e.Ground) {Δ : Ctx S} {result : S.Srt}
    (term : Term (signature S e.arity) Δ result) (value : Term S Δ result)
    {W : Type} (target : W → MetaArity S) :
    instantiate (e.assign θ (ground S)) term = Rigid.includeTerm (ground S) value ↔
      instantiate (e.assign θ target) term = Rigid.includeTerm target value := by
  rw [← e.assign_ground θ target, Assignment.instantiate_compose]
  constructor
  · intro same
    rw [same, Rigid.instantiate_include]
  · intro same
    obtain ⟨source, read⟩ := holeFree (instantiate (e.assign θ (ground S)) term)
    rw [read, Rigid.instantiate_include] at same
    rw [read, Rigid.include_injective target source value same]

/-! ## The reference semantics -/

/-- `θ` solves `lhs ≐ call`: higher-order pattern unification against a ground call. -/
def Matches (e : Equation S Γ sort) (call : Term S Γ sort) (θ : e.Ground) : Prop :=
  instantiate (e.assign θ (ground S)) e.lhs = Rigid.includeTerm (ground S) call

/-- An answer of the branch of `e` at `call`. -/
def Answers (e : Equation S Γ sort) (call answer : Term S Γ sort) : Prop :=
  ∃ θ : e.Ground, Matches e call θ ∧ instantiate (e.assign θ (ground S)) e.rhs = Rigid.includeTerm (ground S) answer

/-- One rewrite of a call by a program: some equation matches, and the call becomes its answer. -/
def Rewrites {ι : Type} (program : ι → Equation S Γ sort) (call answer : Term S Γ sort) : Prop :=
  ∃ index, Answers (program index) call answer

/-! ## Principal answers for Miller patterns -/

/-- The unification problem of one equation against a call. -/
def problem (e : Equation S Γ sort) (call : Term S Γ sort) : ContextualResidual.Problem e.arity :=
  ContextualResidual.observeProblem [(e.lhs, Rigid.includeTerm e.arity call)]

theorem problem_pattern (e : Equation S Γ sort) (call : Term S Γ sort)
    (patterned : ContextualPatternFragment.Pattern S e.arity e.lhs) :
    ContextualPatternFragment.ProblemPattern (problem e call) := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  exact ⟨patterned, ContextualPatternFragment.rigid_inclusion_pattern e.arity call⟩

theorem models_problem (e : Equation S Γ sort) (call : Term S Γ sort) {W : Type} {target : W → MetaArity S}
    (change : Assignment e.arity target) :
    ContextualResidual.Models change (problem e call) ↔
      instantiate change e.lhs = Rigid.includeTerm target call := by
  rw [problem, ContextualResidual.models_observeProblem]
  constructor
  · intro solved
    have same : instantiate change e.lhs = instantiate change (Rigid.includeTerm e.arity call) :=
      solved _ (List.mem_singleton_self _)
    rwa [Rigid.instantiate_include] at same
  · intro same equation member
    have only := List.mem_singleton.mp member
    subst equation
    change instantiate change e.lhs = instantiate change (Rigid.includeTerm e.arity call)
    rw [Rigid.instantiate_include]
    exact same

theorem matches_iff_models (e : Equation S Γ sort) (call : Term S Γ sort) (θ : e.Ground) :
    Matches e call θ ↔ ContextualResidual.Models (e.assign θ (ground S)) (problem e call) :=
  (models_problem e call _).symm

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Principal answers.** For a Miller-pattern left-hand side that matches the call, the actual
worklist returns a completed update. Its answer applied to the right-hand side is principal: the
answers of the branch are exactly its ground instances. -/
theorem principal_answers (e : Equation S Γ sort)
    (patterned : ContextualPatternFragment.Pattern S e.arity e.lhs)
    (call : Term S Γ sort) (θ : e.Ground) (matched : Matches e call θ) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (problem e call)),
      ContextualFrameWorklist.run fuel e.arity (problem e call) = .residual update ∧
        update.remaining = [] ∧
        ∀ answer, Answers e call answer ↔
          ∃ factor : Assignment update.declaration (ground S),
            instantiate factor (instantiate update.answer e.rhs) = Rigid.includeTerm (ground S) answer := by
  obtain ⟨fuel, update, computed, empty, solved, factors⟩ :=
    ContextualPatternCompleteness.solves_principally_of_model (ground S) (problem e call)
      (problem_pattern e call patterned) (e.assign θ (ground S)) ((matches_iff_models e call θ).mp matched)
  refine ⟨fuel, update, computed, empty, fun answer => ⟨?_, ?_⟩⟩
  · rintro ⟨other, otherMatched, read⟩
    obtain ⟨factor, components⟩ := factors (ground S) (e.assign other (ground S))
      ((matches_iff_models e call other).mp otherMatched)
    exact ⟨factor, (ContextualFrameUnifier.factor_terms _ _ factor components e.rhs).symm.trans read⟩
  · rintro ⟨factor, read⟩
    let solution : e.Ground := fun hole => decode (instantiate factor (update.answer hole))
    have restored : e.assign solution (ground S) = Assignment.compose factor update.answer :=
      e.ground_assignment (Assignment.compose factor update.answer)
    refine ⟨solution, ?_, ?_⟩
    · apply (matches_iff_models e call solution).mpr
      rw [restored]
      exact ContextualResidual.models_compose solved factor
    · rw [restored, Assignment.instantiate_compose]
      exact read

/-- When no ground solution exists, the actual worklist refutes a Miller-pattern problem. -/
theorem refuted_of_no_match [ClosedTerms S] (e : Equation S Γ sort)
    (patterned : ContextualPatternFragment.Pattern S e.arity e.lhs)
    (call : Term S Γ sort) (unmatched : ∀ θ, ¬ Matches e call θ) :
    ∃ fuel proof, ContextualFrameWorklist.run fuel e.arity (problem e call) = .refuted proof := by
  apply ContextualPatternTermination.refutes_of_no_model (problem e call) (problem_pattern e call patterned)
  intro Next next candidate solved
  apply unmatched (fun hole => decode (instantiate (close next) (candidate hole)))
  apply (matches_iff_models e call _).mpr
  rw [e.ground_assignment (Assignment.compose (close next) candidate)]
  exact ContextualResidual.models_compose solved (close next)

#print axioms holeFree
#print axioms Equation.reads_in_frame
#print axioms matches_iff_models
#print axioms principal_answers
#print axioms refuted_of_no_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
