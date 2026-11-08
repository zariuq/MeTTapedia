import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersCached
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# Range-restricted Miller-pattern equations are determinate

Matching a Miller pattern fixes every hole it contains: at a hole occurrence the instance is the
hole's image renamed along distinct variables, and an injective renaming is injective on terms.
- `rename_inj`: an injective renaming is injective on terms.
- `pattern_match_unique`: two solutions giving one instance of a Miller pattern agree on its holes.
- `determinate_of_pattern`: an equation whose left-hand side is a Miller pattern and whose
  right-hand-side holes occur on the left is determinate.
- `miller_with_solvers`: for every program of such equations, source runs are exactly the runs of
  the step with an actual completed incremental solver result, hence a principal answer, at every
  firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern PatternArgs)

mutual
/-- An injective renaming is injective on terms. -/
theorem rename_inj {T : Signature} : ∀ {Γ Δ : Ctx T} {sort : T.Srt} (ρ : Ren T Γ Δ),
    (∀ sort, Function.Injective (ρ sort)) → ∀ (first second : Term T Γ sort),
      rename ρ first = rename ρ second → first = second
  | _, _, _, _, injective, .var first, .var second, same =>
      congrArg Term.var (injective _ (Term.var.inj same))
  | _, _, _, _, _, .var _, .op _ _, same => by cases same
  | _, _, _, _, _, .op _ _, .var _, same => by cases same
  | _, _, _, ρ, injective, .op operator arguments, .op operator' arguments', same => by
      obtain ⟨sameOperator, sameArguments⟩ := Term.op.inj same
      subst sameOperator
      rw [renameArgs_inj ρ injective arguments arguments' (eq_of_heq sameArguments)]

theorem renameArgs_inj {T : Signature} : ∀ {arities : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T}
    (ρ : Ren T Γ Δ), (∀ sort, Function.Injective (ρ sort)) → ∀ (first second : Args T arities Γ),
      renameArgs ρ first = renameArgs ρ second → first = second
  | _, _, _, _, _, .nil, .nil, _ => rfl
  | _, _, _, ρ, injective, .cons (bs := binders) head tail, .cons head' tail', same => by
      obtain ⟨sameHead, sameTail⟩ := Args.cons.inj same
      rw [rename_inj (liftRen ρ binders) (RenamingSlots.lift_injective ρ injective binders) head head' sameHead,
        renameArgs_inj ρ injective tail tail' sameTail]
end

variable {S : Signature} {V W : Type} {source : V → MetaArity S}

/-- The arguments of a Miller occurrence are variables, so they contain no hole. -/
theorem spine_support {Γ : Ctx S} :
    ∀ (parameters : Ctx S) (arguments : Args (signature S source) (parameters.map fun sort => ([], sort)) Γ)
      (ρ : Ren S parameters Γ), (∀ sort index, argsToSub arguments sort index = .var (ρ sort index)) →
        supportArgs arguments = []
  | [], .nil, _, _ => rfl
  | _ :: rest, .cons head tail, ρ, spine => by
      have headVar : head = .var (ρ _ .zero) := spine _ .zero
      have restEmpty := spine_support rest tail (fun sort index => ρ sort (.succ index))
        (fun sort index => spine sort (.succ index))
      change support head ++ supportArgs tail = []
      rw [headVar, restEmpty]
      rfl

/-- **Miller matching is unique**: two solutions giving one instance of a Miller pattern agree on
every hole of the pattern. -/
theorem pattern_match_unique {target : W → MetaArity S} (first second : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) (patterned : Pattern S source term)
    (same : instantiate first term = instantiate second term) :
    ∀ hole ∈ support term, first hole = second hole := by
  refine Pattern.rec
    (motive_1 := fun value _ => instantiate first value = instantiate second value →
      ∀ hole ∈ support value, first hole = second hole)
    (motive_2 := fun values _ => instantiateArgs first values = instantiateArgs second values →
      ∀ hole ∈ supportArgs values, first hole = second hole)
    ?_ ?_ ?_ ?_ ?_ patterned same
  · intro context result position _ hole member
    cases member
  · intro context result operator arguments fields checked equal hole member
    have parts := eq_of_heq (Term.op.inj equal).2
    exact checked parts hole member
  · intro context identity arguments spineMap spine distinct equal hole member
    rw [ContextualPatternFragment.instantiate_spine first identity arguments spineMap spine,
      ContextualPatternFragment.instantiate_spine second identity arguments spineMap spine] at equal
    have image := rename_inj (T := signature S target) spineMap distinct _ _ equal
    change hole ∈ identity :: supportArgs arguments at member
    rw [spine_support _ arguments spineMap spine] at member
    rw [List.mem_singleton.mp member]
    exact image
  · intro context _ hole member
    cases member
  · intro arities context binders result head tail _ _ checkedHead checkedTail equal hole member
    obtain ⟨sameHead, sameTail⟩ := Args.cons.inj equal
    rcases List.mem_append.mp member with inHead | inTail
    · exact checkedHead sameHead hole inHead
    · exact checkedTail sameTail hole inTail

variable {Γ : Ctx S} {sort : S.Srt}

/-- Every hole of the right-hand side occurs on the left. -/
def RangeRestricted (e : Equation S Γ sort) : Prop := ∀ hole ∈ support e.rhs, hole ∈ support e.lhs

/-- **Range-restricted Miller-pattern equations are determinate.** -/
theorem determinate_of_pattern (e : Equation S Γ sort) (patterned : Pattern S e.arity e.lhs)
    (restricted : RangeRestricted e) : Determinate e := by
  intro W target first second call firstMatch secondMatch
  have agree := pattern_match_unique first second e.lhs patterned (firstMatch.trans secondMatch.symm)
  exact instantiate_congr first second e.rhs (fun hole member => agree hole (restricted hole member))

variable {ι : Type} [DecidableEq ι] [ClosedTerms S] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Principal answers along every run.** For a program of range-restricted Miller-pattern
equations, source runs are exactly the readings of runs of the step with an actual completed
incremental solver result at every firing. -/
theorem miller_with_solvers {program : ι → Equation S Γ sort}
    (patterns : ∀ index, Pattern S (program index).arity (program index).lhs)
    (restricted : ∀ index, RangeRestricted (program index)) (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites program) call answer ↔
      ∃ (state : State program) (cache : Cache state), SolverPath call state cache ∧ Reads program state answer :=
  execution_with_solvers_iff (fun index => determinate_of_pattern _ (patterns index) (restricted index))
    patterns call answer

#print axioms rename_inj
#print axioms spine_support
#print axioms pattern_match_unique
#print axioms determinate_of_pattern
#print axioms miller_with_solvers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
