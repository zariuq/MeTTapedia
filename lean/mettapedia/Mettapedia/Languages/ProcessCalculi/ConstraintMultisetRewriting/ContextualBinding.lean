import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies

/-!
# Principal contextual binding at the declared parameter interface

An equation `F[parameters] = body` has the usual principal binding when
`body` does not contain `F`. The body is intrinsically scoped in precisely
`F`'s declared parameter context. It may contain other unresolved
metavariables and arbitrary application spines.

The executable operation checks occurrence and returns that binding.
Refusal of this particular operation is not a proof of inconsistency:
reflexive equations also contain their own metavariable. General spines,
decomposition and flex-flex solving are separate solver cases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding

open Mettapedia.OSLF.Binding hiding instantiate
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]
  {declaration : V → MetaArity S}

def answer (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2) :
    Assignment declaration declaration :=
  Function.update (generator declaration) identity body

theorem answer_same (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2) :
    answer identity body identity = body := by simp [answer]

theorem answer_other (identity other : V) (different : other ≠ identity)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2) :
    answer identity body other = generator declaration other := by simp [answer, different]

theorem instantiate_answer_of_absent (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S declaration) Γ sort)
    (absent : identity ∉ support term) :
    instantiate (answer identity body) term = term := by
  calc
    instantiate (answer identity body) term = instantiate (generator declaration) term := by
      apply instantiate_congr
      intro other member
      exact answer_other identity other (fun same => absent (same ▸ member)) body
    _ = term := instantiate_identity term

/-- Every solution of the binding equation is unchanged by first applying
the proposed binding and then the solution. This is a componentwise law at
all declared arities, not only an observation at the equation's sort. -/
theorem candidate_factors {Next : Type} {next : Next → MetaArity S} (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (candidate : Assignment declaration next)
    (binding : candidate identity = instantiate candidate body) :
    candidate = fun other => instantiate candidate (answer identity body other) := by
  funext other
  by_cases same : other = identity
  · subst other
    rw [answer_same]
    exact binding
  · rw [answer_other identity other same body, instantiate_generator]

theorem principal (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (absent : identity ∉ support body) :
    (ContextualFamilies.action declaration (declaration identity).1 (declaration identity).2).Principal
      [(generator declaration identity, body)] (answer identity body) := by
  constructor
  · intro equation member
    have same : equation = (generator declaration identity, body) := by simpa using member
    subst equation
    change instantiate (answer identity body) (generator declaration identity) =
      instantiate (answer identity body) body
    rw [instantiate_generator, answer_same, instantiate_answer_of_absent identity body body absent]
  · intro candidate solved
    have binding := solved (generator declaration identity, body) (by simp)
    change instantiate candidate (generator declaration identity) = instantiate candidate body at binding
    rw [instantiate_generator] at binding
    refine ⟨candidate, ?_⟩
    intro term
    exact congrArg (fun assignment => instantiate assignment term)
      (candidate_factors identity body candidate binding)

theorem answer_idempotent (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (absent : identity ∉ support body) :
    (fun other => instantiate (answer identity body) (answer identity body other)) =
      answer identity body := by
  funext other
  by_cases same : other = identity
  · subst other
    rw [answer_same, instantiate_answer_of_absent identity body body absent]
  · rw [answer_other identity other same body, instantiate_generator]
    exact answer_other identity other same body

/-- This operation handles a binding equation at its declared formal
spine. An occurrence failure leaves the equation for other solver cases. -/
def solve? (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2) :
    Option (Assignment declaration declaration) :=
  if identity ∈ support body then none else some (answer identity body)

theorem solve_principal {identity : V}
    {body : Term (signature S declaration) (declaration identity).1 (declaration identity).2}
    {assignment : Assignment declaration declaration}
    (success : solve? identity body = some assignment) :
    (ContextualFamilies.action declaration (declaration identity).1 (declaration identity).2).Principal
      [(generator declaration identity, body)] assignment := by
  unfold solve? at success
  split at success
  · cases success
  · have same := Option.some.inj success
    subst assignment
    exact principal identity body (by assumption)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding
