import Mettapedia.TypeTheory.ContextualBasedIdentityScope

/-!
# Based identity elimination retaining a typed motive function

The applied family need not determine a submitted function in an intensional
presentation. This input retains an actual typed function as well as the
family and reflexivity method. Raw input data assert neither that the function
denotes that family nor that elimination exists. Those obligations belong to
the interpretation and its admitted domain.

Reindexing transports every retained component. Its method cast needs only
the section square, not a total elimination operation. The substitution law
quantifies over every method equal to the transported one, independently of
the canonical cast used to construct a reindexed request.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualRetainedIdentityOperations

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations (IdentityFormationOperations)
open ContextualBasedIdentityOperations (basedContext Reindexing)

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}
variable {identity : IdentityFormationOperations C}
variable {reflSection : ContextualBasedIdentityScope.Section identity}

structure Input (identity : IdentityFormationOperations C)
    (reflSection : ContextualBasedIdentityScope.Section identity) where
  body : ContextualBasedIdentityScope.Input identity reflSection
  functionType : C.Ty body.context
  function : C.Tm body.context functionType

abbrev Input.Output (input : Input identity reflSection) := input.body.Output

theorem Input.ext {first second : Input identity reflSection}
    (bodies : first.body = second.body)
    (types : HEq first.functionType second.functionType)
    (functions : HEq first.function second.function) : first = second := by
  cases first
  cases second
  cases bodies
  cases eq_of_heq types
  cases eq_of_heq functions
  rfl

def SectionSquare (reflSection : ContextualBasedIdentityScope.Section identity)
    (reindexing : Reindexing identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type),
    C.compS (reindexing.map substitution left)
        (reflSection (C.tmSub left substitution)) =
      C.compS (reflSection left) substitution

/-- A supplied method lives in the actual reindexed reflexivity fibre.
No equality to the original method is hidden in these raw data. -/
def Input.reindexWithBase (input : Input identity reflSection)
    (reindexing : Reindexing identity) {source : C.Ctx}
    (substitution : C.Sub source input.body.context)
    (base : C.Tm source
      (C.tySub (C.tySub input.body.motive (reindexing.map substitution input.body.left))
        (reflSection (C.tmSub input.body.left substitution)))) : Input identity reflSection where
  body := {
    context := source
    type := C.tySub input.body.type substitution
    left := C.tmSub input.body.left substitution
    motive := C.tySub input.body.motive (reindexing.map substitution input.body.left)
    base := base }
  functionType := C.tySub input.functionType substitution
  function := C.tmSub input.function substitution

def Input.reindexedBase (input : Input identity reflSection)
    (reindexing : Reindexing identity) (square : SectionSquare reflSection reindexing)
    {source : C.Ctx} (substitution : C.Sub source input.body.context) :
    C.Tm source
      (C.tySub (C.tySub input.body.motive (reindexing.map substitution input.body.left))
        (reflSection (C.tmSub input.body.left substitution))) :=
  cast (by rw [← C.tySub_comp, ← square substitution input.body.left, C.tySub_comp])
    (C.tmSub input.body.base substitution)

theorem Input.reindexedBase_heq (input : Input identity reflSection)
    (reindexing : Reindexing identity) (square : SectionSquare reflSection reindexing)
    {source : C.Ctx} (substitution : C.Sub source input.body.context) :
    HEq (input.reindexedBase reindexing square substitution)
      (C.tmSub input.body.base substitution) := cast_heq _ _

def Input.reindex (input : Input identity reflSection)
    (reindexing : Reindexing identity) (square : SectionSquare reflSection reindexing)
    {source : C.Ctx} (substitution : C.Sub source input.body.context) : Input identity reflSection :=
  input.reindexWithBase reindexing substitution
    (input.reindexedBase reindexing square substitution)

/-- Any method satisfying the heterogeneous transport premise is the
canonical method in its actual target fibre. -/
theorem Input.reindexWithBase_eq (input : Input identity reflSection)
    (reindexing : Reindexing identity) (square : SectionSquare reflSection reindexing)
    {source : C.Ctx} (substitution : C.Sub source input.body.context)
    (base : C.Tm source
      (C.tySub (C.tySub input.body.motive (reindexing.map substitution input.body.left))
        (reflSection (C.tmSub input.body.left substitution))))
    (same : HEq (C.tmSub input.body.base substitution) base) :
    input.reindexWithBase reindexing substitution base =
      input.reindex reindexing square substitution := by
  have equal := eq_of_heq ((input.reindexedBase_heq reindexing square substitution).trans same)
  cases equal
  rfl

/-- Scope membership supplies no result. The operation must construct a
term in each independently specified admitted output fibre. -/
abbrev Run (scope : Input identity reflSection → Prop) :=
  (input : Input identity reflSection) → scope input → input.Output

def Beta {scope : Input identity reflSection → Prop} (run : Run scope) : Prop :=
  ∀ (input : Input identity reflSection) (admitted : scope input),
    C.tmSub (run input admitted) (reflSection input.body.left) = input.body.base

/-- Closure and result preservation are demanded for every transported
method representative, not only the particular cast in `Input.reindex`. -/
def Substitution {scope : Input identity reflSection → Prop} (run : Run scope)
    (reindexing : Reindexing identity) : Prop :=
  ∀ (input : Input identity reflSection) (admitted : scope input)
    (source : C.Ctx) (substitution : C.Sub source input.body.context)
    (base : C.Tm source
      (C.tySub (C.tySub input.body.motive (reindexing.map substitution input.body.left))
        (reflSection (C.tmSub input.body.left substitution)))),
    HEq (C.tmSub input.body.base substitution) base →
      ∃ reindexedAdmitted : scope (input.reindexWithBase reindexing substitution base),
        C.tmSub (run input admitted) (reindexing.map substitution input.body.left) =
          run (input.reindexWithBase reindexing substitution base) reindexedAdmitted

theorem beta_substitution {scope : Input identity reflSection → Prop} (run : Run scope)
    (reindexing : Reindexing identity) (square : SectionSquare reflSection reindexing)
    (stable : Substitution run reindexing) (beta : Beta run)
    (input : Input identity reflSection) (admitted : scope input)
    {source : C.Ctx} (substitution : C.Sub source input.body.context) :
    HEq (C.tmSub
      (C.tmSub (run input admitted) (reindexing.map substitution input.body.left))
        (reflSection (C.tmSub input.body.left substitution)))
      (C.tmSub input.body.base substitution) := by
  obtain ⟨reindexedAdmitted, same⟩ := stable input admitted source substitution
    (input.reindexedBase reindexing square substitution)
    (input.reindexedBase_heq reindexing square substitution).symm
  rw [same]
  exact (heq_of_eq (beta _ reindexedAdmitted)).trans
    (input.reindexedBase_heq reindexing square substitution)

/-- A total family-only operation can be used on any retained scope by
forgetting the additional function. No converse or scope closure is asserted. -/
def restrict (elimination : ContextualBasedIdentityScope.FixedSection identity reflSection)
    (scope : Input identity reflSection → Prop) : Run scope :=
  fun input _ => elimination.run input.body

theorem restrict_beta (elimination : ContextualBasedIdentityScope.FixedSection identity reflSection)
    (scope : Input identity reflSection → Prop)
    (beta : ContextualBasedIdentityOperations.Beta elimination.val) :
    Beta (restrict elimination scope) := by
  rcases elimination with ⟨⟨actualSection, j⟩, same⟩
  cases same
  intro input _
  exact beta input.body.left input.body.motive input.body.base

#print axioms Input.reindexedBase_heq
#print axioms Input.reindexWithBase_eq
#print axioms beta_substitution
#print axioms restrict_beta

end Mettapedia.TypeTheory.ContextualRetainedIdentityOperations
