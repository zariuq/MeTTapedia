import Mettapedia.TypeTheory.ContextualBasedIdentityOperations

/-!
# Scoped based identity elimination and total extension

A supplied family of typed based-J inputs need not cover every motive of
the ambient CwF. This file isolates the extra output-fibre obligation for
extending a scoped operation to the existing total `Elimination` record.
The extension criterion concerns raw operation data, not beta, substitution,
native interpretation, or a choice of identity theory.

The separating instance uses the existing indiscrete identity on the full
set-family CwF. Motives pulled back from the original context have a genuine,
substitution-stable elimination operation. An endpoint-sensitive motive with
an empty off-reflexivity fibre prevents any boundary-correct total extension.
The restricted instance is a control, not a proposed scope for native J.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualBasedIdentityScope

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations (IdentityFormationOperations)
open ContextualBasedIdentityOperations

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

abbrev Section (identity : IdentityFormationOperations C) :=
  {context : C.Ctx} → {type : C.Ty context} →
    (left : C.Tm context type) → C.Sub context (basedContext identity left)

/-- An actual typed motive and reflexivity method. The scope is supplied
separately, so packaging an input asserts no elimination or coverage law. -/
structure Input (identity : IdentityFormationOperations C) (reflSection : Section identity) where
  context : C.Ctx
  type : C.Ty context
  left : C.Tm context type
  motive : C.Ty (basedContext identity left)
  base : C.Tm context (C.tySub motive (reflSection left))

def Input.Output {identity : IdentityFormationOperations C} {reflSection : Section identity}
    (input : Input identity reflSection) :=
  C.Tm (basedContext identity input.left) input.motive

/-- A fibre of the existing total operation record, not an alternative
operation signature. Fixing its section keeps all method types explicit. -/
abbrev FixedSection (identity : IdentityFormationOperations C) (reflSection : Section identity) :=
  {elimination : Elimination identity // @elimination.reflSection = @reflSection}

def FixedSection.run {identity : IdentityFormationOperations C} {reflSection : Section identity}
    (elimination : FixedSection identity reflSection) (input : Input identity reflSection) :
    input.Output := by
  rcases elimination with ⟨⟨actualSection, j⟩, same⟩
  cases same
  exact j input.left input.motive input.base

/-- A sectionwise output function constructs the old total record directly. -/
def fromOutputs {identity : IdentityFormationOperations C} {reflSection : Section identity}
    (outputs : (input : Input identity reflSection) → input.Output) : FixedSection identity reflSection :=
  ⟨{ reflSection := reflSection
     j := fun {context type} left motive base =>
       outputs ⟨context, type, left, motive, base⟩ }, rfl⟩

@[simp] theorem fromOutputs_run {identity : IdentityFormationOperations C}
    {reflSection : Section identity} (outputs : (input : Input identity reflSection) → input.Output)
    (input : Input identity reflSection) :
    (fromOutputs outputs).run input = outputs input := rfl

/-- With an actual scope decision and supplied outputs on its complement,
the extension is constructive and leaves every scoped result unchanged. -/
def extend {identity : IdentityFormationOperations C} {reflSection : Section identity}
    (scope : Input identity reflSection → Prop) [DecidablePred scope]
    (scopedOutput : (input : Input identity reflSection) → scope input → input.Output)
    (outside : (input : Input identity reflSection) → ¬ scope input → input.Output) :
    FixedSection identity reflSection :=
  fromOutputs fun input => if admitted : scope input then scopedOutput input admitted
    else outside input admitted

theorem extend_agrees {identity : IdentityFormationOperations C} {reflSection : Section identity}
    (scope : Input identity reflSection → Prop) [DecidablePred scope]
    (scopedOutput : (input : Input identity reflSection) → scope input → input.Output)
    (outside : (input : Input identity reflSection) → ¬ scope input → input.Output)
    (input : Input identity reflSection) (admitted : scope input) :
    (extend scope scopedOutput outside).run input = scopedOutput input admitted := by
  simp [extend, admitted]

/-- Total raw data require outputs even for motives never consumed by a
scoped law. This equivalence does not construct beta or substitution laws. -/
theorem total_extension_iff {identity : IdentityFormationOperations C}
    {reflSection : Section identity} (scope : Input identity reflSection → Prop)
    (scopedOutput : (input : Input identity reflSection) → scope input → input.Output) :
    (∃ elimination : FixedSection identity reflSection,
      ∀ (input : Input identity reflSection) (admitted : scope input),
        elimination.run input = scopedOutput input admitted) ↔
    ∀ input : Input identity reflSection, ¬ scope input → Nonempty input.Output := by
  constructor
  · rintro ⟨elimination, _⟩ input _
    exact ⟨elimination.run input⟩
  · intro outside
    classical
    refine ⟨extend scope scopedOutput (fun input excluded => Classical.choice (outside input excluded)), ?_⟩
    intro input admitted
    exact extend_agrees scope scopedOutput _ input admitted

/-- If even one off-scope output fibre is empty, agreement with all local
results cannot turn the scoped operation into the old total record. -/
theorem no_total_extension_of_empty_output {identity : IdentityFormationOperations C}
    {reflSection : Section identity} (scope : Input identity reflSection → Prop)
    (scopedOutput : (input : Input identity reflSection) → scope input → input.Output)
    (input : Input identity reflSection) (empty : ¬ Nonempty input.Output) :
    ¬ ∃ elimination : FixedSection identity reflSection,
      ∀ (input : Input identity reflSection) (admitted : scope input),
        elimination.run input = scopedOutput input admitted := by
  rintro ⟨elimination, _⟩
  exact empty ⟨elimination.run input⟩

namespace EqualityFamilies

/-- The existing full, arbitrary-motive set-family operation satisfies the
extra raw-fibre requirement for every externally supplied restriction. -/
theorem complement_inhabited
    (scope : Input ContextualTypeOperations.Families.formation.{w}
      ContextualBasedIdentityOperations.Families.elimination.reflSection → Prop)
    (input : Input ContextualTypeOperations.Families.formation.{w}
      ContextualBasedIdentityOperations.Families.elimination.reflSection)
    (_excluded : ¬ scope input) : Nonempty input.Output :=
  ⟨ContextualBasedIdentityOperations.Families.elimination.j
    input.left input.motive input.base⟩

/-- Any supplied local results extend as raw data in this particular
full-motive model. No law is inferred for those supplied results. -/
theorem extends_any_scoped_output
    (scope : Input ContextualTypeOperations.Families.formation.{w}
      ContextualBasedIdentityOperations.Families.elimination.reflSection → Prop)
    (scopedOutput : (input : Input ContextualTypeOperations.Families.formation.{w}
      ContextualBasedIdentityOperations.Families.elimination.reflSection) →
      scope input → input.Output) :
    ∃ elimination : FixedSection ContextualTypeOperations.Families.formation.{w}
        ContextualBasedIdentityOperations.Families.elimination.reflSection,
      ∀ input admitted, elimination.run input = scopedOutput input admitted :=
  (total_extension_iff scope scopedOutput).mpr (complement_inhabited scope)

end EqualityFamilies

namespace Indiscrete

open ContextualTypeOperations.IndiscreteBoundary (formation reflexivity)

/-- The actual endpoint/reflexivity section for the existing indiscrete
identity, independently of the impossible total elimination operation. -/
def reflSection : Section formation :=
  fun {_ _} left context => ⟨⟨context, left context⟩, PUnit.unit⟩

def reindexing : Reindexing formation where
  map := fun {_ _} substitution {_} _left point =>
    ⟨⟨substitution point.1.1, point.1.2⟩, point.2⟩

theorem section_boundary {context : Type} {type : context → Type} (left : (x : context) → type x) :
    (familiesCwf.{0}).compS ((familiesCwf.{0}).wk (witnessType formation left)) (reflSection left) =
        ContextualProductComparison.selfExtend (familiesCwf.{0}) left ∧
      HEq ((familiesCwf.{0}).tmSub ((familiesCwf.{0}).vz (witnessType formation left))
        (reflSection left)) (reflexivity.refl left) :=
  ⟨rfl, HEq.rfl⟩

theorem section_square {source target : Type} (substitution : source → target)
    {type : target → Type} (left : (x : target) → type x) :
    (familiesCwf.{0}).compS (reindexing.map substitution left)
        (reflSection ((familiesCwf.{0}).tmSub left substitution)) =
      (familiesCwf.{0}).compS (reflSection left) substitution := rfl

/-- These fibres can vary with the original context but are independent of
the added endpoint and path. This is a separating example of a scope, not
a restriction imposed on arbitrary supplied scopes or on native motives. -/
def PullbackScope (input : Input formation reflSection) : Prop :=
  ∀ point : basedContext formation input.left,
    input.motive point = input.motive (reflSection input.left point.1.1)

def scopedJ (input : Input formation reflSection) (admitted : PullbackScope input) : input.Output :=
  fun point => cast (admitted point).symm (input.base point.1.1)

theorem scoped_beta (input : Input formation reflSection) (admitted : PullbackScope input) :
    (familiesCwf.{0}).tmSub (scopedJ input admitted) (reflSection input.left) = input.base := by
  funext point
  rfl

/-- Actual dependent reindexing of all five input components; its method
type is the reflexivity pullback of its reindexed motive. -/
def reindex (input : Input formation reflSection) {source : Type}
    (substitution : source → input.context) : Input formation reflSection where
  context := source
  type := fun point => input.type (substitution point)
  left := fun point => input.left (substitution point)
  motive := fun point => input.motive (reindexing.map substitution input.left point)
  base := fun point => input.base (substitution point)

theorem reindex_comp (input : Input formation reflSection) {source target : Type}
    (first : source → input.context) (second : target → source) :
    reindex (reindex input first) second = reindex input (fun point => first (second point)) := rfl

theorem reindex_admitted (input : Input formation reflSection) (admitted : PullbackScope input)
    {source : Type} (substitution : source → input.context) :
    PullbackScope (reindex input substitution) := by
  intro point
  exact admitted (reindexing.map substitution input.left point)

theorem scoped_substitution (input : Input formation reflSection) (admitted : PullbackScope input)
    {source : Type} (substitution : source → input.context) :
    (familiesCwf.{0}).tmSub (scopedJ input admitted) (reindexing.map substitution input.left) =
      scopedJ (reindex input substitution) (reindex_admitted input admitted substitution) := rfl

theorem scoped_beta_substitution (input : Input formation reflSection)
    (admitted : PullbackScope input) {source : Type}
    (substitution : source → input.context) :
    (familiesCwf.{0}).tmSub
        ((familiesCwf.{0}).tmSub (scopedJ input admitted)
          (reindexing.map substitution input.left))
        (reflSection ((familiesCwf.{0}).tmSub input.left substitution)) =
      (familiesCwf.{0}).tmSub input.base substitution := by
  rw [scoped_substitution]
  exact scoped_beta (reindex input substitution) (reindex_admitted input admitted substitution)

/-- A nonconstant finite family over a nontrivial context. -/
def varying : Input formation reflSection where
  context := Nat
  type := fun context => Fin (context + 2)
  left := fun context => ⟨context, by omega⟩
  motive := fun point => Fin (point.1.1 + 3)
  base := fun context => ⟨context + 1, by change context + 1 < context + 3; omega⟩

theorem varying_admitted : PullbackScope varying := fun _ => rfl

theorem scope_nonempty : ∃ input : Input formation reflSection, PullbackScope input :=
  ⟨varying, varying_admitted⟩

def folding (context : Nat) : Nat := context % 3 + 1

/-- A non-reflexive endpoint is allowed by this deliberately indiscrete
identity. The admitted computation is nonempty, and substitution changes
the contextual value and finite result fibre. -/
theorem varying_computation :
    (scopedJ varying varying_admitted ⟨⟨(0 : Nat), ⟨1, by decide⟩⟩, PUnit.unit⟩).val = 1 ∧
      (scopedJ (reindex varying folding) (reindex_admitted varying varying_admitted folding)
        (reflSection (reindex varying folding).left (0 : Nat))).val = 2 :=
  ⟨rfl, rfl⟩

/-- An output in the same nonempty motive fibre can still violate the
method computation equation. Raw output existence is not qualification. -/
def wrongVarying : varying.Output := fun point =>
  ⟨0, by change 0 < (show Nat from point.1.1) + 3; omega⟩

theorem wrong_scoped_beta :
    (familiesCwf.{0}).tmSub wrongVarying (reflSection varying.left) ≠ varying.base := by
  intro same
  have value := congrArg (fun output => (output (0 : Nat)).val) same
  change (0 : Nat) = 1 at value
  exact Nat.zero_ne_one value

/-- Reuse the actual endpoint-sensitive motive of the established based-J
obstruction; the base is well typed at the concrete correct section. -/
def obstructed : Input formation reflSection where
  context := PUnit
  type := ContextualBasedIdentityOperations.IndiscreteBoundary.domain
  left := ContextualBasedIdentityOperations.IndiscreteBoundary.left
  motive := ContextualBasedIdentityOperations.IndiscreteBoundary.motive
  base := fun _ => PUnit.unit

theorem obstructed_output_empty : ¬ Nonempty obstructed.Output := by
  rintro ⟨output⟩
  have result := output ⟨⟨PUnit.unit, true⟩, PUnit.unit⟩
  have empty : Empty := by
    simpa [obstructed, ContextualBasedIdentityOperations.IndiscreteBoundary.motive] using result
  exact empty.elim

theorem obstructed_outside : ¬ PullbackScope obstructed := by
  intro admitted
  exact obstructed_output_empty ⟨scopedJ obstructed admitted⟩

theorem no_total_extension :
    ¬ ∃ elimination : FixedSection formation reflSection,
      ∀ (input : Input formation reflSection) (admitted : PullbackScope input),
        elimination.run input = scopedJ input admitted :=
  no_total_extension_of_empty_output PullbackScope scopedJ obstructed obstructed_output_empty

/-- Even changing the section does not repair the obstruction if its
endpoint and reflexivity equations must still be correct. -/
theorem no_boundary_correct_total :
    ¬ ∃ elimination : Elimination formation, Boundary reflexivity elimination :=
  ContextualBasedIdentityOperations.IndiscreteBoundary.no_boundary_elimination

theorem scoped_operation_without_total_extension :
    (∃ input : Input formation reflSection, PullbackScope input) ∧
      (∀ (input : Input formation reflSection) (admitted : PullbackScope input),
        (familiesCwf.{0}).tmSub (scopedJ input admitted) (reflSection input.left) = input.base) ∧
      (∀ (input : Input formation reflSection) (_admitted : PullbackScope input)
        (source : Type) (substitution : source → input.context),
        PullbackScope (reindex input substitution)) ∧
      (∀ (input : Input formation reflSection) (admitted : PullbackScope input)
        (source : Type) (substitution : source → input.context),
        (familiesCwf.{0}).tmSub (scopedJ input admitted) (reindexing.map substitution input.left) =
          scopedJ (reindex input substitution) (reindex_admitted input admitted substitution)) ∧
      ¬ ∃ elimination : Elimination formation, Boundary reflexivity elimination :=
  ⟨scope_nonempty, scoped_beta, fun input admitted _ substitution =>
    reindex_admitted input admitted substitution,
    fun input admitted _ substitution => scoped_substitution input admitted substitution,
    no_boundary_correct_total⟩

end Indiscrete

#print axioms total_extension_iff
#print axioms Indiscrete.scoped_beta_substitution
#print axioms Indiscrete.scoped_operation_without_total_extension

end Mettapedia.TypeTheory.ContextualBasedIdentityScope
