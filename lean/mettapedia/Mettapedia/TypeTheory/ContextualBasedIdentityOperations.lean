import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Raw fixed-left-endpoint contextual identity elimination

The left endpoint is a term in the original context. Motives range over the
extension by a right endpoint and an identity witness from that fixed left
endpoint. The reflexivity method therefore lives in the original context,
not its extension by an arbitrary left endpoint.

This is the shape of based path induction. It is not identified with the
full two-endpoint operation in `ContextualTypeOperations`; relating those
interfaces requires additional motive-abstraction structure. The operation,
its context maps and its laws remain separate. Strict substitution predicates
describe equality-based representatives, not all equivalence-based models.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualBasedIdentityOperations

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations (IdentityFormationOperations IdentityReflexivityOperations)
open ContextualProductComparison (selfExtend)

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

def witnessType (identity : IdentityFormationOperations C)
    {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type) :
    C.Ty (C.ext context type) :=
  identity.idTy (C.tySub type (C.wk type)) (C.tmSub left (C.wk type)) (C.vz type)

def basedContext (identity : IdentityFormationOperations C)
    {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type) : C.Ctx :=
  C.ext (C.ext context type) (witnessType identity left)

def baseProjection (identity : IdentityFormationOperations C)
    {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type) :
    C.Sub (basedContext identity left) context :=
  C.compS (C.wk type) (C.wk (witnessType identity left))

def rightEndpoint (identity : IdentityFormationOperations C)
    {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type) :
    C.Tm (basedContext identity left)
      (C.tySub (C.tySub type (C.wk type)) (C.wk (witnessType identity left))) :=
  C.tmSub (C.vz type) (C.wk (witnessType identity left))

/-- Data only. A reflexivity section is not declared correct merely by its
name; the endpoint and witness equations occur in `Boundary`. -/
structure Elimination (identity : IdentityFormationOperations C) where
  reflSection : {context : C.Ctx} → {type : C.Ty context} →
    (left : C.Tm context type) → C.Sub context (basedContext identity left)
  j : {context : C.Ctx} → {type : C.Ty context} →
    (left : C.Tm context type) → (motive : C.Ty (basedContext identity left)) →
    C.Tm context (C.tySub motive (reflSection left)) →
    C.Tm (basedContext identity left) motive

structure Reindexing (identity : IdentityFormationOperations C) where
  map : {source target : C.Ctx} → (substitution : C.Sub source target) →
    {type : C.Ty target} → (left : C.Tm target type) →
    C.Sub (basedContext identity (C.tmSub left substitution)) (basedContext identity left)

structure Operations (identity : IdentityFormationOperations C) where
  elimination : Elimination identity
  reindexing : Reindexing identity

def Boundary {identity : IdentityFormationOperations C}
    (reflexivity : IdentityReflexivityOperations identity) (elimination : Elimination identity) : Prop :=
  (∀ {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type),
    C.compS (C.wk (witnessType identity left)) (elimination.reflSection left) =
      selfExtend C left) ∧
  (∀ {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type),
    HEq (C.tmSub (C.vz (witnessType identity left)) (elimination.reflSection left))
      (reflexivity.refl left))

def Beta {identity : IdentityFormationOperations C} (elimination : Elimination identity) : Prop :=
  ∀ {context : C.Ctx} {type : C.Ty context} (left : C.Tm context type)
    (motive : C.Ty (basedContext identity left))
    (base : C.Tm context (C.tySub motive (elimination.reflSection left))),
    C.tmSub (elimination.j left motive base) (elimination.reflSection left) = base

def ReflexivitySquare {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type),
    C.compS (reindexing.map substitution left)
        (elimination.reflSection (C.tmSub left substitution)) =
      C.compS (elimination.reflSection left) substitution

def StrictReindexing {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity) : Prop :=
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type),
    C.compS (baseProjection identity left) (reindexing.map substitution left) =
      C.compS substitution (baseProjection identity (C.tmSub left substitution))) ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type),
    HEq (C.tmSub (rightEndpoint identity left) (reindexing.map substitution left))
        (rightEndpoint identity (C.tmSub left substitution)) ∧
      HEq (C.tmSub (C.vz (witnessType identity left)) (reindexing.map substitution left))
        (C.vz (witnessType identity (C.tmSub left substitution)))) ∧
  ReflexivitySquare elimination reindexing

def StrictJSubstitution {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type)
    (motive : C.Ty (basedContext identity left))
    (base : C.Tm target (C.tySub motive (elimination.reflSection left)))
    (reindexedBase : C.Tm source
      (C.tySub (C.tySub motive (reindexing.map substitution left))
        (elimination.reflSection (C.tmSub left substitution)))),
    HEq (C.tmSub base substitution) reindexedBase →
    HEq (C.tmSub (elimination.j left motive base) (reindexing.map substitution left))
      (elimination.j (C.tmSub left substitution)
        (C.tySub motive (reindexing.map substitution left)) reindexedBase)

/-- The base transport is derived from the section square and ordinary
CwF substitution composition. -/
def reindexBase {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity)
    (square : ReflexivitySquare elimination reindexing)
    {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type)
    (motive : C.Ty (basedContext identity left))
    (base : C.Tm target (C.tySub motive (elimination.reflSection left))) :
    C.Tm source (C.tySub (C.tySub motive (reindexing.map substitution left))
      (elimination.reflSection (C.tmSub left substitution))) :=
  cast (by rw [← C.tySub_comp, ← square substitution left, C.tySub_comp])
    (C.tmSub base substitution)

theorem reindexBase_heq {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity)
    (square : ReflexivitySquare elimination reindexing)
    {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type)
    (motive : C.Ty (basedContext identity left))
    (base : C.Tm target (C.tySub motive (elimination.reflSection left))) :
    HEq (reindexBase elimination reindexing square substitution left motive base)
      (C.tmSub base substitution) := cast_heq _ _

theorem j_beta_substitution {identity : IdentityFormationOperations C}
    (elimination : Elimination identity) (reindexing : Reindexing identity)
    (square : ReflexivitySquare elimination reindexing)
    (stable : StrictJSubstitution elimination reindexing) (beta : Beta elimination)
    {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (left : C.Tm target type)
    (motive : C.Ty (basedContext identity left))
    (base : C.Tm target (C.tySub motive (elimination.reflSection left))) :
    C.tmSub (C.tmSub (elimination.j left motive base) (reindexing.map substitution left))
        (elimination.reflSection (C.tmSub left substitution)) =
      reindexBase elimination reindexing square substitution left motive base := by
  have commutes := eq_of_heq (stable substitution left motive base _
    (reindexBase_heq elimination reindexing square substitution left motive base).symm)
  rw [commutes]
  exact beta _ _ _

namespace Families

open ContextualTypeOperations.Families (formation reflexivity)

/-- Equality elimination at one fixed endpoint in the actual full
set-family CwF. The motive remains an arbitrary family on the based context. -/
def elimination : Elimination formation.{w} where
  reflSection left context := ⟨⟨context, left context⟩, ⟨⟨rfl⟩⟩⟩
  j left motive base := by
    intro point
    rcases point with ⟨⟨context, right⟩, equality⟩
    change ULift (PLift (left context = right)) at equality
    rcases equality with ⟨⟨equality⟩⟩
    cases equality
    exact base context

def reindexing : Reindexing formation.{w} where
  map := fun {_ _} substitution {_} _left point =>
    ⟨⟨substitution point.1.1, point.1.2⟩, point.2⟩

def operations : Operations formation.{w} := ⟨elimination, reindexing⟩

theorem boundary : Boundary reflexivity.{w} elimination := ⟨fun _ => rfl, fun _ => HEq.rfl⟩

theorem beta : Beta elimination.{w} := fun _ _ _ => rfl

theorem reindexing_laws : StrictReindexing elimination.{w} reindexing := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution type left
    rfl
  · intro source target substitution type left
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro source target substitution type left
    rfl

theorem substitution : StrictJSubstitution elimination.{w} reindexing := by
  intro source target sigma type left motive base reindexedBase same
  have equal : (familiesCwf.{w}).tmSub base sigma = reindexedBase := eq_of_heq same
  cases equal
  apply heq_of_eq
  funext point
  rcases point with ⟨⟨context, right⟩, equality⟩
  change ULift (PLift (left (sigma context) = right)) at equality
  rcases equality with ⟨⟨equality⟩⟩
  cases equality
  rfl

def domain : Nat → Type := fun context => Fin (context + 2)

def left : (familiesCwf.{0}).Tm Nat domain := fun context => ⟨context, by omega⟩

def motive : (familiesCwf.{0}).Ty (basedContext formation left) :=
  fun point => Fin (point.1.1 + point.1.2.val + 3)

def base : (familiesCwf.{0}).Tm Nat
    ((familiesCwf.{0}).tySub motive (elimination.reflSection left)) :=
  fun context => ⟨context + 1, by change context + 1 < context + context + 3; omega⟩

def foldingContext (context : Nat) : Nat := context % 3 + 1

/-- A genuinely varying motive and noninjective context map instantiate
the generic based-J substitution/beta consequence. -/
theorem varying_substitution_square :
    (familiesCwf.{0}).tmSub
        ((familiesCwf.{0}).tmSub (elimination.j left motive base)
          (reindexing.map foldingContext left))
        (elimination.reflSection ((familiesCwf.{0}).tmSub left foldingContext)) =
      reindexBase elimination reindexing reindexing_laws.2.2 foldingContext left motive base :=
  j_beta_substitution elimination reindexing reindexing_laws.2.2 substitution beta
    foldingContext left motive base

theorem dropping_substitution_changes_value :
    ((elimination.j left motive base) (elimination.reflSection left 0)).val = 1 ∧
      (((familiesCwf.{0}).tmSub
        ((familiesCwf.{0}).tmSub (elimination.j left motive base)
          (reindexing.map foldingContext left))
        (elimination.reflSection ((familiesCwf.{0}).tmSub left foldingContext))) 0).val = 2 :=
  ⟨rfl, rfl⟩

end Families

namespace IndiscreteBoundary

open ContextualTypeOperations.IndiscreteBoundary (formation reflexivity)

def domain : PUnit → Type := fun _ => Bool

def left : (familiesCwf.{0}).Tm PUnit domain := fun _ => false

/-- The right endpoint is visible to an actual dependent motive. -/
def motive : (familiesCwf.{0}).Ty (basedContext formation left) :=
  fun point => if (show Bool from point.1.2) = false then PUnit else Empty

def base (elimination : Elimination formation) (boundary : Boundary reflexivity elimination) :
    (familiesCwf.{0}).Tm PUnit
      ((familiesCwf.{0}).tySub motive (elimination.reflSection left)) := by
  intro point
  have endpoint := congrArg (fun pair => pair.2) (congrFun (boundary.1 left) point)
  change (if (show Bool from (elimination.reflSection left point).1.2) = false
    then PUnit else Empty)
  exact if_pos endpoint ▸ PUnit.unit

/-- Formation and reflexivity on the same full CwF cannot supply based J
for the indiscrete identity. Even its beta equation is unnecessary here. -/
theorem no_boundary_elimination :
    ¬ ∃ elimination : Elimination formation, Boundary reflexivity elimination := by
  rintro ⟨elimination, boundary⟩
  have result := elimination.j left motive (base elimination boundary)
    ⟨⟨PUnit.unit, true⟩, PUnit.unit⟩
  have empty : Empty := by simpa [motive] using result
  exact empty.elim

end IndiscreteBoundary

/-- A concrete based-J instance and a dependent-motive obstruction on the
same contextual core; neither selects an object-language identity principle. -/
theorem set_family_controls :
    Boundary ContextualTypeOperations.Families.reflexivity.{0} Families.elimination ∧
      Beta Families.elimination.{0} ∧ StrictReindexing Families.elimination.{0} Families.reindexing ∧
      StrictJSubstitution Families.elimination.{0} Families.reindexing ∧
      ¬ ∃ elimination : Elimination ContextualTypeOperations.IndiscreteBoundary.formation,
        Boundary ContextualTypeOperations.IndiscreteBoundary.reflexivity elimination :=
  ⟨Families.boundary, Families.beta, Families.reindexing_laws, Families.substitution,
    IndiscreteBoundary.no_boundary_elimination⟩

#print axioms j_beta_substitution
#print axioms Families.substitution
#print axioms Families.varying_substitution_square
#print axioms IndiscreteBoundary.no_boundary_elimination
#print axioms set_family_controls

end Mettapedia.TypeTheory.ContextualBasedIdentityOperations
