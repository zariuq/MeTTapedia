import Mettapedia.TypeTheory.ContextualIdentityTypes

/-!
# Substitution coherence of full set-family identity elimination

The endpoint and identity-context substitutions below are the actual maps
of the existing set-family CwF. They preserve the reflexivity boundary and
commute with its equality eliminator for every dependent motive, including
motives indexed by both endpoints and the identity witness.

These laws apply to the identity component of the stratified set-family
semantic span by universe instantiation. They are not an interpretation of
native syntax: declaration meaning and its connection to native substitution
remain separate obligations. The underlying equality model validates proof
irrelevance; substitution coherence does not select that principle for an
object language.

The negative control reuses the existing indiscrete identity formation and
its dependent diagonal motive. Pulling that motive to an off-diagonal point
has no section, so context reindexing does not repair an invalid eliminator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualIdentitySubstitution

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualIdentityTypes

universe u

variable {source middle target : Type u}

/-- The canonical comprehension map over a context substitution. -/
def endpointReindex (substitution : source → target) (type : target → Type u) :
    (familiesCwf.{u}).Sub
      ((familiesCwf.{u}).ext source ((familiesCwf.{u}).tySub type substitution))
      ((familiesCwf.{u}).ext target type) :=
  fun point => ⟨substitution point.1, point.2⟩

/-- Reindex both endpoints and retain their actual equality witness. -/
def identityReindex (substitution : source → target) (type : target → Type u) :
    (familiesCwf.{u}).Sub
      (identityContext familiesCwf Families.identityFormation
        ((familiesCwf.{u}).tySub type substitution))
      (identityContext familiesCwf Families.identityFormation type) :=
  fun point => ⟨⟨⟨substitution point.1.1.1, point.1.1.2⟩, point.1.2⟩, point.2⟩

@[simp] theorem endpointReindex_id (type : target → Type u) :
    endpointReindex (id : target → target) type = id := rfl

@[simp] theorem endpointReindex_comp
    (earlier : source → middle) (later : middle → target) (type : target → Type u) :
    endpointReindex (later ∘ earlier) type =
      endpointReindex later type ∘
        endpointReindex earlier ((familiesCwf.{u}).tySub type later) := rfl

@[simp] theorem identityReindex_id (type : target → Type u) :
    identityReindex (id : target → target) type = id := rfl

@[simp] theorem identityReindex_comp
    (earlier : source → middle) (later : middle → target) (type : target → Type u) :
    identityReindex (later ∘ earlier) type =
      identityReindex later type ∘
        identityReindex earlier ((familiesCwf.{u}).tySub type later) := rfl

/-- The identity-context map preserves the actual reflexivity substitution,
not merely the endpoint pair. -/
theorem reflexivity_square (substitution : source → target) (type : target → Type u) :
    identityReindex substitution type ∘
        Families.identityElimination.reflexivitySubstitution
          ((familiesCwf.{u}).tySub type substitution) =
      Families.identityElimination.reflexivitySubstitution type ∘
        endpointReindex substitution type := rfl

/-- Full contextual J commutes with substitution. The motive is arbitrary
over the complete identity context, rather than restricted to a constant
family or a predicate of endpoints alone. -/
theorem j_substitution (substitution : source → target) (type : target → Type u)
    (motive : (familiesCwf.{u}).Ty
      (identityContext familiesCwf Families.identityFormation type))
    (base : (familiesCwf.{u}).Tm ((familiesCwf.{u}).ext target type)
      ((familiesCwf.{u}).tySub motive
        (Families.identityElimination.reflexivitySubstitution type))) :
    (familiesCwf.{u}).tmSub (Families.identityElimination.j motive base)
        (identityReindex substitution type) =
      Families.identityElimination.j
        ((familiesCwf.{u}).tySub motive (identityReindex substitution type))
        ((familiesCwf.{u}).tmSub base (endpointReindex substitution type)) := by
  funext point
  rcases point with ⟨⟨⟨context, left⟩, right⟩, equality⟩
  cases equality.down.down
  rfl

/-- Substitution preserves J's beta boundary at the same reindexed motive
and base section. -/
theorem j_beta_substitution (substitution : source → target) (type : target → Type u)
    (motive : (familiesCwf.{u}).Ty
      (identityContext familiesCwf Families.identityFormation type))
    (base : (familiesCwf.{u}).Tm ((familiesCwf.{u}).ext target type)
      ((familiesCwf.{u}).tySub motive
        (Families.identityElimination.reflexivitySubstitution type))) :
    (familiesCwf.{u}).tmSub
        ((familiesCwf.{u}).tmSub (Families.identityElimination.j motive base)
          (identityReindex substitution type))
        (Families.identityElimination.reflexivitySubstitution
          ((familiesCwf.{u}).tySub type substitution)) =
      (familiesCwf.{u}).tmSub base (endpointReindex substitution type) := by
  rw [j_substitution]
  exact Families.identityElimination.beta _ _

/-- Reindexing a full J term along a composite agrees with successive
reindexing, at the original dependent motive. -/
theorem j_substitution_comp
    (earlier : source → middle) (later : middle → target) (type : target → Type u)
    (motive : (familiesCwf.{u}).Ty
      (identityContext familiesCwf Families.identityFormation type))
    (base : (familiesCwf.{u}).Tm ((familiesCwf.{u}).ext target type)
      ((familiesCwf.{u}).tySub motive
        (Families.identityElimination.reflexivitySubstitution type))) :
    Families.identityElimination.j
        ((familiesCwf.{u}).tySub motive (identityReindex (later ∘ earlier) type))
        ((familiesCwf.{u}).tmSub base (endpointReindex (later ∘ earlier) type)) =
      (familiesCwf.{u}).tmSub
        (Families.identityElimination.j
          ((familiesCwf.{u}).tySub motive (identityReindex later type))
          ((familiesCwf.{u}).tmSub base (endpointReindex later type)))
        (identityReindex earlier ((familiesCwf.{u}).tySub type later)) := by
  rw [← j_substitution, ← j_substitution]
  rfl

/-! ## The existing dependent-motive obstruction survives reindexing -/

/-- A point already used by the full-family indiscrete-identity countermodel. -/
def indiscreteOffDiagonal :
    (familiesCwf.{0}).Sub PUnit
      (identityContext familiesCwf Families.indiscreteFormation Families.boolFamily) :=
  fun _ => ⟨⟨⟨PUnit.unit, false⟩, true⟩, PUnit.unit⟩

/-- Pullback does not create a section at the forbidden endpoint pair. -/
theorem offDiagonal_pullback_has_no_section :
    IsEmpty ((familiesCwf.{0}).Tm PUnit
      ((familiesCwf.{0}).tySub Families.diagonalOnlyMotive indiscreteOffDiagonal)) := by
  constructor
  intro candidate
  have empty : Empty := by
    simpa [Families.diagonalOnlyMotive, indiscreteOffDiagonal] using candidate PUnit.unit
  exact empty.elim

#print axioms endpointReindex
#print axioms identityReindex
#print axioms endpointReindex_id
#print axioms endpointReindex_comp
#print axioms identityReindex_id
#print axioms identityReindex_comp
#print axioms reflexivity_square
#print axioms j_substitution
#print axioms j_beta_substitution
#print axioms j_substitution_comp
#print axioms indiscreteOffDiagonal
#print axioms offDiagonal_pullback_has_no_section

end Mettapedia.TypeTheory.ContextualIdentitySubstitution
