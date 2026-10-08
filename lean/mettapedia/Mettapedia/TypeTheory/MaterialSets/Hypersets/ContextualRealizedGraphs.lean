import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers

/-!
# Future-indexed equality and membership in the contextual graph universe

Equality is the constructed small matching limit. A current membership
receipt retains a literal child and equality to that child's whole future
diagram. Context transport computes both parts. Two-sided future
membership actions construct extensional equality; present-only actions
are insufficient for this construction.

Matching evidence is not native identity. No equality reflection, UIP or
identity eliminator is imposed by these operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs

open CategoryTheory ContextualGraphDiagrams
universe u
variable {D : Type u} [Category.{u} D]

abbrev Equal {point : D} (first second : Value D point) : Type u :=
  ContextualGraphRealizers.Realizer first.1 second.1 point first.2 second.2

namespace Equal

def refl {point : D} (value : Value D point) : Equal value value :=
  ContextualGraphRealizers.Realizer.refl value.1 point value.2

def ofEq {point : D} {first second : Value D point} (same : first = second) :
    Equal first second := same ▸ refl first

def symm {point : D} {first second : Value D point} (proof : Equal first second) :
    Equal second first := ContextualGraphRealizers.Realizer.symm proof

def trans {point : D} {first middle last : Value D point}
    (earlier : Equal first middle) (later : Equal middle last) : Equal first last :=
  ContextualGraphRealizers.Realizer.trans middle.1 earlier later

def restrict {first second : D} (arrival : first ⟶ second)
    {left right : Value D first} (proof : Equal left right) :
    Equal (move D arrival left) (move D arrival right) :=
  ContextualGraphRealizers.Realizer.restrict arrival proof

end Equal

abbrev Member {point : D} (child parent : Value D point) : Type u :=
  Σ receipt : ContextualGraphDiagrams.Child D parent,
    Equal child (childValue D parent receipt)

namespace Member

def atChild {point : D} (parent : Value D point)
    (child : ContextualGraphDiagrams.Child D parent) :
    Member (childValue D parent child) parent := ⟨child, Equal.refl _⟩

def restrict {first second : D} (arrival : first ⟶ second)
    {child parent : Value D first} (proof : Member child parent) :
    Member (move D arrival child) (move D arrival parent) :=
  ⟨moveChild D arrival parent proof.1, Equal.restrict arrival proof.2⟩

def transportChild {point : D} {child other parent : Value D point}
    (same : Equal child other) (proof : Member child parent) : Member other parent :=
  ⟨proof.1, same.symm.trans proof.2⟩

def transportParent {point : D} {child parent other : Value D point}
    (same : Equal parent other) (proof : Member child parent) : Member child other :=
  let response := ContextualGraphRealizers.Realizer.currentForth same proof.1
  ⟨response.1, proof.2.trans response.2⟩

def transport {point : D} {child otherChild parent otherParent : Value D point}
    (sameChild : Equal child otherChild) (sameParent : Equal parent otherParent)
    (proof : Member child parent) : Member otherChild otherParent :=
  transportParent sameParent (transportChild sameChild proof)

end Member

/-- The unbounded premise supplies actions at every future, exactly as
required by contextual extensionality. -/
def extensionality {point : D} {first second : Value D point}
    (forth : ∀ (target : D) (arrival : point ⟶ target) (child : Value D target),
      Member child (move D arrival first) → Member child (move D arrival second))
    (back : ∀ (target : D) (arrival : point ⟶ target) (child : Value D target),
      Member child (move D arrival second) → Member child (move D arrival first)) :
    Equal first second :=
  ContextualGraphRealizers.roll first.1 second.1
    (fun future child =>
      let response := forth future.1 future.2
        (childValue D (move D future.2 first) child)
        (Member.atChild (move D future.2 first) child)
      ⟨response.1, response.2⟩)
    (fun future child =>
      let response := back future.1 future.2
        (childValue D (move D future.2 second) child)
        (Member.atChild (move D future.2 second) child)
      ⟨response.1, response.2.symm⟩)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
