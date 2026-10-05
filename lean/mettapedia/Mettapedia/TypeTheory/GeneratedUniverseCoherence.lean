import Mettapedia.TypeTheory.GeneratedUniverseSubstitution

/-!
# Constructed cumulative comparisons for generated universes

The successor envelope contains the lower code carrier and faithfully embeds
its codes. Forming a product, sum, identity fibre or W-type before embedding
and forming it from embedded data are generally different codes. Explicit
decoding equivalences compare these routes. Iterating the actual successor
construction gives a second embedding and coherent decoding, without a
supplied small enclosing operator or an internal reflection principle.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GeneratedUniverseCoherence

open GeneratedFamilyUniverse FamilyEnclosingUniverse

universe u

variable {A : Type u} {B : A → Type u}

abbrev NextCode (A : Type u) (B : A → Type u) :=
  Code (Code A B) (fun code => ULift.{u + 1, u} code.El)

def piUp (domain : Code A B) (codomain : domain.El → Code A B) : NextCode A B :=
  Code.pi (successorEmbedding A B domain)
    (fun value => successorEmbedding A B (codomain value.down))

def sigmaUp (domain : Code A B) (codomain : domain.El → Code A B) : NextCode A B :=
  Code.sigma (successorEmbedding A B domain)
    (fun value => successorEmbedding A B (codomain value.down))

def identityUp (domain : Code A B) (left right : domain.El) : NextCode A B :=
  Code.identity (successorEmbedding A B domain) (ULift.up left) (ULift.up right)

def wUp (shape : Code A B) (position : shape.El → Code A B) : NextCode A B :=
  Code.w (successorEmbedding A B shape)
    (fun value => successorEmbedding A B (position value.down))

/-- Both dependent function arguments and values are compared explicitly. -/
def piDecode (domain : Code A B) (codomain : domain.El → Code A B) :
    (piUp domain codomain).El ≃ (Code.pi domain codomain).El where
  toFun function argument := (function (ULift.up argument)).down
  invFun function argument := ULift.up (function argument.down)
  left_inv function := by
    funext argument
    cases argument
    rfl
  right_inv _ := rfl

def sigmaDecode (domain : Code A B) (codomain : domain.El → Code A B) :
    (sigmaUp domain codomain).El ≃ (Code.sigma domain codomain).El where
  toFun value := ⟨value.1.down, value.2.down⟩
  invFun value := ⟨ULift.up value.1, ULift.up value.2⟩
  left_inv value := by
    rcases value with ⟨⟨argument⟩, ⟨result⟩⟩
    rfl
  right_inv value := by
    cases value
    rfl

def identityDecode (domain : Code A B) (left right : domain.El) :
    (identityUp domain left right).El ≃ (Code.identity domain left right).El where
  toFun witness := ⟨⟨congrArg ULift.down witness.down.down⟩⟩
  invFun witness := ⟨⟨congrArg ULift.up witness.down.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace WTree

variable {Shape : Type u} {Position : Shape → Type u}

/-- Lift every shape and child address of an actual well-founded tree. -/
def raise : WTree Shape Position →
    WTree (ULift.{u + 1, u} Shape)
      (fun shape => ULift.{u + 1, u} (Position shape.down))
  | .sup shape children => .sup (ULift.up shape) (fun address => raise (children address.down))

def lower : WTree (ULift.{u + 1, u} Shape)
    (fun shape => ULift.{u + 1, u} (Position shape.down)) → WTree Shape Position
  | .sup shape children => .sup shape.down (fun address => lower (children (ULift.up address)))

theorem lower_raise (tree : WTree Shape Position) : lower (raise tree) = tree := by
  induction tree with
  | sup shape children earlier =>
      simp only [raise, lower]
      congr
      funext address
      exact earlier address

theorem raise_lower (tree : WTree (ULift.{u + 1, u} Shape)
    (fun shape => ULift.{u + 1, u} (Position shape.down))) : raise (lower tree) = tree := by
  induction tree with
  | sup shape children earlier =>
      cases shape
      simp only [raise, lower]
      congr
      funext address
      cases address
      exact earlier (ULift.up _)

def liftEquiv :
    WTree (ULift.{u + 1, u} Shape)
        (fun shape => ULift.{u + 1, u} (Position shape.down)) ≃ WTree Shape Position where
  toFun := lower
  invFun := raise
  left_inv := raise_lower
  right_inv := lower_raise

end WTree

def wDecode (shape : Code A B) (position : shape.El → Code A B) :
    (wUp shape position).El ≃ (Code.w shape position).El :=
  WTree.liftEquiv (Shape := shape.El) (Position := fun value => (position value).El)

/-- Decode a lifted lower product, then encode the product formed from
lifted data. Neither route is identified by code equality. -/
def piComparison (domain : Code A B) (codomain : domain.El → Code A B) :
    (successor A B).El (successorEmbedding A B (Code.pi domain codomain)) ≃
      (piUp domain codomain).El :=
  (decodeSuccessor (Code.pi domain codomain)).trans (piDecode domain codomain).symm

def sigmaComparison (domain : Code A B) (codomain : domain.El → Code A B) :
    (successor A B).El (successorEmbedding A B (Code.sigma domain codomain)) ≃
      (sigmaUp domain codomain).El :=
  (decodeSuccessor (Code.sigma domain codomain)).trans (sigmaDecode domain codomain).symm

def identityComparison (domain : Code A B) (left right : domain.El) :
    (successor A B).El (successorEmbedding A B (Code.identity domain left right)) ≃
      (identityUp domain left right).El :=
  (decodeSuccessor (Code.identity domain left right)).trans (identityDecode domain left right).symm

def wComparison (shape : Code A B) (position : shape.El → Code A B) :
    (successor A B).El (successorEmbedding A B (Code.w shape position)) ≃
      (wUp shape position).El :=
  (decodeSuccessor (Code.w shape position)).trans (wDecode shape position).symm

theorem piComparison_application (domain : Code A B) (codomain : domain.El → Code A B)
    (function : (Code.pi domain codomain).El) (argument : domain.El) :
    (piComparison domain codomain (ULift.up function) (ULift.up argument)).down =
      function argument := rfl

theorem sigmaComparison_first (domain : Code A B) (codomain : domain.El → Code A B)
    (value : (Code.sigma domain codomain).El) :
    (sigmaComparison domain codomain (ULift.up value)).1.down = value.1 := rfl

/-- A second enclosure is constructed from the actual first successor's
code carrier and decoded family. -/
def secondSuccessor (A : Type u) (B : A → Type u) :=
  successor (Code A B) (fun code => ULift.{u + 1, u} code.El)

def doubleEmbedding (A : Type u) (B : A → Type u) : Code A B ↪ (secondSuccessor A B).Code :=
  (successorEmbedding A B).trans
    (successorEmbedding (Code A B) (fun code => ULift.{u + 1, u} code.El))

def decodeDouble (code : Code A B) :
    (secondSuccessor A B).El (doubleEmbedding A B code) ≃ code.El :=
  (decodeSuccessor (successorEmbedding A B code)).trans (decodeSuccessor code)

/-- The composite decoder agrees with the two successive decoders on every
actual value. Code embedding identity is retained by injectivity. -/
theorem decodeDouble_composes (code : Code A B)
    (value : (secondSuccessor A B).El (doubleEmbedding A B code)) :
    decodeDouble code value =
      decodeSuccessor code (decodeSuccessor (successorEmbedding A B code) value) := rfl

#print axioms piComparison
#print axioms sigmaComparison
#print axioms identityComparison
#print axioms wComparison
#print axioms doubleEmbedding
#print axioms decodeDouble_composes

end Mettapedia.TypeTheory.GeneratedUniverseCoherence
