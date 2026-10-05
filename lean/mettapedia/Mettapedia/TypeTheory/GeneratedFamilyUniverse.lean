import Mettapedia.TypeTheory.FamilyEnclosingUniverse

/-!
# Generated semantic codes enclosing a dependent family

The code grammar is indexed by the type it represents. This permits ordinary
strictly positive induction in place of an inductive-recursive definition:
the index records a decoding, while the derivation records how that decoding
was generated. A code consists of both, rather than an arbitrary ambient type.

The grammar encloses an arbitrary dependent family and has actual constructors
for dependent products, sums, equality fibres and well-founded trees. Codes
live one ambient level above their decoded types. Equality fibres interpret
identity in the discrete type model; they do not impose identity reflection
or proof irrelevance on a native calculus. This semantic grammar does not
assert an internally small code carrier or internal closure under enclosure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GeneratedFamilyUniverse

open FamilyEnclosingUniverse

universe u

/-- A type-indexed derivation in the family-enclosing grammar. The recursive
premises of a dependent constructor range over its decoded domain, so the
grammar admits arbitrary dependent families of previously generated codes. -/
inductive Generation (A : Type u) (B : A → Type u) : Type u → Type (u + 1) where
  | base : Generation A B A
  | fibre (index : A) : Generation A B (B index)
  | empty : Generation A B (ULift.{u, 0} Empty)
  | unit : Generation A B (ULift.{u, 0} PUnit)
  | nat : Generation A B (ULift.{u, 0} Nat)
  | sum {X Y : Type u} (left : Generation A B X) (right : Generation A B Y) :
      Generation A B (Sum X Y)
  | pi {X : Type u} {Y : X → Type u} (domain : Generation A B X)
      (codomain : (x : X) → Generation A B (Y x)) :
      Generation A B ((x : X) → Y x)
  | sigma {X : Type u} {Y : X → Type u} (domain : Generation A B X)
      (codomain : (x : X) → Generation A B (Y x)) :
      Generation A B (Σ x : X, Y x)
  | identity {X : Type u} (domain : Generation A B X) (left right : X) :
      Generation A B (ULift.{u, 0} (PLift (left = right)))
  | w {X : Type u} {Y : X → Type u} (shape : Generation A B X)
      (position : (x : X) → Generation A B (Y x)) :
      Generation A B (WTree X Y)

namespace Generation

variable {A C : Type u} {B : A → Type u} {D : C → Type u}

/-- Replace the generating family by derivations for that same family in
another grammar. Every dependent branch is recursively translated. -/
def substitute (baseDerivation : Generation C D A)
    (fibres : (a : A) → Generation C D (B a)) :
    {X : Type u} → Generation A B X → Generation C D X
  | _, .base => baseDerivation
  | _, .fibre a => fibres a
  | _, .empty => .empty
  | _, .unit => .unit
  | _, .nat => .nat
  | _, .sum left right =>
      .sum (substitute baseDerivation fibres left) (substitute baseDerivation fibres right)
  | _, .pi domain codomain =>
      .pi (substitute baseDerivation fibres domain)
        (fun x => substitute baseDerivation fibres (codomain x))
  | _, .sigma domain codomain =>
      .sigma (substitute baseDerivation fibres domain)
        (fun x => substitute baseDerivation fibres (codomain x))
  | _, .identity domain left right =>
      .identity (substitute baseDerivation fibres domain) left right
  | _, .w shape position =>
      .w (substitute baseDerivation fibres shape)
        (fun x => substitute baseDerivation fibres (position x))

@[simp] theorem substitute_id {X : Type u} (generation : Generation A B X) :
    substitute .base .fibre generation = generation := by
  induction generation <;> simp_all [substitute]

/-- Substitution of generators composes on the entire grammar, including
arbitrary dependent product and tree branches. -/
theorem substitute_comp {E : Type u} {F : E → Type u}
    (firstBase : Generation C D A)
    (firstFibres : (a : A) → Generation C D (B a))
    (secondBase : Generation E F C)
    (secondFibres : (c : C) → Generation E F (D c))
    {X : Type u} (generation : Generation A B X) :
    substitute secondBase secondFibres
        (substitute firstBase firstFibres generation) =
      substitute (substitute secondBase secondFibres firstBase)
        (fun a => substitute secondBase secondFibres (firstFibres a))
        generation := by
  induction generation <;> simp_all [substitute]

/-- A closure predicate contains every generated decoding precisely by its
closure under the grammar's constructors. No ambient universe is substituted
for the generated carrier. -/
theorem closed_induction (P : Type u → Prop)
    (hBase : P A) (hFibre : ∀ a, P (B a))
    (hEmpty : P (ULift.{u, 0} Empty))
    (hUnit : P (ULift.{u, 0} PUnit))
    (hNat : P (ULift.{u, 0} Nat))
    (hSum : ∀ {X Y : Type u}, P X → P Y → P (Sum X Y))
    (hPi : ∀ {X : Type u} {Y : X → Type u},
      P X → (∀ x, P (Y x)) → P ((x : X) → Y x))
    (hSigma : ∀ {X : Type u} {Y : X → Type u},
      P X → (∀ x, P (Y x)) → P (Σ x : X, Y x))
    (hId : ∀ {X : Type u}, P X → ∀ x y : X,
      P (ULift.{u, 0} (PLift (x = y))))
    (hW : ∀ {X : Type u} {Y : X → Type u},
      P X → (∀ x, P (Y x)) → P (WTree X Y))
    {X : Type u} (generation : Generation A B X) : P X := by
  induction generation with
  | base => exact hBase
  | fibre a => exact hFibre a
  | empty => exact hEmpty
  | unit => exact hUnit
  | nat => exact hNat
  | sum _ _ left right => exact hSum left right
  | pi _ _ domain codomain => exact hPi domain codomain
  | sigma _ _ domain codomain => exact hSigma domain codomain
  | identity _ x y domain => exact hId domain x y
  | w _ _ shape position => exact hW shape position

end Generation

/-- Generated codes retain their formation derivation. -/
abbrev Code (A : Type u) (B : A → Type u) : Type (u + 1) :=
  Σ X : Type u, Generation A B X

namespace Code

variable {A : Type u} {B : A → Type u}

/-- Decode the type index certified by a formation derivation. -/
def El (code : Code A B) : Type u := code.1

def base : Code A B := ⟨A, .base⟩

def fibre (index : A) : Code A B := ⟨B index, .fibre index⟩

def empty : Code A B := ⟨ULift.{u, 0} Empty, .empty⟩

def unit : Code A B := ⟨ULift.{u, 0} PUnit, .unit⟩

def nat : Code A B := ⟨ULift.{u, 0} Nat, .nat⟩

def sum (left right : Code A B) : Code A B :=
  ⟨Sum left.El right.El, .sum left.2 right.2⟩

def pi (domain : Code A B) (codomain : domain.El → Code A B) : Code A B :=
  ⟨(x : domain.El) → (codomain x).El,
    .pi domain.2 (fun x => (codomain x).2)⟩

def sigma (domain : Code A B) (codomain : domain.El → Code A B) : Code A B :=
  ⟨Σ x : domain.El, (codomain x).El,
    .sigma domain.2 (fun x => (codomain x).2)⟩

def identity (domain : Code A B) (left right : domain.El) : Code A B :=
  ⟨ULift.{u, 0} (PLift (left = right)), .identity domain.2 left right⟩

def w (shape : Code A B) (position : shape.El → Code A B) : Code A B :=
  ⟨WTree shape.El (fun x => (position x).El),
    .w shape.2 (fun x => (position x).2)⟩

/-- The generated decoder has its own formation derivation at every code. -/
def generation (code : Code A B) : Generation A B code.El := code.2

/-- The selected fibre index remains available in a code, independently of
whether two fibres have the same decoding. -/
def rootFibre : Code A B → Option A
  | ⟨_, .fibre index⟩ => some index
  | _ => none

@[simp] theorem rootFibre_fibre (index : A) :
    rootFibre (fibre (B := B) index) = some index := rfl

theorem fibre_injective : Function.Injective (fibre (B := B)) := by
  intro left right equalCodes
  exact Option.some.inj (congrArg rootFibre equalCodes)

/-- Derivation-preserving substitution of the enclosing family. -/
def substitute {C : Type u} {D : C → Type u}
    (baseDerivation : Generation C D A)
    (fibres : (a : A) → Generation C D (B a))
    (code : Code A B) : Code C D :=
  ⟨code.El, Generation.substitute baseDerivation fibres code.generation⟩

@[simp] theorem substitute_decode {C : Type u} {D : C → Type u}
    (baseDerivation : Generation C D A)
    (fibres : (a : A) → Generation C D (B a)) (code : Code A B) :
    (code.substitute baseDerivation fibres).El = code.El := rfl

@[simp] theorem substitute_id (code : Code A B) :
    code.substitute .base .fibre = code := by
  cases code
  simp [substitute, generation, El]

theorem substitute_comp {C E : Type u} {D : C → Type u} {F : E → Type u}
    (firstBase : Generation C D A)
    (firstFibres : (a : A) → Generation C D (B a))
    (secondBase : Generation E F C)
    (secondFibres : (c : C) → Generation E F (D c))
    (code : Code A B) :
    (code.substitute firstBase firstFibres).substitute secondBase secondFibres =
      code.substitute (Generation.substitute secondBase secondFibres firstBase)
        (fun a => Generation.substitute secondBase secondFibres (firstFibres a)) := by
  cases code
  simp only [substitute, generation, El, Generation.substitute_comp]

end Code

/-- An actual generated envelope, with no enclosure operator supplied as an
assumption. The code constructors above, rather than all ambient types, supply
its closure operations. -/
def envelope (A : Type u) (B : A → Type u) :
    ClosedTarskiUniverseOver.{u + 1, u} A B where
  Code := Code A B
  El := Code.El
  baseCode := Code.base
  elBase := Equiv.refl A
  fibreCode := Code.fibre
  elFibre := fun index => Equiv.refl (B index)
  emptyCode := Code.empty
  elEmpty := Equiv.ulift
  unitCode := Code.unit
  elUnit := Equiv.ulift
  natCode := Code.nat
  elNat := Equiv.ulift
  sumCode := Code.sum
  elSum := fun left right => Equiv.refl (Sum left.El right.El)
  piCode := Code.pi
  elPi := fun domain codomain =>
    Equiv.refl ((x : domain.El) → (codomain x).El)
  sigmaCode := Code.sigma
  elSigma := fun domain codomain =>
    Equiv.refl (Σ x : domain.El, (codomain x).El)
  identityCode := Code.identity
  elIdentity := fun _domain _left _right => Equiv.ulift.trans Equiv.plift
  wCode := Code.w
  elW := fun shape position =>
    Equiv.refl (WTree shape.El (fun x => (position x).El))

/-- The generated grammar supplies a uniform family-enclosing operation. -/
def operator : FamilyEnclosingUniverseOperator.{u} where
  enclose := envelope

/-- Full dependent closure holds for arbitrary codes and arbitrary coded
families, rather than just a finite or constant-family fragment. -/
theorem dependent_closure (A : Type u) (B : A → Type u) :
    (envelope A B).toCodeFamily.PiClosedAt PUnit.unit ∧
      (envelope A B).toCodeFamily.SigmaClosedAt PUnit.unit :=
  ⟨(envelope A B).piClosedAt, (envelope A B).sigmaClosedAt⟩

/-! ## A constructed successor enclosure -/

/-- The next envelope contains the actual generated code carrier and its
decoded family. Its decoding level is increased because the lower carrier
already lives in `Type (u + 1)`. -/
def successor (A : Type u) (B : A → Type u) :
    ClosedTarskiUniverseOver.{u + 2, u + 1}
      (Code A B) (fun code => ULift.{u + 1, u} code.El) :=
  envelope (Code A B) (fun code => ULift.{u + 1, u} code.El)

/-- Cumulativity into the constructed successor preserves code identity,
even where decoding forgets differences between formation derivations. -/
def successorEmbedding (A : Type u) (B : A → Type u) :
    Code A B ↪ (successor A B).Code where
  toFun := Code.fibre
  inj' := Code.fibre_injective

def decodeSuccessor {A : Type u} {B : A → Type u} (code : Code A B) :
    (successor A B).El (successorEmbedding A B code) ≃ code.El :=
  Equiv.ulift

@[simp] theorem decodeSuccessor_apply {A : Type u} {B : A → Type u}
    (code : Code A B) (value : code.El) :
    decodeSuccessor code (ULift.up value) = value := rfl

/-- Universe formation in the successor has a code for the entire lower
code carrier, in addition to separate lifted codes for its decoded types. -/
def successorCodeCarrier (A : Type u) (B : A → Type u) :
    (successor A B).El (successor A B).baseCode ≃ Code A B :=
  (successor A B).elBase

/-! ## Discriminating generated-code controls -/

namespace Controls

def constantBool : Bool → Type := fun _ => Bool

/-- Different generator occurrences retain their identities despite equal
decoded types. -/
theorem equal_decodings_distinct_fibre_codes :
    (Code.fibre (B := constantBool) false).El =
        (Code.fibre (B := constantBool) true).El ∧
      Code.fibre (B := constantBool) false ≠
        Code.fibre (B := constantBool) true := by
  refine ⟨rfl, ?_⟩
  intro equalCodes
  exact Bool.false_ne_true (Code.fibre_injective equalCodes)

/-- The generated product encloses a nonconstant dependent family. -/
def varyingProduct : Code Bool varyingFamily :=
  Code.pi Code.base (fun index => Code.fibre index)

/-- The varying-family product has one independently selectable Boolean
value, rather than two. -/
def varyingProductEquiv : varyingProduct.El ≃ Bool where
  toFun := fun valueMap => valueMap true
  invFun := fun value index => by
    cases index
    · exact PUnit.unit
    · exact value
  left_inv := by
    intro valueMap
    funext index
    cases index
    · change (PUnit.unit : PUnit) = valueMap false
      exact Subsingleton.elim _ _
    · rfl
  right_inv := fun _ => rfl

/-- Decoding cannot recover the distinct formation occurrences discarded by
this readout. -/
theorem decoder_not_injective :
    ¬ Function.Injective (Code.El : Code Bool constantBool → Type) := by
  intro injective
  exact equal_decodings_distinct_fibre_codes.2
    (injective equal_decodings_distinct_fibre_codes.1)

end Controls

#print axioms Generation.substitute_comp
#print axioms Generation.closed_induction
#print axioms envelope
#print axioms successorEmbedding
#print axioms Controls.varyingProductEquiv
#print axioms Controls.decoder_not_injective

end Mettapedia.TypeTheory.GeneratedFamilyUniverse
