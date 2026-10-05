import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LiftedFamilyModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLiftCoherence
import Mettapedia.TypeTheory.GeneratedFamilyUniverse

/-!
# Constructed material decoder for the generated dependent core

Every derivation in the dependent core grammar receives an actual material
graph, an explicitly constructed member equivalence, and uniform term graphs.
Dependent products, sums, discrete equality fibres and W-types all preserve
the common graph bound, including arbitrarily nested nonconstant families.
The interpretation is stable under substitution of the generating family.

For arbitrary original `HSet.{u}` families the common graph bound is `u + 1`.
The construction of their initial presentations uses the uniform universe
lift, not a section of the quotient map at level `u`. The generated code
carrier lives one level above its decoded types; collecting all interpreted
type values therefore takes another material level.

This core embeds into the broader semantic grammar. Its host binary-sum and
natural-number conveniences are not assigned stronger decoding rules here.
Identity remains the discrete equality interpretation, not a rule imposing
identity reflection or proof irrelevance on another calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialDecoder

open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open Mettapedia.TypeTheory.GeneratedFamilyUniverse
open LiftedFamilyModel (Elements)

universe u

/-- The dependent core keeps its entire formation derivation. Its Pi, Sigma
and W premises range over arbitrary families of recursively generated types. -/
inductive CoreGeneration (A : Type u) (B : A → Type u) : Type u → Type (u + 1) where
  | base : CoreGeneration A B A
  | fibre (index : A) : CoreGeneration A B (B index)
  | empty : CoreGeneration A B (ULift.{u, 0} Empty)
  | unit : CoreGeneration A B (ULift.{u, 0} PUnit)
  | pi {X : Type u} {Y : X → Type u} (domain : CoreGeneration A B X)
      (codomain : (x : X) → CoreGeneration A B (Y x)) : CoreGeneration A B ((x : X) → Y x)
  | sigma {X : Type u} {Y : X → Type u} (domain : CoreGeneration A B X)
      (codomain : (x : X) → CoreGeneration A B (Y x)) : CoreGeneration A B (Sigma Y)
  | identity {X : Type u} (domain : CoreGeneration A B X) (left right : X) :
      CoreGeneration A B (ULift.{u, 0} (PLift (left = right)))
  | w {X : Type u} {Y : X → Type u} (shape : CoreGeneration A B X)
      (position : (x : X) → CoreGeneration A B (Y x)) : CoreGeneration A B (WTree X Y)

namespace CoreGeneration

variable {A C : Type u} {B : A → Type u} {D : C → Type u}

/-- The core interpretation covers actual derivations of the original semantic
grammar, with no change to their decoded type. -/
def toSemantic : {T : Type u} → CoreGeneration A B T → Generation A B T
  | _, .base => .base
  | _, .fibre a => .fibre a
  | _, .empty => .empty
  | _, .unit => .unit
  | _, .pi domain codomain => .pi domain.toSemantic (fun x => (codomain x).toSemantic)
  | _, .sigma domain codomain => .sigma domain.toSemantic (fun x => (codomain x).toSemantic)
  | _, .identity domain left right => .identity domain.toSemantic left right
  | _, .w shape position => .w shape.toSemantic (fun x => (position x).toSemantic)

def substitute (baseDerivation : CoreGeneration C D A)
    (fibres : (a : A) → CoreGeneration C D (B a)) :
    {T : Type u} → CoreGeneration A B T → CoreGeneration C D T
  | _, .base => baseDerivation
  | _, .fibre a => fibres a
  | _, .empty => .empty
  | _, .unit => .unit
  | _, .pi domain codomain =>
      .pi (substitute baseDerivation fibres domain) (fun x => substitute baseDerivation fibres (codomain x))
  | _, .sigma domain codomain =>
      .sigma (substitute baseDerivation fibres domain) (fun x => substitute baseDerivation fibres (codomain x))
  | _, .identity domain left right => .identity (substitute baseDerivation fibres domain) left right
  | _, .w shape position =>
      .w (substitute baseDerivation fibres shape) (fun x => substitute baseDerivation fibres (position x))

theorem substitute_id {T : Type u} (derivation : CoreGeneration A B T) :
    substitute .base .fibre derivation = derivation := by
  induction derivation <;> simp_all [substitute]

theorem substitute_comp {E : Type u} {F : E → Type u}
    (firstBase : CoreGeneration C D A) (firstFibres : (a : A) → CoreGeneration C D (B a))
    (secondBase : CoreGeneration E F C) (secondFibres : (c : C) → CoreGeneration E F (D c))
    {T : Type u} (derivation : CoreGeneration A B T) :
    substitute secondBase secondFibres (substitute firstBase firstFibres derivation) =
      substitute (substitute secondBase secondFibres firstBase)
        (fun a => substitute secondBase secondFibres (firstFibres a)) derivation := by
  induction derivation <;> simp_all [substitute]

theorem toSemantic_substitute (baseDerivation : CoreGeneration C D A)
    (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (substitute baseDerivation fibres derivation).toSemantic =
      Generation.substitute baseDerivation.toSemantic (fun a => (fibres a).toSemantic) derivation.toSemantic := by
  induction derivation <;> simp_all [substitute, toSemantic, Generation.substitute]

/-- Each branch uses a constructed same-bound material operation. This is
recursion through the whole dependent grammar, not a seed-only comparison. -/
def interpret (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a)) :
    {T : Type u} → CoreGeneration A B T → PresentedType T
  | _, .base => baseModel
  | _, .fibre a => fibreModels a
  | _, .empty => PresentedType.empty
  | _, .unit => PresentedType.unit
  | _, .pi domain codomain =>
      PresentedType.product (domain.interpret baseModel fibreModels)
        (fun x => (codomain x).interpret baseModel fibreModels)
  | _, .sigma domain codomain =>
      PresentedType.sum (domain.interpret baseModel fibreModels)
        (fun x => (codomain x).interpret baseModel fibreModels)
  | _, .identity domain left right =>
      PresentedType.identity (domain.interpret baseModel fibreModels) left right
  | _, .w shape position =>
      PresentedType.W.model (shape.interpret baseModel fibreModels)
        (fun x => (position x).interpret baseModel fibreModels)

/-- Substitution commutes with the actual graphs and both decoding operations,
including every nonconstant dependent family branch. -/
theorem interpret_substitute (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (substitute baseDerivation fibres derivation).interpret baseModel fibreModels =
      derivation.interpret (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) := by
  induction derivation <;> simp_all [substitute, interpret]

theorem termGraph_substitute (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) (term : T) :
    ((substitute baseDerivation fibres derivation).interpret baseModel fibreModels).termGraph term =
      (derivation.interpret (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels)).termGraph term :=
  congrArg (fun model => model.termGraph term) (interpret_substitute baseModel fibreModels baseDerivation fibres derivation)

theorem value_substitute (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) (term : T) :
    ((substitute baseDerivation fibres derivation).interpret baseModel fibreModels).value term =
      (derivation.interpret (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels)).value term :=
  congrArg (fun model => model.value term) (interpret_substitute baseModel fibreModels baseDerivation fibres derivation)

theorem decode_substitute (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u} // value ∈
      ((substitute baseDerivation fibres derivation).interpret baseModel fibreModels).carrier}) :
    (derivation.interpret (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels)).decode
      (PresentedType.transportMember (interpret_substitute baseModel fibreModels baseDerivation fibres derivation) member) =
      ((substitute baseDerivation fibres derivation).interpret baseModel fibreModels).decode member :=
  PresentedType.decode_transportMember (interpret_substitute baseModel fibreModels baseDerivation fibres derivation) member

end CoreGeneration

/-- Uniformly present original members at the one raised graph bound. Both
directions retain the original material value and membership proof. -/
def liftedModel (X : HSet.{u}) : PresentedType (Elements X) where
  graph := HSet.presentationUp X
  decode := {
    toFun := fun member => ⟨HSet.lowerMemberValue X member.1,
      HSet.lowerMemberValue_mem (HSet.mk_presentationUp X ▸ member.2)⟩
    invFun := fun original => ⟨HSet.lift original.1,
      (HSet.mk_presentationUp X).symm ▸ HSet.lift_mem_lift_iff.mpr original.2⟩
    left_inv := fun member => Subtype.ext (HSet.lift_lowerMemberValue
      (HSet.mk_presentationUp X ▸ member.2))
    right_inv := fun original => El.ext HSet.propositional (HSet.lowerMemberValue_lift original.2) }

theorem liftedModel_value (X : HSet.{u}) (member : Elements X) :
    (liftedModel X).value member = HSet.lift member.1 := rfl

/-- An arbitrary bare material family supplies all initial model data by
construction. No graph selector, small section carrier or decoder is assumed. -/
def interpretFamily (X : HSet.{u}) (B : Elements X → HSet.{u}) {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) : PresentedType T :=
  derivation.interpret (liftedModel X) (fun a => liftedModel (B a))

def typeValue (X : HSet.{u}) (B : Elements X → HSet.{u}) {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) : HSet.{u + 1} :=
  (interpretFamily X B derivation).carrier

def termGraph {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) (term : T) :
    AccessiblePointedGraph.{u + 1} := (interpretFamily X B derivation).termGraph term

theorem mk_termGraph {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) (term : T) :
    HSet.mk (termGraph derivation term) = (interpretFamily X B derivation).value term :=
  PresentedType.mk_termGraph _ _

/-- The whole generated core has an actual member equivalence at its common
material bound. The inverse is the authored material encoding of each term. -/
def decode {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) :
    {value : HSet.{u + 1} // value ∈ typeValue X B derivation} ≃ T :=
  (interpretFamily X B derivation).decode

theorem decode_encode {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) (term : T) :
    decode derivation ((decode derivation).symm term) = term :=
  (decode derivation).apply_symm_apply term

theorem encode_decode {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T)
    (member : {value : HSet.{u + 1} // value ∈ typeValue X B derivation}) :
    (decode derivation).symm (decode derivation member) = member := (decode derivation).symm_apply_apply member

abbrev CoreCode (A : Type u) (B : A → Type u) := Σ T : Type u, CoreGeneration A B T

def semanticCode {A : Type u} {B : A → Type u} (code : CoreCode A B) : Code A B :=
  ⟨code.1, code.2.toSemantic⟩

def modelEnclosure {A : Type u} {B : A → Type u}
    (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a)) : HSet.{u + 1} :=
  HSet.imageUp fun code : CoreCode A B => (code.2.interpret baseModel fibreModels).carrier

theorem mem_modelEnclosure_iff {A : Type u} {B : A → Type u}
    {baseModel : PresentedType A} {fibreModels : (a : A) → PresentedType (B a)} {value : HSet.{u + 1}} :
    value ∈ modelEnclosure baseModel fibreModels ↔
      ∃ code : CoreCode A B, HSet.lift (code.2.interpret baseModel fibreModels).carrier = value :=
  HSet.mem_imageUp_iff

/-- Replacing generators by actual derivations yields an inclusion of their
material enclosures. Every translated code has literally the same graph and
decoder by the structural interpretation-substitution theorem. -/
theorem modelEnclosure_substitute_subset {A C : Type u} {B : A → Type u} {D : C → Type u}
    (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a)) :
    modelEnclosure (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) ⊆ modelEnclosure baseModel fibreModels := by
  intro value member
  obtain ⟨⟨T, derivation⟩, same⟩ := mem_modelEnclosure_iff.mp member
  apply mem_modelEnclosure_iff.mpr
  refine ⟨⟨T, CoreGeneration.substitute baseDerivation fibres derivation⟩, ?_⟩
  exact (congrArg (fun model => HSet.lift model.carrier)
    (CoreGeneration.interpret_substitute baseModel fibreModels baseDerivation fibres derivation)).trans same

/-- The material carrier of every generated core decoding is collected at
the next bound. This is a constructed enclosing set, not a universal-set rule. -/
def codeEnclosure (X : HSet.{u}) (B : Elements X → HSet.{u}) : HSet.{u + 2} :=
  modelEnclosure (liftedModel X) (fun a => liftedModel (B a))

theorem mem_codeEnclosure_iff {X : HSet.{u}} {B : Elements X → HSet.{u}} {value : HSet.{u + 2}} :
    value ∈ codeEnclosure X B ↔
      ∃ code : CoreCode (Elements X) (fun a => Elements (B a)), HSet.lift (typeValue X B code.2) = value :=
  HSet.mem_imageUp_iff

theorem generated_type_enclosed {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) :
    HSet.lift (typeValue X B derivation) ∈ codeEnclosure X B :=
  mem_codeEnclosure_iff.mpr ⟨⟨T, derivation⟩, rfl⟩

theorem generated_members_small {X : HSet.{u}} {B : Elements X → HSet.{u}} {T : Type (u + 1)}
    (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T) :
    Small.{u + 1} {value : HSet.{u + 1} // value ∈ typeValue X B derivation} := Small.mk' (decode derivation)

/-! ## Nested dependent controls -/

/-- Pi of Sigma of discrete identity is an actual nested derivation. Its
codomain retains the material fibre selected by each domain member. -/
def pairedIdentitySections (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    CoreGeneration (Elements X) (fun a => Elements (B a))
      ((a : Elements X) → Σ b : Elements (B a), ULift.{u + 1, 0} (PLift (b = b))) :=
  .pi .base (fun a => .sigma (.fibre a) (fun b : Elements (B a) =>
    CoreGeneration.identity (B := fun a => Elements (B a)) (.fibre a) b b))

def singletonFamily {X : HSet.{u}} (a : Elements X) : HSet.{u} := {a.1}

def singletonIdentitySection (X : HSet.{u}) :
    (a : Elements X) → Σ b : Elements (singletonFamily a), ULift.{u + 1, 0} (PLift (b = b)) :=
  fun a => ⟨⟨a.1, HSet.mem_singleton_self _⟩, ⟨⟨rfl⟩⟩⟩

/-- The nonconstant singleton family keeps both actual material observations
in the nested function row, while the equality witness has value empty. -/
theorem singletonIdentitySection_entry (X : HSet.{u}) (a : Elements X) :
    HSet.kpair (HSet.lift a.1) (HSet.kpair (HSet.lift a.1) ∅) ∈
      (interpretFamily X singletonFamily (pairedIdentitySections X singletonFamily)).value
        (singletonIdentitySection X) := by
  have entry := PresentedType.product_entry (liftedModel X)
    (fun a => PresentedType.sum (liftedModel (singletonFamily a))
      (fun b => PresentedType.identity (liftedModel (singletonFamily a)) b b))
    (singletonIdentitySection X) a
  simpa only [interpretFamily, pairedIdentitySections, CoreGeneration.interpret,
    PresentedType.sum_value, liftedModel_value, PresentedType.identity_value, singletonIdentitySection]
    using entry

/-- This nested decoder preserves an actual cyclic material value. -/
theorem quine_nested_entry :
    HSet.kpair HSet.quineAtom.{u + 1} (HSet.kpair HSet.quineAtom ∅) ∈
      (interpretFamily ({HSet.quineAtom.{u}} : HSet.{u}) singletonFamily
        (pairedIdentitySections {HSet.quineAtom} singletonFamily)).value
        (singletonIdentitySection {HSet.quineAtom}) := by
  simpa only [HSet.lift_quineAtom] using
    singletonIdentitySection_entry ({HSet.quineAtom.{u}} : HSet.{u})
      ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩

/-- A nested Sigma cannot manufacture a value in an empty fibre, and the
surrounding Pi cannot supply such a value at a nonempty domain member. -/
theorem pairedIdentitySections_empty_of_empty_fibre {X : HSet.{u}}
    {B : Elements X → HSet.{u}} (a : Elements X) (empty : B a = ∅) :
    typeValue X B (pairedIdentitySections X B) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  have result := decode (pairedIdentitySections X B) ⟨value, member⟩ a
  exact HSet.notMem_empty result.1.1 (empty ▸ result.1.2)

/-- Generated W with identity-as-position has a branch at every shape.
The material interpretation therefore has no well-founded tree. -/
def identityPositions (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    CoreGeneration (Elements X) (fun a => Elements (B a))
      (WTree (Elements X) (fun a => ULift.{u + 1, 0} (PLift (a = a)))) :=
  .w .base (fun a => .identity .base a a)

theorem identityPositions_empty (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    typeValue X B (identityPositions X B) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  have tree := decode (identityPositions X B) ⟨value, member⟩
  induction tree with
  | sup _ _ earlier => exact earlier ⟨⟨rfl⟩⟩

theorem generated_identity_empty_of_distinct {X : HSet.{u}} {B : Elements X → HSet.{u}}
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (B a)) T)
    (left right : T) (different : left ≠ right) :
    typeValue X B (.identity derivation left right) = ∅ :=
  PresentedType.identity_empty_of_distinct (interpretFamily X B derivation) left right different

/-- The constructed code enclosure still has a concrete absent Russell
value; generating all these types does not create a universal set. -/
theorem codeEnclosure_russell_notMem (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    HSet.russell (codeEnclosure X B) ∉ codeEnclosure X B := HSet.russell_notMem _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialDecoder
