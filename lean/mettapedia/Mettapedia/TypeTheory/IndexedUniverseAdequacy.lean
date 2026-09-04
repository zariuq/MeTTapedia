import Mettapedia.TypeTheory.FamilyEnclosingUniverse

/-!
# Indexed intensional families and extensional universe adequacy

This module isolates two joints needed when a dependent construction language
is interpreted in an extensional universe host.

First, an observer-indexed world has an index `I`, an extensional state family
`P i`, and an intensional family `Q i p`.  Its full state is the dependent total
space `Σ i, Σ p, Q i p`; its extensional readout retains `i` and `p` while
forgetting only the selected fibre element.  This is the precise mathematical
shape behind a P/Q/I comparison.  No identification of phenomenal description,
dependent type theory, or physical ontology is built into the definition.

Second, `FamilyUniverseAdequacy` states the commuting data required to
interpret a family-enclosing Tarski universe in an extensional universe
algebra.  Interpretation is total from codes to host objects.  Reification is
provided only for code-retaining presented objects.  A tagged universe gives a
negative control: two distinct codes may have the same extensional denotation,
so no global left inverse can recover intensional code identity.

Finally, a small finite-support theorem records the honest open-tower promise:
every finite collection of stage requirements has a strict upper stage, while
there is no final natural-number stage.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedUniverseAdequacy

open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe uIndex uState uCode uObject uElement

/-! ## Observer-indexed extensional and intensional state -/

/-- An indexical family with an extensional state at each index and a further
intensional fibre over each indexed state. -/
structure IndexedIntensionalFamily where
  Index : Type uIndex
  Extensional : Index → Type uState
  Intensional : (index : Index) → Extensional index → Type uState

namespace IndexedIntensionalFamily

variable (world : IndexedIntensionalFamily.{uIndex, uState})

/-- The index and extensional state, with the intensional fibre forgotten. -/
abbrev ExtensionalState := Σ index, world.Extensional index

/-- The proof-relevant dependent total space. -/
abbrev IntensionalState :=
  Σ index, Σ state : world.Extensional index, world.Intensional index state

/-- Forget the intensional fibre while retaining both the observer index and
the extensional state. -/
def erase : world.IntensionalState → world.ExtensionalState
  | ⟨index, state, _evidence⟩ => ⟨index, state⟩

/-- Extensionalization preserves the observer/indexical coordinate exactly. -/
theorem erase_preserves_index (state : world.IntensionalState) :
    (world.erase state).1 = state.1 := by
  rfl

/-- If every intensional fibre is inhabited, every indexed extensional state
has at least one intensional realization. -/
theorem erase_surjective_of_fibres_inhabited
    (inhabited : ∀ index state,
      Nonempty (world.Intensional index state)) :
    Function.Surjective world.erase := by
  rintro ⟨index, state⟩
  rcases inhabited index state with ⟨evidence⟩
  exact ⟨⟨index, state, evidence⟩, rfl⟩

/-- Two different inhabitants of one fibre are an exact obstruction to a
faithful extensional readout. -/
theorem erase_not_injective_of_distinct_fibre
    {index : world.Index} {state : world.Extensional index}
    {left right : world.Intensional index state} (different : left ≠ right) :
    ¬ Function.Injective world.erase := by
  intro injective
  have equalStates :
      (⟨index, state, left⟩ : world.IntensionalState) =
        ⟨index, state, right⟩ :=
    injective rfl
  cases equalStates
  exact different rfl

/-- A family-enclosing universe can be selected independently at every
observer index.  The universe encloses the extensional state family and its
genuinely varying intensional fibres. -/
def localUniverse
    (operator : FamilyEnclosingUniverseOperator.{uState})
    (index : world.Index) :
    ClosedTarskiUniverseOver
      (world.Extensional index) (world.Intensional index) :=
  operator.enclose (world.Extensional index) (world.Intensional index)

end IndexedIntensionalFamily

/-! ## An extensional algebra of universe objects -/

/-- The extensional operations that a host must provide in order to interpret
the selected family-universe profile.  `Object` may be a type of sets, objects
of a category, or another extensional carrier; `Elements` exposes its semantic
family. -/
structure ExtensionalUniverseAlgebra where
  Object : Type uObject
  Elements : Object → Type uElement
  empty : Object
  unit : Object
  nat : Object
  sum : Object → Object → Object
  pi : (domain : Object) → (Elements domain → Object) → Object
  sigma : (domain : Object) → (Elements domain → Object) → Object
  identity : (domain : Object) → Elements domain → Elements domain → Object
  w : (shape : Object) → (Elements shape → Object) → Object
  elEmpty : Elements empty ≃ Empty
  elUnit : Elements unit ≃ PUnit.{1}
  elNat : Elements nat ≃ Nat
  elSum : ∀ left right,
    Elements (sum left right) ≃ Sum (Elements left) (Elements right)
  elPi : ∀ domain codomain,
    Elements (pi domain codomain) ≃
      ((argument : Elements domain) → Elements (codomain argument))
  elSigma : ∀ domain codomain,
    Elements (sigma domain codomain) ≃
      (Σ argument : Elements domain, Elements (codomain argument))
  elIdentity : ∀ domain left right,
    Elements (identity domain left right) ≃ (left = right)
  elW : ∀ shape position,
    Elements (w shape position) ≃
      WTree (Elements shape) (fun value => Elements (position value))

/-- Interpretation of native Tarski codes in an extensional universe algebra.
The equations are the constructor-commuting part of the adequacy square.  The
dependent host families are reindexed through `decode` explicitly. -/
structure FamilyUniverseAdequacy
    {A : Type uElement} {B : A → Type uElement}
    (envelope : ClosedTarskiUniverseOver.{uCode, uElement} A B)
    (host : ExtensionalUniverseAlgebra.{uObject, uElement}) where
  denote : envelope.Code → host.Object
  decode : ∀ code, envelope.El code ≃ host.Elements (denote code)
  denoteEmpty : denote envelope.emptyCode = host.empty
  denoteUnit : denote envelope.unitCode = host.unit
  denoteNat : denote envelope.natCode = host.nat
  denoteSum : ∀ left right,
    denote (envelope.sumCode left right) =
      host.sum (denote left) (denote right)
  denotePi : ∀ domain codomain,
    denote (envelope.piCode domain codomain) =
      host.pi (denote domain) fun argument =>
        denote (codomain ((decode domain).symm argument))
  denoteSigma : ∀ domain codomain,
    denote (envelope.sigmaCode domain codomain) =
      host.sigma (denote domain) fun argument =>
        denote (codomain ((decode domain).symm argument))
  denoteIdentity : ∀ domain left right,
    denote (envelope.identityCode domain left right) =
      host.identity (denote domain) (decode domain left) (decode domain right)
  denoteW : ∀ shape position,
    denote (envelope.wCode shape position) =
      host.w (denote shape) fun value =>
        denote (position ((decode shape).symm value))

namespace FamilyUniverseAdequacy

variable {A : Type uElement} {B : A → Type uElement}
variable {envelope : ClosedTarskiUniverseOver.{uCode, uElement} A B}
variable {host : ExtensionalUniverseAlgebra.{uObject, uElement}}
variable (adequacy : FamilyUniverseAdequacy envelope host)

/-- Transport the element family along equality of host objects. -/
def castElements {left right : host.Object} (equal : left = right) :
    host.Elements left ≃ host.Elements right :=
  Equiv.cast (congrArg host.Elements equal)

/-- The sum-code square commutes all the way down to host elements. -/
def sumCommutation (left right : envelope.Code) :
    envelope.El (envelope.sumCode left right) ≃
      Sum (host.Elements (adequacy.denote left))
        (host.Elements (adequacy.denote right)) :=
  (adequacy.decode (envelope.sumCode left right)).trans
    ((castElements (adequacy.denoteSum left right)).trans
      (host.elSum (adequacy.denote left) (adequacy.denote right)))

/-- The dependent-product square commutes, including the change of index from
native decoded arguments to host elements. -/
def piCommutation (domain : envelope.Code)
    (codomain : envelope.El domain → envelope.Code) :
    envelope.El (envelope.piCode domain codomain) ≃
      ((argument : host.Elements (adequacy.denote domain)) →
        host.Elements
          (adequacy.denote
            (codomain ((adequacy.decode domain).symm argument)))) :=
  (adequacy.decode (envelope.piCode domain codomain)).trans
    ((castElements (adequacy.denotePi domain codomain)).trans
      (host.elPi (adequacy.denote domain) fun argument =>
        adequacy.denote
          (codomain ((adequacy.decode domain).symm argument))))

/-- The dependent-sum square commutes with the same explicit reindexing. -/
def sigmaCommutation (domain : envelope.Code)
    (codomain : envelope.El domain → envelope.Code) :
    envelope.El (envelope.sigmaCode domain codomain) ≃
      (Σ argument : host.Elements (adequacy.denote domain),
        host.Elements
          (adequacy.denote
            (codomain ((adequacy.decode domain).symm argument)))) :=
  (adequacy.decode (envelope.sigmaCode domain codomain)).trans
    ((castElements (adequacy.denoteSigma domain codomain)).trans
      (host.elSigma (adequacy.denote domain) fun argument =>
        adequacy.denote
          (codomain ((adequacy.decode domain).symm argument))))

/-- A representable host object together with the native code needed
for computation.  Retaining this witness avoids an arbitrary choice of code. -/
structure CodedObject where
  object : host.Object
  code : envelope.Code
  denotes : adequacy.denote code = object

namespace CodedObject

/-- Reification on the code-retaining representable image. -/
def reify (coded : adequacy.CodedObject) : envelope.Code :=
  coded.code

/-- Forget the code and retain the extensional host object. -/
def forget (coded : adequacy.CodedObject) : host.Object :=
  coded.object

/-- Reification followed by interpretation recovers the represented object. -/
theorem denote_reify (coded : adequacy.CodedObject) :
    adequacy.denote coded.reify = coded.forget :=
  coded.denotes

end CodedObject

end FamilyUniverseAdequacy

/-! ## A semantic host and a nonfaithful tagged-code control -/

/-- Ordinary ambient types form one extensional universe algebra.  This is a
semantic model used to test the adequacy interface; it is not a set-theoretic
or object-syntactic identification. -/
def typeAlgebra : ExtensionalUniverseAlgebra.{uElement + 1, uElement} where
  Object := Type uElement
  Elements := id
  empty := ULift.{uElement, 0} Empty
  unit := ULift.{uElement, 0} PUnit
  nat := ULift.{uElement, 0} Nat
  sum := Sum
  pi := fun domain codomain => (argument : domain) → codomain argument
  sigma := fun domain codomain => Σ argument : domain, codomain argument
  identity := fun _domain left right => ULift.{uElement, 0} (PLift (left = right))
  w := WTree
  elEmpty := Equiv.ulift
  elUnit := Equiv.ulift
  elNat := Equiv.ulift
  elSum := fun left right => Equiv.refl (Sum left right)
  elPi := fun domain codomain =>
    Equiv.refl ((argument : domain) → codomain argument)
  elSigma := fun domain codomain =>
    Equiv.refl (Σ argument : domain, codomain argument)
  elIdentity := fun _domain _left _right => Equiv.ulift.trans Equiv.plift
  elW := fun shape position => Equiv.refl (WTree shape position)

/-- A full family-enclosing universe with an intentionally intensional Boolean
tag on every code.  Decoding ignores the tag. -/
def taggedEnvelope (A : Type uElement) (B : A → Type uElement) :
    ClosedTarskiUniverseOver.{uElement + 1, uElement} A B where
  Code := Bool × Type uElement
  El := fun code => code.2
  baseCode := (false, A)
  elBase := Equiv.refl A
  fibreCode := fun index => (false, B index)
  elFibre := fun index => Equiv.refl (B index)
  emptyCode := (false, ULift.{uElement, 0} Empty)
  elEmpty := Equiv.ulift
  unitCode := (false, ULift.{uElement, 0} PUnit)
  elUnit := Equiv.ulift
  natCode := (false, ULift.{uElement, 0} Nat)
  elNat := Equiv.ulift
  sumCode := fun left right => (false, Sum left.2 right.2)
  elSum := fun left right => Equiv.refl (Sum left.2 right.2)
  piCode := fun domain codomain =>
    (false, (argument : domain.2) → (codomain argument).2)
  elPi := fun domain codomain =>
    Equiv.refl ((argument : domain.2) → (codomain argument).2)
  sigmaCode := fun domain codomain =>
    (false, Σ argument : domain.2, (codomain argument).2)
  elSigma := fun domain codomain =>
    Equiv.refl (Σ argument : domain.2, (codomain argument).2)
  identityCode := fun _domain left right =>
    (false, ULift.{uElement, 0} (PLift (left = right)))
  elIdentity := fun _domain _left _right => Equiv.ulift.trans Equiv.plift
  wCode := fun shape position =>
    (false, WTree shape.2 fun value => (position value).2)
  elW := fun shape position =>
    Equiv.refl (WTree shape.2 fun value => (position value).2)

/-- Erasing the Boolean code tag is an adequacy interpretation into the
ambient extensional type algebra, and all constructor squares commute. -/
def taggedAdequacy (A : Type uElement) (B : A → Type uElement) :
    FamilyUniverseAdequacy (taggedEnvelope A B) typeAlgebra where
  denote := Prod.snd
  decode := fun code => Equiv.refl code.2
  denoteEmpty := rfl
  denoteUnit := rfl
  denoteNat := rfl
  denoteSum := fun _ _ => rfl
  denotePi := fun _ _ => rfl
  denoteSigma := fun _ _ => rfl
  denoteIdentity := fun _ _ _ => rfl
  denoteW := fun _ _ => rfl

/-- Negative control: interpretation of a valid universe algebra need not be
faithful on intensional codes. -/
theorem tagged_denote_not_injective (A : Type uElement)
    (B : A → Type uElement) :
    ¬ Function.Injective (taggedAdequacy A B).denote := by
  intro injective
  let carrier : Type uElement := ULift.{uElement, 0} PUnit
  have equalCodes :
      ((false, carrier) : (taggedEnvelope A B).Code) =
        (true, carrier) :=
    injective rfl
  have equalTags := congrArg Prod.fst equalCodes
  simp at equalTags

/-- Hence there is no total reifier which is a left inverse to the tagged
interpretation.  Reverse passage is lawful only on a code-retaining or
otherwise independently definable image. -/
theorem no_global_tag_reification (A : Type uElement)
    (B : A → Type uElement) :
    ¬ ∃ reify : typeAlgebra.Object → (taggedEnvelope A B).Code,
      Function.LeftInverse reify (taggedAdequacy A B).denote := by
  rintro ⟨reify, leftInverse⟩
  exact tagged_denote_not_injective A B leftInverse.injective

/-! ## A concrete indexed non-collapse canary -/

namespace Canary

/-- Two observer positions share the same visible carrier; one position has a
nontrivial intensional fibre. -/
def indexedWorld : IndexedIntensionalFamily where
  Index := Bool
  Extensional := fun _ => PUnit
  Intensional := fun index _ => if index then Bool else PUnit

theorem indexedWorld_fibres_inhabited :
    ∀ index state, Nonempty (indexedWorld.Intensional index state) := by
  intro index state
  cases index
  · exact ⟨PUnit.unit⟩
  · exact ⟨false⟩

theorem indexedWorld_erase_surjective :
    Function.Surjective indexedWorld.erase :=
  indexedWorld.erase_surjective_of_fibres_inhabited
    indexedWorld_fibres_inhabited

theorem indexedWorld_erase_not_injective :
    ¬ Function.Injective indexedWorld.erase := by
  apply indexedWorld.erase_not_injective_of_distinct_fibre
    (index := true) (state := PUnit.unit)
    (left := false) (right := true)
  exact Bool.false_ne_true

/-- Every observer position in the non-collapse example receives its own
closed family-enclosing universe. -/
def indexedWorldUniverses (index : indexedWorld.Index) :
    ClosedTarskiUniverseOver
      (indexedWorld.Extensional index) (indexedWorld.Intensional index) :=
  indexedWorld.localUniverse ambientOperator index

end Canary

/-! ## Finite support and open ascent -/

/-- A strict host stage for a finite list of required natural-number stages. -/
def nextStage : List Nat → Nat
  | [] => 0
  | stage :: rest => max (stage + 1) (nextStage rest)

/-- Every requirement in a finite task lies strictly below `nextStage`. -/
theorem mem_lt_nextStage {requirements : List Nat} {stage : Nat}
    (member : stage ∈ requirements) :
    stage < nextStage requirements := by
  induction requirements with
  | nil => simp at member
  | cons first tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      simp only [nextStage]
      rcases member with rfl | member
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
      · exact lt_of_lt_of_le (inductionHypothesis member) (Nat.le_max_right ..)

/-- Every finite metareasoning task therefore has a strict later host stage. -/
theorem finite_support_has_strict_host (requirements : List Nat) :
    ∃ host : Nat, ∀ stage ∈ requirements, stage < host :=
  ⟨nextStage requirements, fun _stage member => mem_lt_nextStage member⟩

/-- The natural-number tower has no final stage.  Open ascent is a schema of
arbitrarily extendable finite stages, not one same-level self-containing type. -/
theorem no_final_stage : ¬ ∃ final : Nat, ∀ stage : Nat, stage ≤ final := by
  rintro ⟨final, maximal⟩
  exact Nat.not_succ_le_self final (maximal (final + 1))

#print axioms IndexedIntensionalFamily.erase_surjective_of_fibres_inhabited
#print axioms IndexedIntensionalFamily.erase_not_injective_of_distinct_fibre
#print axioms FamilyUniverseAdequacy.sumCommutation
#print axioms FamilyUniverseAdequacy.piCommutation
#print axioms FamilyUniverseAdequacy.sigmaCommutation
#print axioms FamilyUniverseAdequacy.CodedObject.denote_reify
#print axioms tagged_denote_not_injective
#print axioms no_global_tag_reification
#print axioms Canary.indexedWorld_erase_surjective
#print axioms Canary.indexedWorld_erase_not_injective
#print axioms mem_lt_nextStage
#print axioms finite_support_has_strict_host
#print axioms no_final_stage

end Mettapedia.TypeTheory.IndexedUniverseAdequacy
