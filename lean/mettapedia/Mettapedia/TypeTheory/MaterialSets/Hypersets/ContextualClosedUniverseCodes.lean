import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes
import Mathlib.Data.Quot

/-!
# Constructor-closed formation codes

The raw data are actual contextual families and their formation derivations.
The declared relation adds constructor congruence to the previously proved
base-substitution equations. It does not identify arbitrary equal families,
carrier values, or derivations. Semantic soundness is proved before decoding.

Dependent quotient eliminators construct Pi, Sigma, identity and W codes
from actual input codes. No formation derivation is selected from Nonempty.
A dependent body remains over its domain's actual comprehension context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev RawCode (context : LabelledContext C) := ContextualGeneratedUniverse.Code seeds seedModel arrows context

inductive BinaryFormation where
  | pi | sigma | w

def materialBinary (kind : BinaryFormation) {context : LabelledContext C}
    (domain : MaterialFamily context) (body : MaterialFamily domain.extension) : MaterialFamily context :=
  match kind with
  | .pi => domain.pi body arrows
  | .sigma => domain.sigma body
  | .w => domain.w body arrows

def generationBinary (kind : BinaryFormation) {context : LabelledContext C}
    {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
    (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body) :
    Generation seeds seedModel arrows (materialBinary arrows kind domain body) :=
  match kind with
  | .pi => Generation.pi first second
  | .sigma => Generation.sigma first second
  | .w => Generation.w first second

def rawBinary (kind : BinaryFormation) {context : LabelledContext C}
    (domain : RawCode seeds seedModel arrows context)
    (body : RawCode seeds seedModel arrows domain.1.extension) : RawCode seeds seedModel arrows context :=
  ⟨materialBinary arrows kind domain.1 body.1, generationBinary seeds seedModel arrows kind domain.2 body.2⟩

def rawIdentity {context : LabelledContext C} (domain : RawCode seeds seedModel arrows context)
    (left right : domain.1.family.sections) : RawCode seeds seedModel arrows context :=
  ⟨domain.1.identity left right, Generation.identity domain.2 left right⟩


inductive UnderFormation where
  | pi | sigma

def materialUnder (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base)
    (domain : MaterialFamily context) (body : MaterialFamily domain.extension) : MaterialFamily other :=
  match kind with
  | .pi => domain.piUnder body arrows change
  | .sigma => domain.sigmaUnder body change

def generationUnder (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base)
    {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
    (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body) :
    Generation seeds seedModel arrows (materialUnder arrows kind change domain body) :=
  match kind with
  | .pi => Generation.piUnder first second change
  | .sigma => Generation.sigmaUnder first second change

def rawUnder (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (domain : RawCode seeds seedModel arrows context)
    (body : RawCode seeds seedModel arrows domain.1.extension) : RawCode seeds seedModel arrows other :=
  ⟨materialUnder arrows kind change domain.1 body.1,
    generationUnder seeds seedModel arrows kind change domain.2 body.2⟩

/-- Constructor congruence retains related derivations. Equal semantic family
values alone are never a constructor of this relation. The dependent bodies
in binary congruence have the same actual comprehension context. -/
inductive Equation : {context : LabelledContext C} →
    RawCode seeds seedModel arrows context → RawCode seeds seedModel arrows context → Prop where
  | substitution {context} {first second : RawCode seeds seedModel arrows context}
      (related : ContextualUniverseCodes.Equation seeds seedModel arrows first second) : Equation first second
  | refl {context} (raw : RawCode seeds seedModel arrows context) : Equation raw raw
  | symm {context} {first second : RawCode seeds seedModel arrows context}
      (related : Equation first second) : Equation second first
  | trans {context} {first middle last : RawCode seeds seedModel arrows context}
      (earlier : Equation first middle) (later : Equation middle last) : Equation first last
  | reindex_congr {context other : LabelledContext C} {first second : RawCode seeds seedModel arrows context}
      (change : NatTrans other.base context.base) (related : Equation first second) :
      Equation (ContextualUniverseCodes.rawReindex seeds seedModel arrows change first)
        (ContextualUniverseCodes.rawReindex seeds seedModel arrows change second)
  | binary_congr {context : LabelledContext C} (kind : BinaryFormation) {domain : MaterialFamily context}
      {first second : Generation seeds seedModel arrows domain}
      {left right : RawCode seeds seedModel arrows domain.extension}
      (domains : Equation ⟨domain, first⟩ ⟨domain, second⟩) (bodies : Equation left right) :
      Equation (rawBinary seeds seedModel arrows kind ⟨domain, first⟩ left)
        (rawBinary seeds seedModel arrows kind ⟨domain, second⟩ right)
  | identity_congr {context : LabelledContext C} {domain : MaterialFamily context}
      {first second : Generation seeds seedModel arrows domain}
      (domains : Equation ⟨domain, first⟩ ⟨domain, second⟩) (left right : domain.family.sections) :
      Equation (rawIdentity seeds seedModel arrows ⟨domain, first⟩ left right)
        (rawIdentity seeds seedModel arrows ⟨domain, second⟩ left right)
  | under_congr {context other : LabelledContext C} (kind : UnderFormation)
      (change : NatTrans other.base context.base) {domain : MaterialFamily context}
      {first second : Generation seeds seedModel arrows domain}
      {left right : RawCode seeds seedModel arrows domain.extension}
      (domains : Equation ⟨domain, first⟩ ⟨domain, second⟩) (bodies : Equation left right) :
      Equation (rawUnder seeds seedModel arrows kind change ⟨domain, first⟩ left)
        (rawUnder seeds seedModel arrows kind change ⟨domain, second⟩ right)

namespace Equation

theorem sound {context : LabelledContext C} {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) : first.1 = second.1 := by
  induction related with
  | substitution related => exact ContextualUniverseCodes.Equation.sound seeds seedModel arrows related
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex_congr change _ ih => exact congrArg (fun family => family.reindex change) ih
  | binary_congr kind _ _ _ bodySound => exact congrArg (materialBinary arrows kind _) bodySound
  | identity_congr => rfl
  | under_congr kind change _ _ _ bodySound => exact congrArg (materialUnder arrows kind change _) bodySound

end Equation

def codeSetoid (context : LabelledContext C) : Setoid (RawCode seeds seedModel arrows context) where
  r := Equation seeds seedModel arrows
  iseqv := ⟨Equation.refl, Equation.symm, Equation.trans⟩

def Code (context : LabelledContext C) : Type (u + 1) := Quotient (codeSetoid seeds seedModel arrows context)

def ofRaw {context : LabelledContext C} (raw : RawCode seeds seedModel arrows context) :
    Code seeds seedModel arrows context := Quotient.mk (codeSetoid seeds seedModel arrows context) raw

def decodeFamily {context : LabelledContext C} : Code seeds seedModel arrows context → MaterialFamily context :=
  Quotient.lift Sigma.fst (fun _ _ related => Equation.sound seeds seedModel arrows related)

theorem decodeFamily_ofRaw {context : LabelledContext C} (raw : RawCode seeds seedModel arrows context) :
    decodeFamily seeds seedModel arrows (ofRaw seeds seedModel arrows raw) = raw.1 := rfl

theorem ofRaw_eq_iff {context : LabelledContext C} (first second : RawCode seeds seedModel arrows context) :
    ofRaw seeds seedModel arrows first = ofRaw seeds seedModel arrows second ↔
      Equation seeds seedModel arrows first second :=
  ⟨fun same => Quotient.exact same,
    fun related => @Quotient.sound _ (codeSetoid seeds seedModel arrows context) first second related⟩

/-- The narrower substitution quotient maps to the constructor-closed code
quotient. Its formation data are retained through the quotient map. -/
def fromSubstitutionCode {context : LabelledContext C} :
    ContextualUniverseCodes.Code seeds seedModel arrows context → Code seeds seedModel arrows context :=
  Quotient.map id (fun _ _ related => Equation.substitution related)

theorem decode_fromSubstitutionCode {context : LabelledContext C}
    (code : ContextualUniverseCodes.Code seeds seedModel arrows context) :
    decodeFamily seeds seedModel arrows (fromSubstitutionCode seeds seedModel arrows code) =
      ContextualUniverseCodes.decodeFamily seeds seedModel arrows code := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl

def binaryFromRaw (kind : BinaryFormation) {context : LabelledContext C}
    (domain : RawCode seeds seedModel arrows context) :
    Code seeds seedModel arrows domain.1.extension → Code seeds seedModel arrows context :=
  Quotient.lift (fun body => ofRaw seeds seedModel arrows (rawBinary seeds seedModel arrows kind domain body))
    (fun _ _ related => Quotient.sound (Equation.binary_congr kind (Equation.refl domain) related))

theorem binaryFromRaw_congr (kind : BinaryFormation) {context : LabelledContext C}
    {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) :
    HEq (binaryFromRaw seeds seedModel arrows kind first) (binaryFromRaw seeds seedModel arrows kind second) := by
  have semantic := Equation.sound seeds seedModel arrows related
  rcases first with ⟨domain, first⟩
  rcases second with ⟨other, second⟩
  dsimp only at semantic
  cases semantic
  apply heq_of_eq
  funext body
  induction body using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.binary_congr kind related (Equation.refl raw))

/-- The outer dependent eliminator accounts for the changing actual
comprehension context. The inner quotient eliminator constructs the body
formation directly. No existence proof is decoded to a derivation. -/
def binary (kind : BinaryFormation) {context : LabelledContext C}
    (domain : Code seeds seedModel arrows context) :
    Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension →
      Code seeds seedModel arrows context :=
  Quotient.hrecOn' (φ := fun code =>
    Code seeds seedModel arrows (decodeFamily seeds seedModel arrows code).extension →
      Code seeds seedModel arrows context) domain
    (fun raw => binaryFromRaw seeds seedModel arrows kind raw)
    (fun _ _ related => binaryFromRaw_congr seeds seedModel arrows kind related)

def pi {context : LabelledContext C} (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context := binary seeds seedModel arrows .pi domain body

def sigma {context : LabelledContext C} (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context := binary seeds seedModel arrows .sigma domain body

def w {context : LabelledContext C} (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context := binary seeds seedModel arrows .w domain body

theorem binary_ofRaw (kind : BinaryFormation) {context : LabelledContext C}
    (domain : RawCode seeds seedModel arrows context) (body : RawCode seeds seedModel arrows domain.1.extension) :
    binary seeds seedModel arrows kind (ofRaw seeds seedModel arrows domain) (ofRaw seeds seedModel arrows body) =
      ofRaw seeds seedModel arrows (rawBinary seeds seedModel arrows kind domain body) := rfl

theorem decode_binary (kind : BinaryFormation) {context : LabelledContext C}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    decodeFamily seeds seedModel arrows (binary seeds seedModel arrows kind domain body) =
      materialBinary arrows kind (decodeFamily seeds seedModel arrows domain)
        (decodeFamily seeds seedModel arrows body) := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  rfl

def identityFromRaw {context : LabelledContext C} (domain : RawCode seeds seedModel arrows context) :
    domain.1.family.sections → domain.1.family.sections → Code seeds seedModel arrows context :=
  fun left right => ofRaw seeds seedModel arrows (rawIdentity seeds seedModel arrows domain left right)

theorem identityFromRaw_congr {context : LabelledContext C}
    {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) :
    HEq (identityFromRaw seeds seedModel arrows first) (identityFromRaw seeds seedModel arrows second) := by
  have semantic := Equation.sound seeds seedModel arrows related
  rcases first with ⟨domain, first⟩
  rcases second with ⟨other, second⟩
  dsimp only at semantic
  cases semantic
  apply heq_of_eq
  funext left right
  exact Quotient.sound (Equation.identity_congr related left right)

def identity {context : LabelledContext C} (domain : Code seeds seedModel arrows context) :
    (decodeFamily seeds seedModel arrows domain).family.sections →
      (decodeFamily seeds seedModel arrows domain).family.sections → Code seeds seedModel arrows context :=
  Quotient.hrecOn' (φ := fun code =>
    (decodeFamily seeds seedModel arrows code).family.sections →
      (decodeFamily seeds seedModel arrows code).family.sections → Code seeds seedModel arrows context) domain
    (identityFromRaw seeds seedModel arrows)
    (fun _ _ related => identityFromRaw_congr seeds seedModel arrows related)

theorem decode_identity {context : LabelledContext C} (domain : Code seeds seedModel arrows context)
    (left right : (decodeFamily seeds seedModel arrows domain).family.sections) :
    decodeFamily seeds seedModel arrows (identity seeds seedModel arrows domain left right) =
      (decodeFamily seeds seedModel arrows domain).identity left right := by
  revert left right
  refine Quotient.inductionOn domain ?_
  intro raw left right
  rfl

def reindex {context other : LabelledContext C} (change : NatTrans other.base context.base) :
    Code seeds seedModel arrows context → Code seeds seedModel arrows other :=
  Quotient.map (ContextualUniverseCodes.rawReindex seeds seedModel arrows change)
    (fun _ _ related => Equation.reindex_congr change related)

theorem reindex_identity {context : LabelledContext C} (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity context.base) code = code := by
  induction code using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.substitution (ContextualUniverseCodes.Equation.reindex_identity raw))

theorem reindex_comp {context middle other : LabelledContext C}
    (earlier : NatTrans other.base middle.base) (later : NatTrans middle.base context.base)
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows earlier (reindex seeds seedModel arrows later code) =
      reindex seeds seedModel arrows (compose earlier later) code := by
  induction code using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.substitution (ContextualUniverseCodes.Equation.reindex_comp raw earlier later))

theorem decode_reindex {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context) :
    decodeFamily seeds seedModel arrows (reindex seeds seedModel arrows change code) =
      (decodeFamily seeds seedModel arrows code).reindex change := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl



def underFromRaw (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (domain : RawCode seeds seedModel arrows context) :
    Code seeds seedModel arrows domain.1.extension → Code seeds seedModel arrows other :=
  Quotient.lift (fun body => ofRaw seeds seedModel arrows (rawUnder seeds seedModel arrows kind change domain body))
    (fun _ _ related => Quotient.sound (Equation.under_congr kind change (Equation.refl domain) related))

theorem underFromRaw_congr (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base) {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) :
    HEq (underFromRaw seeds seedModel arrows kind change first)
      (underFromRaw seeds seedModel arrows kind change second) := by
  have semantic := Equation.sound seeds seedModel arrows related
  rcases first with ⟨domain, first⟩
  rcases second with ⟨otherDomain, second⟩
  dsimp only at semantic
  cases semantic
  apply heq_of_eq
  funext body
  induction body using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.under_congr kind change related (Equation.refl raw))

/-- Transported formation is constructed independently from its own raw
formation derivation. It is not declared equal to the reindexed old code. -/
def under (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (domain : Code seeds seedModel arrows context) :
    Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension →
      Code seeds seedModel arrows other :=
  Quotient.hrecOn' (φ := fun code =>
    Code seeds seedModel arrows (decodeFamily seeds seedModel arrows code).extension →
      Code seeds seedModel arrows other) domain
    (fun raw => underFromRaw seeds seedModel arrows kind change raw)
    (fun _ _ related => underFromRaw_congr seeds seedModel arrows kind change related)

def piUnder {context other : LabelledContext C} (change : NatTrans other.base context.base)
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows other := under seeds seedModel arrows .pi change domain body

def sigmaUnder {context other : LabelledContext C} (change : NatTrans other.base context.base)
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows other := under seeds seedModel arrows .sigma change domain body

theorem decode_under (kind : UnderFormation) {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension) :
    decodeFamily seeds seedModel arrows (under seeds seedModel arrows kind change domain body) =
      materialUnder arrows kind change (decodeFamily seeds seedModel arrows domain)
        (decodeFamily seeds seedModel arrows body) := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  rfl


/-- An interpreted declared seed is actual code data, not a proof of
existence of some interpretation. -/
def seed (context : LabelledContext C) (label : seeds context) : Code seeds seedModel arrows context :=
  ofRaw seeds seedModel arrows ⟨seedModel context label, Generation.seed context label⟩

def unit (context : LabelledContext C) : Code seeds seedModel arrows context :=
  ofRaw seeds seedModel arrows ⟨MaterialFamily.unit context, Generation.unit context⟩

def empty (context : LabelledContext C) : Code seeds seedModel arrows context :=
  ofRaw seeds seedModel arrows ⟨MaterialFamily.empty context, Generation.empty context⟩

theorem formed {context : LabelledContext C} (code : Code seeds seedModel arrows context) :
    Nonempty (Generation seeds seedModel arrows (decodeFamily seeds seedModel arrows code)) := by
  induction code using Quotient.inductionOn with
  | _ raw => exact ⟨raw.2⟩

theorem interpreted_code_enclosed {context : LabelledContext C}
    (code : Code seeds seedModel arrows context) (point : context.base.Elements) :
    HSet.lift ((decodeFamily seeds seedModel arrows code).model point).carrier ∈
      ContextualGeneratedUniverse.enclosure seeds seedModel arrows context point := by
  induction code using Quotient.inductionOn with
  | _ raw => exact generated_mem_enclosure seeds seedModel arrows raw.2 point

def baseSubstitutionCodeFunctor : LabelledContext C ⥤ Type (u + 1) where
  obj := Code seeds seedModel arrows
  map change := TypeCat.ofHom (reindex seeds seedModel arrows change)
  map_id _ := by apply ConcreteCategory.hom_ext; exact reindex_identity seeds seedModel arrows
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro code
    exact (reindex_comp seeds seedModel arrows second first code).symm

def interpretation : NatTrans (baseSubstitutionCodeFunctor seeds seedModel arrows)
    (ContextualUniverseCodes.baseSubstitutionFamilyFunctor (C := C)) where
  app _ := TypeCat.ofHom (decodeFamily seeds seedModel arrows)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    exact decode_reindex seeds seedModel arrows change

/-- Substitution coherence does not erase the formation constructors. This
structural observation supplies a separate invariant from material decoding. -/
inductive FormationSkeleton where
  | seed | empty | unit
  | pi (domain body : FormationSkeleton)
  | sigma (domain body : FormationSkeleton)
  | w (domain body : FormationSkeleton)
  | identity (domain : FormationSkeleton)

def skeleton : {context : LabelledContext C} → {domain : MaterialFamily context} →
    Generation seeds seedModel arrows domain → FormationSkeleton
  | _, _, .seed _ _ => .seed
  | _, _, .empty _ => .empty
  | _, _, .unit _ => .unit
  | _, _, .pi domain body => .pi (skeleton domain) (skeleton body)
  | _, _, .sigma domain body => .sigma (skeleton domain) (skeleton body)
  | _, _, .w domain body => .w (skeleton domain) (skeleton body)
  | _, _, .identity domain _ _ => .identity (skeleton domain)
  | _, _, .reindex domain _ => skeleton domain
  | _, _, .piUnder domain body _ => .pi (skeleton domain) (skeleton body)
  | _, _, .sigmaUnder domain body _ => .sigma (skeleton domain) (skeleton body)

theorem skeleton_substitution {context : LabelledContext C}
    {first second : RawCode seeds seedModel arrows context}
    (related : ContextualUniverseCodes.Equation seeds seedModel arrows first second) :
    skeleton seeds seedModel arrows first.2 = skeleton seeds seedModel arrows second.2 := by
  induction related with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex_identity => rfl
  | reindex_comp => rfl
  | reindex_cong _ _ ih => exact ih

theorem skeleton_equation {context : LabelledContext C}
    {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) :
    skeleton seeds seedModel arrows first.2 = skeleton seeds seedModel arrows second.2 := by
  induction related with
  | substitution related => exact skeleton_substitution seeds seedModel arrows related
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex_congr _ _ ih => exact ih
  | binary_congr kind _ _ domains bodies =>
    cases kind <;> dsimp only [rawBinary, generationBinary, skeleton] <;> rw [domains, bodies]
  | identity_congr _ _ _ ih => exact congrArg FormationSkeleton.identity ih
  | under_congr kind _ _ _ domains bodies =>
    cases kind <;> dsimp only [rawUnder, generationUnder, skeleton] <;> rw [domains, bodies]

def codeSkeleton {context : LabelledContext C} : Code seeds seedModel arrows context → FormationSkeleton :=
  Quotient.lift (fun raw => skeleton seeds seedModel arrows raw.2)
    (fun _ _ related => skeleton_equation seeds seedModel arrows related)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes
