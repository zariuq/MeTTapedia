import Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary
import Mettapedia.GSLT.LanguageDef.BiformTheoryGraph

/-!
# Certified biform theories over the theory graph

The fixed-institution certified biform category fixes one consequence
institution and one native proof calculus.  This module supplies its total
counterpart.  An object may select its own native institution, closed theory,
proof calculus, proof-relevant GSLT, and exact executable certificate boundary.

An arrow retains three mutually constrained actions:

* a heterogeneous biform route transports native sentences and operational
  events through their commuting meaning square; and
* a certificate map replays through the sentence translation chosen by that
  same biform route.

The construction does not infer a checker from theoremhood and does not infer
native proof identity from an operational event.  Forgetting certificates and
forgetting operational structure are explicit functors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraph

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe uSignature uHom uSentence uTerm uCertificate

/-! ## A reusable exact replay boundary for native proof objects -/

/-- The sentence concluded by one native proof object.  Naming the coercion
keeps executable equality tests at the selected sentence carrier. -/
def nativeProofConclusion
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (logical : PiInstitution.TheoryObject institution)
    (calculus : PiInstitution.ProofCalculus institution)
    (proof : calculus.proof.obj logical) :
    institution.sentence.obj logical.signature :=
  calculus.projection.app logical proof

/-- When native sentence equality is decidable, native proof objects
themselves form an exact executable certificate representation.  Replay only
checks the proof projection; the proof object, including any intensional tag,
is retained unchanged. -/
def nativeProofBoundary
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (logical : PiInstitution.TheoryObject institution)
    (calculus : PiInstitution.ProofCalculus institution)
    [DecidableEq (institution.sentence.obj logical.signature)] :
    ProofCarryingAuthority.{0, uSentence}
      (ClosedTheorySemanticTarget.evidenceDiscipline calculus logical) where
  Certificate := fun _ => calculus.proof.obj logical
  checker := fun _ =>
    { check := fun formula proof =>
        decide (nativeProofConclusion logical calculus proof = formula) }
  certificateBoundary := fun _ =>
    { fibreEquiv := fun formula =>
        { toFun := fun accepted =>
            ⟨accepted.1, by
              change nativeProofConclusion logical calculus accepted.1 = formula
              exact of_decide_eq_true accepted.2⟩
          invFun := fun native =>
            ⟨native.1, by
              apply decide_eq_true
              exact native.2⟩
          left_inv := by
            intro accepted
            apply Subtype.ext
            rfl
          right_inv := by
            intro native
            apply Subtype.ext
            rfl } }

@[simp]
theorem nativeProofBoundary_check
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (logical : PiInstitution.TheoryObject institution)
    (calculus : PiInstitution.ProofCalculus institution)
    [DecidableEq (institution.sentence.obj logical.signature)]
    (formula : institution.sentence.obj logical.signature)
    (proof : calculus.proof.obj logical) :
    ((nativeProofBoundary logical calculus).checker ()).check formula proof =
      decide (nativeProofConclusion logical calculus proof = formula) :=
  rfl

/-! ## Objects and exact replay routes -/

/-- A heterogeneous biform theory equipped with one selected native proof
calculus and an exact primary certificate boundary for that calculus. -/
structure Object where
  biform :
    BiformTheoryGraph.Object.{uSignature, uHom, uSentence, uTerm}
  calculus : PiInstitution.ProofCalculus biform.logical.institution
  contract :
    ProofCarryingAuthority.{0, uCertificate}
      (ClosedTheorySemanticTarget.evidenceDiscipline calculus
        biform.logical.logical)

namespace Object

/-- The certified theory carried by one certified biform theory. -/
def toCertifiedTheory
    (object : Object.{uSignature, uHom, uSentence, uTerm, uCertificate}) :
    CertifiedTheoryCategory.CertifiedTheory.{0, uSignature, uSentence,
      uCertificate} where
  Kind := Unit
  family := ClosedTheorySemanticTarget.theoryFamily object.biform.logical.logical
  contract := object.contract.toAuthorityContract

end Object

/-- A heterogeneous qualified route transports the biform structure and its
executable certificates together.  Its claim map is not an independent field:
it is the cross-institution sentence map already selected by the biform route. -/
structure Hom
    (source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}) where
  biform : BiformTheoryGraph.Hom source.biform target.biform
  mapCertificate :
    source.contract.Certificate () → target.contract.Certificate ()
  check_commutes : ∀ formula certificate,
    (target.contract.checker ()).check
        (TheoryGraph.translateSentence
          (TheoryGraph.Hom.institution biform.logical)
          (TheoryGraph.Hom.mapSignature biform.logical) formula)
        (mapCertificate certificate) =
      (source.contract.checker ()).check formula certificate

namespace Hom

variable
  {first middle last :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate}}

/-- Qualified routes are determined by their biform and certificate actions;
the replay equation is proof-irrelevant. -/
@[ext]
theorem ext_data {left right : Hom first middle}
    (biform : left.biform = right.biform)
    (certificate : left.mapCertificate = right.mapCertificate) :
    left = right := by
  cases left
  cases right
  cases biform
  cases certificate
  rfl

/-- Identity changes neither the biform theory nor its certificates. -/
def identity
    (object : Object.{uSignature, uHom, uSentence, uTerm, uCertificate}) :
    Hom object object where
  biform := BiformTheoryGraph.Hom.identity object.biform
  mapCertificate := id
  check_commutes := by
    intro formula certificate
    dsimp only [BiformTheoryGraph.Hom.identity]
    rw [TheoryGraph.translateSentence_id]
    rfl

/-- Composition follows both heterogeneous biform routes and replays the
certificate through their two exact boundaries in sequence. -/
def comp (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  biform := BiformTheoryGraph.Hom.comp earlier.biform later.biform
  mapCertificate certificate :=
    later.mapCertificate (earlier.mapCertificate certificate)
  check_commutes := by
    intro formula certificate
    dsimp only [BiformTheoryGraph.Hom.comp]
    rw [TheoryGraph.translateSentence_comp, later.check_commutes, earlier.check_commutes]

/-- Every certified route induces a certified
translation with the identical native sentence map. -/
def toCertifiedTranslation (route : Hom first middle) :
    first.toCertifiedTheory ⟶ middle.toCertifiedTheory where
  mapKind := id
  mapSignature := fun _ => .selected
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ formula =>
    TheoryGraph.translateSentence
      (TheoryGraph.Hom.institution route.biform.logical)
      (TheoryGraph.Hom.mapSignature route.biform.logical) formula
  mapCertificate := fun _ certificate => route.mapCertificate certificate
  check_commutes := by
    intro kind formula certificate
    cases kind
    exact route.check_commutes formula certificate
  meaning_preserved := by
    intro kind formula theoremhood
    cases kind
    exact TheoryGraph.Hom.preserves route.biform.logical theoremhood

end Hom

instance instQuiver : Quiver
    (Object.{uSignature, uHom, uSentence, uTerm, uCertificate}) where
  Hom := Hom

instance instCategory : CategoryTheory.Category
    (Object.{uSignature, uHom, uSentence, uTerm, uCertificate}) where
  id := Hom.identity
  comp := Hom.comp
  id_comp route := by
    apply Hom.ext_data
    · exact BiformTheoryGraph.instCategory.id_comp route.biform
    · rfl
  comp_id route := by
    apply Hom.ext_data
    · exact BiformTheoryGraph.instCategory.comp_id route.biform
    · rfl
  assoc earlier middle later := by
    apply Hom.ext_data
    · exact BiformTheoryGraph.instCategory.assoc
        earlier.biform middle.biform later.biform
    · rfl

/-! ## Independent projections and their compatibility locus -/

/-- Project to the heterogeneous biform theory, forgetting the certificate
boundary. -/
def biformProjection :
    CategoryTheory.Functor
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}
      BiformTheoryGraph.Object.{uSignature, uHom, uSentence, uTerm} where
  obj object := object.biform
  map route := route.biform
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Project to the certified theory, forgetting the operational face. -/
def certifiedTheoryProjection :
    CategoryTheory.Functor
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}
      CertifiedTheoryCategory.CertifiedTheory.{0, uSignature, uSentence,
        uCertificate} where
  obj object := object.toCertifiedTheory
  map route := route.toCertifiedTranslation
  map_id object := by
    apply CertifiedTheoryCategory.CertifiedTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      cases signature
      rfl
    · intro kind formula
      cases kind
      exact heq_of_eq (TheoryGraph.translateSentence_id object.biform.logical formula)
    · intro kind certificate
      cases kind
      rfl
  map_comp earlier later := by
    apply CertifiedTheoryCategory.CertifiedTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      cases signature
      rfl
    · intro kind formula
      cases kind
      exact heq_of_eq
        (TheoryGraph.translateSentence_comp earlier.biform.logical later.biform.logical formula)
    · intro kind certificate
      cases kind
      rfl

/-- The independently readable data of one certified route. -/
def routePair
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}}
    (route : source ⟶ target) :=
  (route.biform, route.mapCertificate)

/-- A heterogeneous biform route and certificate map are compatible exactly
when checker replay commutes through the biform route's native sentence map. -/
def ReplayCompatible
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}}
    (pair :
      BiformTheoryGraph.Hom source.biform target.biform ×
        (source.contract.Certificate () →
          target.contract.Certificate ())) : Prop :=
  ∀ formula certificate,
    (target.contract.checker ()).check
        (TheoryGraph.translateSentence
          (TheoryGraph.Hom.institution pair.1.logical)
          (TheoryGraph.Hom.mapSignature pair.1.logical) formula)
        (pair.2 certificate) =
      (source.contract.checker ()).check formula certificate

/-- The image of qualified routes is exactly the replay-compatible locus. -/
theorem routePair_range_iff_replayCompatible
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}}
    (pair :
      BiformTheoryGraph.Hom source.biform target.biform ×
        (source.contract.Certificate () →
          target.contract.Certificate ())) :
    (∃ route : source ⟶ target, routePair route = pair) ↔
      ReplayCompatible pair := by
  constructor
  · rintro ⟨route, rfl⟩
    exact route.check_commutes
  · intro compatible
    exact ⟨{ biform := pair.1
             mapCertificate := pair.2
             check_commutes := compatible }, rfl⟩

/-- The biform and certificate actions jointly determine a qualified route. -/
theorem routePair_injective
    {source target :
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate}} :
    Function.Injective (routePair : (source ⟶ target) → _) := by
  intro left right equal
  apply Hom.ext_data
  · exact congrArg Prod.fst equal
  · exact congrArg Prod.snd equal

/-! ## Fixed-institution certified biform categories are vertical fibres -/

/-- Regard a fixed-institution certified biform theory as a heterogeneous
one without changing its logic, algorithm, proof calculus, or checker. -/
def fixedObject
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (calculus : PiInstitution.ProofCalculus institution)
    (object : CertifiedBiformTheory.Object.{uSignature, uHom,
      uSentence, uTerm, uCertificate} calculus) :
    Object.{uSignature, uHom, uSentence, uTerm, uCertificate} where
  biform := BiformTheoryGraph.fixedObject object.biform
  calculus := calculus
  contract := object.boundary.contract

/-- An ordinary qualified route is the vertical heterogeneous route over the
identity institution translation. -/
def Hom.ofFixed
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    {calculus : PiInstitution.ProofCalculus institution}
    {source target : CertifiedBiformTheory.Object.{uSignature, uHom,
      uSentence, uTerm, uCertificate} calculus}
    (route : CertifiedBiformTheory.Hom source target) :
    Hom (fixedObject calculus source) (fixedObject calculus target) where
  biform := BiformTheoryGraph.Hom.ofFixed route.biform
  mapCertificate := route.mapCertificate
  check_commutes := by
    intro formula certificate
    dsimp only [BiformTheoryGraph.Hom.ofFixed]
    rw [BiformTheoryGraph.translateSentence_fibre]
    exact route.check_commutes formula certificate

/-- The fixed-institution certified category embeds as the vertical fibre
over each fixed institution and proof calculus. -/
def fixedFiber
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (calculus : PiInstitution.ProofCalculus institution) :
    CategoryTheory.Functor
      (CertifiedBiformTheory.Object.{uSignature, uHom, uSentence,
        uTerm, uCertificate} calculus)
      Object.{uSignature, uHom, uSentence, uTerm, uCertificate} where
  obj := fixedObject calculus
  map := Hom.ofFixed
  map_id object := by
    apply Hom.ext_data
    · exact (BiformTheoryGraph.fixedFiber institution).map_id object.biform
    · rfl
  map_comp earlier later := by
    apply Hom.ext_data
    · exact (BiformTheoryGraph.fixedFiber institution).map_comp
        earlier.biform later.biform
    · rfl

/-- The vertical embedding retains distinct fixed-institution certified
routes. -/
theorem fixedFiber_map_injective
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    {calculus : PiInstitution.ProofCalculus institution}
    {source target : CertifiedBiformTheory.Object.{uSignature, uHom,
      uSentence, uTerm, uCertificate} calculus} :
    Function.Injective
      (fun route : CertifiedBiformTheory.Hom source target =>
        (fixedFiber calculus).map route) := by
  intro left right equal
  apply CertifiedBiformTheory.Hom.ext_data
  · apply BiformTheoryGraph.fixedFiber_map_injective
    exact congrArg Hom.biform equal
  · exact congrArg Hom.mapCertificate equal

/-- The fixed-institution certified category is categorically a faithful
vertical fibre of the heterogeneous total category. -/
instance fixedFiber_faithful
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (calculus : PiInstitution.ProofCalculus institution) :
    (fixedFiber.{uSignature, uHom, uSentence, uTerm, uCertificate}
      calculus).Faithful where
  map_injective := by
    intro source target left right equal
    exact (fixedFiber_map_injective
      (calculus := calculus) (source := source) (target := target)) equal

#print axioms nativeProofConclusion
#print axioms nativeProofBoundary
#print axioms nativeProofBoundary_check
#print axioms Object.toCertifiedTheory
#print axioms Hom.identity
#print axioms Hom.comp
#print axioms Hom.toCertifiedTranslation
#print axioms instCategory
#print axioms biformProjection
#print axioms certifiedTheoryProjection
#print axioms routePair_range_iff_replayCompatible
#print axioms routePair_injective
#print axioms fixedFiber
#print axioms fixedFiber_map_injective
#print axioms fixedFiber_faithful

end Mettapedia.GSLT.LanguageDef.CertifiedBiformTheoryGraph
