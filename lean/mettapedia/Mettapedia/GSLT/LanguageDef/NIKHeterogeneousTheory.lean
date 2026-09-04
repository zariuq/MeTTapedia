import Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView

/-!
# Heterogeneous theory and authority translations

NIK theory profiles inside one family may share claim and certificate fibres.
Distinct native kernels generally do not.  This module gives the latter case
its own interface: source and target kinds, signatures, claims, certificates,
and checkers may all differ.

The conservative sum construction is the minimal plural authority waist.  It
hosts two exact authorities without adding cross-kernel theorems or converting
one proof language into the other.  Cross-kernel transport is a separately
authored `AuthorityTranslation` and therefore carries its own semantic and
replay obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uKind uSignature uClaim uCertificate

/-! ## Semantic translations between distinct theory families -/

/-- A semantic translation between theory families whose signatures and claim
fibres need not have a common representation. -/
structure TheoryTranslation
    {SourceKind TargetKind : Type uKind}
    (source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind)
    (target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind) where
  mapKind : SourceKind -> TargetKind
  mapSignature : source.Signature -> target.Signature
  signature_commutes : forall kind,
    mapSignature (source.signatureOf kind) =
      target.signatureOf (mapKind kind)
  mapClaim : forall kind, source.Claim kind -> target.Claim (mapKind kind)
  scope_preserved : forall kind claim,
    source.Scope kind claim -> target.Scope (mapKind kind) (mapClaim kind claim)
  meaning_preserved : forall kind claim,
    source.Meaning kind claim ->
      target.Meaning (mapKind kind) (mapClaim kind claim)

namespace TheoryTranslation

variable {SourceKind MiddleKind TargetKind : Type uKind}
    {source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind}
    {middle : TheoryFamily.{uSignature, uKind, uClaim} MiddleKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}

/-- Identity does not reinterpret a theory family. -/
def identity (theory : TheoryFamily.{uSignature, uKind, uClaim} SourceKind) :
    TheoryTranslation theory theory where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; rfl
  mapClaim := fun _ claim => claim
  scope_preserved := by intro kind claim inScope; exact inScope
  meaning_preserved := by intro kind claim meaningful; exact meaningful

/-- Heterogeneous semantic translations compose at every indexed fibre. -/
def comp (earlier : TheoryTranslation source middle)
    (later : TheoryTranslation middle target) :
    TheoryTranslation source target where
  mapKind kind := later.mapKind (earlier.mapKind kind)
  mapSignature signature := later.mapSignature (earlier.mapSignature signature)
  signature_commutes := by
    intro kind
    rw [earlier.signature_commutes, later.signature_commutes]
  mapClaim kind claim :=
    later.mapClaim (earlier.mapKind kind) (earlier.mapClaim kind claim)
  scope_preserved := by
    intro kind claim inScope
    exact later.scope_preserved _ _
      (earlier.scope_preserved kind claim inScope)
  meaning_preserved := by
    intro kind claim meaningful
    exact later.meaning_preserved _ _
      (earlier.meaning_preserved kind claim meaningful)

@[simp] theorem identity_mapKind
    (theory : TheoryFamily.{uSignature, uKind, uClaim} SourceKind)
    (kind : SourceKind) :
    (identity theory).mapKind kind = kind :=
  rfl

@[simp] theorem identity_mapClaim
    (theory : TheoryFamily.{uSignature, uKind, uClaim} SourceKind)
    (kind : SourceKind) (claim : theory.Claim kind) :
    (identity theory).mapClaim kind claim = claim :=
  rfl

@[simp] theorem comp_mapKind
    (earlier : TheoryTranslation source middle)
    (later : TheoryTranslation middle target) (kind : SourceKind) :
    (comp earlier later).mapKind kind = later.mapKind (earlier.mapKind kind) :=
  rfl

@[simp] theorem comp_mapClaim
    (earlier : TheoryTranslation source middle)
    (later : TheoryTranslation middle target)
    (kind : SourceKind) (claim : source.Claim kind) :
    (comp earlier later).mapClaim kind claim =
      later.mapClaim (earlier.mapKind kind) (earlier.mapClaim kind claim) :=
  rfl

/-- Scope reflection is the no-new-source-theorems half of conservativity. -/
def ScopeReflecting (translation : TheoryTranslation source target) : Prop :=
  forall kind claim,
    target.Scope (translation.mapKind kind) (translation.mapClaim kind claim) ->
      source.Scope kind claim

/-- Meaning reflection is the no-new-source-truths half of conservativity. -/
def MeaningReflecting (translation : TheoryTranslation source target) : Prop :=
  forall kind claim,
    target.Meaning (translation.mapKind kind) (translation.mapClaim kind claim) ->
      source.Meaning kind claim

/-- A conservative heterogeneous translation reflects both theorem scope and
authored semantic meaning on translated source claims. -/
structure Conservative (translation : TheoryTranslation source target) : Prop where
  scope_reflecting : ScopeReflecting translation
  meaning_reflecting : MeaningReflecting translation

/-- Conservativity composes: a staged route cannot invent source theorems or
meanings when neither of its stages can. -/
theorem Conservative.comp
    (earlier : TheoryTranslation source middle)
    (later : TheoryTranslation middle target)
    (earlierConservative : earlier.Conservative)
    (laterConservative : later.Conservative) :
    (TheoryTranslation.comp earlier later).Conservative where
  scope_reflecting := by
    intro kind claim inScope
    exact earlierConservative.scope_reflecting kind claim
      (laterConservative.scope_reflecting (earlier.mapKind kind)
        (earlier.mapClaim kind claim) inScope)
  meaning_reflecting := by
    intro kind claim meaningful
    exact earlierConservative.meaning_reflecting kind claim
      (laterConservative.meaning_reflecting (earlier.mapKind kind)
        (earlier.mapClaim kind claim) meaningful)

theorem scope_iff_of_conservative
    (translation : TheoryTranslation source target)
    (conservative : translation.Conservative)
    (kind : SourceKind) (claim : source.Claim kind) :
    target.Scope (translation.mapKind kind)
        (translation.mapClaim kind claim) <->
      source.Scope kind claim := by
  constructor
  · exact conservative.scope_reflecting kind claim
  · exact translation.scope_preserved kind claim

theorem meaning_iff_of_conservative
    (translation : TheoryTranslation source target)
    (conservative : translation.Conservative)
    (kind : SourceKind) (claim : source.Claim kind) :
    target.Meaning (translation.mapKind kind)
        (translation.mapClaim kind claim) <->
      source.Meaning kind claim := by
  constructor
  · exact conservative.meaning_reflecting kind claim
  · exact translation.meaning_preserved kind claim

end TheoryTranslation

/-! ## Exact proof-carrying translations between distinct authorities -/

/-- A heterogeneous authority translation transports native evidence and
makes replay commute exactly.  Scope preservation is deliberately not a
field: it follows from exact replay and the two endpoint authority theorems. -/
structure AuthorityTranslation
    {SourceKind TargetKind : Type uKind}
    {source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}
    (sourceContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} source)
    (targetContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} target) where
  mapKind : SourceKind -> TargetKind
  mapSignature : source.Signature -> target.Signature
  signature_commutes : forall kind,
    mapSignature (source.signatureOf kind) =
      target.signatureOf (mapKind kind)
  mapClaim : forall kind, source.Claim kind -> target.Claim (mapKind kind)
  mapCertificate : forall kind,
    sourceContract.Certificate kind ->
      targetContract.Certificate (mapKind kind)
  check_commutes : forall kind claim certificate,
    (targetContract.checker (mapKind kind)).check
        (mapClaim kind claim) (mapCertificate kind certificate) =
      (sourceContract.checker kind).check claim certificate
  meaning_preserved : forall kind claim,
    source.Meaning kind claim ->
      target.Meaning (mapKind kind) (mapClaim kind claim)

namespace AuthorityTranslation

variable {SourceKind MiddleKind TargetKind : Type uKind}
    {source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind}
    {middle : TheoryFamily.{uSignature, uKind, uClaim} MiddleKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}
    {sourceContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} source}
    {middleContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} middle}
    {targetContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} target}

/-- Exact replay derives theorem-scope preservation across different kernels. -/
theorem scope_preserved
    (translation : AuthorityTranslation sourceContract targetContract)
    (kind : SourceKind) (claim : source.Claim kind)
    (inScope : source.Scope kind claim) :
    target.Scope (translation.mapKind kind)
      (translation.mapClaim kind claim) := by
  obtain ⟨certificate, accepted⟩ :=
    (sourceContract.scopeAuthority kind).complete claim inScope
  apply (targetContract.scopeAuthority (translation.mapKind kind)).sound
    (translation.mapClaim kind claim)
    (translation.mapCertificate kind certificate)
  rw [translation.check_commutes]
  exact accepted

/-- Forget native evidence transport only after deriving the semantic map. -/
def toTheoryTranslation
    (translation : AuthorityTranslation sourceContract targetContract) :
    TheoryTranslation source target where
  mapKind := translation.mapKind
  mapSignature := translation.mapSignature
  signature_commutes := translation.signature_commutes
  mapClaim := translation.mapClaim
  scope_preserved := translation.scope_preserved
  meaning_preserved := translation.meaning_preserved

/-- Identity authority translation. -/
def identity (contract :
    AuthorityContract.{uKind, uCertificate, uSignature, uClaim} source) :
    AuthorityTranslation contract contract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; rfl
  mapClaim := fun _ claim => claim
  mapCertificate := fun _ certificate => certificate
  check_commutes := by intro kind claim certificate; rfl
  meaning_preserved := by intro kind claim meaningful; exact meaningful

/-- Exact authority translations compose without choosing a universal claim
or certificate representation. -/
def comp
    (earlier : AuthorityTranslation sourceContract middleContract)
    (later : AuthorityTranslation middleContract targetContract) :
    AuthorityTranslation sourceContract targetContract where
  mapKind kind := later.mapKind (earlier.mapKind kind)
  mapSignature signature := later.mapSignature (earlier.mapSignature signature)
  signature_commutes := by
    intro kind
    rw [earlier.signature_commutes, later.signature_commutes]
  mapClaim kind claim :=
    later.mapClaim (earlier.mapKind kind) (earlier.mapClaim kind claim)
  mapCertificate kind certificate :=
    later.mapCertificate (earlier.mapKind kind)
      (earlier.mapCertificate kind certificate)
  check_commutes := by
    intro kind claim certificate
    rw [later.check_commutes, earlier.check_commutes]
  meaning_preserved := by
    intro kind claim meaningful
    exact later.meaning_preserved _ _
      (earlier.meaning_preserved kind claim meaningful)

@[simp] theorem comp_mapClaim
    (earlier : AuthorityTranslation sourceContract middleContract)
    (later : AuthorityTranslation middleContract targetContract)
    (kind : SourceKind) (claim : source.Claim kind) :
    (comp earlier later).mapClaim kind claim =
      later.mapClaim (earlier.mapKind kind) (earlier.mapClaim kind claim) :=
  rfl

@[simp] theorem comp_mapCertificate
    (earlier : AuthorityTranslation sourceContract middleContract)
    (later : AuthorityTranslation middleContract targetContract)
    (kind : SourceKind)
    (certificate : sourceContract.Certificate kind) :
    (comp earlier later).mapCertificate kind certificate =
      later.mapCertificate (earlier.mapKind kind)
        (earlier.mapCertificate kind certificate) :=
  rfl

end AuthorityTranslation

/-! ## Conservative coproduct of independent kernels -/

namespace Coproduct

variable {LeftKind RightKind : Type uKind}
    (left : TheoryFamily.{uSignature, uKind, uClaim} LeftKind)
    (right : TheoryFamily.{uSignature, uKind, uClaim} RightKind)

/-- Disjoint coexistence of two theories.  No cross-theory theorem or
conversion is added. -/
def theory : TheoryFamily (Sum LeftKind RightKind) where
  Signature := Sum left.Signature right.Signature
  signatureOf
    | .inl kind => .inl (left.signatureOf kind)
    | .inr kind => .inr (right.signatureOf kind)
  Claim
    | .inl kind => left.Claim kind
    | .inr kind => right.Claim kind
  Scope
    | .inl kind => left.Scope kind
    | .inr kind => right.Scope kind
  Meaning
    | .inl kind => left.Meaning kind
    | .inr kind => right.Meaning kind
  scope_sound := by
    intro kind claim inScope
    cases kind with
    | inl kind => exact left.scope_sound kind claim inScope
    | inr kind => exact right.scope_sound kind claim inScope

variable
    (leftContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} left)
    (rightContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} right)

/-- The tagged authority dispatches to the selected native kernel. -/
def contract : AuthorityContract (theory left right) where
  Certificate
    | .inl kind => leftContract.Certificate kind
    | .inr kind => rightContract.Certificate kind
  checker
    | .inl kind => leftContract.checker kind
    | .inr kind => rightContract.checker kind
  scopeAuthority := by
    intro kind
    cases kind with
    | inl kind => exact leftContract.scopeAuthority kind
    | inr kind => exact rightContract.scopeAuthority kind

/-- The left authority enters the coproduct without reinterpretation. -/
def leftInclusion :
    AuthorityTranslation leftContract
      (contract left right leftContract rightContract) where
  mapKind := Sum.inl
  mapSignature := Sum.inl
  signature_commutes := by intro kind; rfl
  mapClaim := fun _ claim => claim
  mapCertificate := fun _ certificate => certificate
  check_commutes := by intro kind claim certificate; rfl
  meaning_preserved := by intro kind claim meaningful; exact meaningful

/-- The right authority enters the coproduct without reinterpretation. -/
def rightInclusion :
    AuthorityTranslation rightContract
      (contract left right leftContract rightContract) where
  mapKind := Sum.inr
  mapSignature := Sum.inr
  signature_commutes := by intro kind; rfl
  mapClaim := fun _ claim => claim
  mapCertificate := fun _ certificate => certificate
  check_commutes := by intro kind claim certificate; rfl
  meaning_preserved := by intro kind claim meaningful; exact meaningful

/-- The left inclusion is conservative: coproduct coexistence proves no new
left theorem and changes no left meaning. -/
theorem leftInclusion_conservative :
    (leftInclusion left right leftContract rightContract).toTheoryTranslation.Conservative where
  scope_reflecting := by intro kind claim inScope; exact inScope
  meaning_reflecting := by intro kind claim meaningful; exact meaningful

/-- The right inclusion is conservative for the same reason. -/
theorem rightInclusion_conservative :
    (rightInclusion left right leftContract rightContract).toTheoryTranslation.Conservative where
  scope_reflecting := by intro kind claim inScope; exact inScope
  meaning_reflecting := by intro kind claim meaningful; exact meaningful

end Coproduct

/-! ## Positive and negative controls -/

namespace Canary

inductive LeftKind where
  | only
deriving DecidableEq, Repr

inductive RightKind where
  | only
deriving DecidableEq, Repr

abbrev leftTheory : TheoryFamily LeftKind where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ claim => claim = true
  Meaning := fun _ claim => claim = true
  scope_sound := by intro kind claim inScope; exact inScope

abbrev leftContract : AuthorityContract leftTheory where
  Certificate := fun _ => Unit
  checker
    | .only => { check := fun claim _ => claim }
  scopeAuthority
    | .only =>
      { sound := by intro claim certificate accepted; simpa using accepted
        complete := by
          intro claim inScope
          exact ⟨(), by simpa using inScope⟩ }

abbrev rightTheory : TheoryFamily RightKind where
  Signature := Bool
  signatureOf := fun _ => false
  Claim := fun _ => Nat
  Scope := fun _ claim => claim = 0
  Meaning := fun _ claim => claim = 0
  scope_sound := by intro kind claim inScope; exact inScope

abbrev rightContract : AuthorityContract rightTheory where
  Certificate := fun _ => Unit
  checker
    | .only => { check := fun claim _ => decide (claim = 0) }
  scopeAuthority
    | .only =>
      { sound := by
          intro claim certificate accepted
          simpa using accepted
        complete := by
          intro claim inScope
          exact ⟨(), by simpa using inScope⟩ }

abbrev pluralTheory := Coproduct.theory leftTheory rightTheory

abbrev pluralContract :=
  Coproduct.contract leftTheory rightTheory leftContract rightContract

/-- Positive control: a left proof replays unchanged after conservative
inclusion into the plural waist. -/
theorem left_true_replays :
    (pluralContract.checker (.inl .only)).check true () = true :=
  rfl

/-- Positive control: the differently shaped right authority also replays at
its own fibre. -/
theorem right_zero_replays :
    (pluralContract.checker (.inr .only)).check
        (show pluralTheory.Claim (.inr .only) from (0 : Nat)) () = true := by
  rfl

/-- Negative control: even equal certificate payloads cannot cross the tag
boundary of the packed plural dispatcher. -/
theorem wrong_kernel_certificate_rejected :
    pluralContract.toAuthorityFamily.packedChecker.check
        ⟨.inl .only, true⟩ ⟨.inr .only, ()⟩ = false := by
  exact AuthorityFamily.packedChecker_rejects_wrongKind
    (family := pluralContract.toAuthorityFamily)
    (claimKind := Sum.inl LeftKind.only)
    (certificateKind := Sum.inr RightKind.only)
    (by decide) true ()

/-- A semantically false, replay-breaking claim map cannot be installed as a
cross-kernel authority translation merely because both kernels coexist. -/
theorem no_constant_one_translation :
    ¬ (exists translation : AuthorityTranslation leftContract rightContract,
      forall claim,
        (show Nat from translation.mapClaim .only claim) = 1) := by
  rintro ⟨translation, mapsOne⟩
  have mappedMeaning := translation.meaning_preserved .only true (by rfl)
  change (show Nat from translation.mapClaim .only true) = 0 at mappedMeaning
  have oneEqualsZero : (1 : Nat) = 0 :=
    (mapsOne true).symm.trans mappedMeaning
  omega

#print axioms AuthorityTranslation.scope_preserved
#print axioms AuthorityTranslation.comp
#print axioms Coproduct.leftInclusion_conservative
#print axioms Coproduct.rightInclusion_conservative
#print axioms wrong_kernel_certificate_rejected
#print axioms no_constant_one_translation

end Canary

end Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
