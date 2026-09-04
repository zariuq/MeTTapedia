import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Theory-profile views and their NIK realizations

An authored theory translation and a translation of checking evidence are
different structures.  This module separates them while retaining the exact
bridge back to NIK's existing authority diagrams and operational GSLTs.

A `TheoryView` maps claims and preserves the independently declared theorem
scope and meaning.  An `AuthorityView` additionally maps native certificates
and makes Boolean replay commute.  Exact replay derives scope preservation;
meaning preservation remains an authored semantic obligation.  Consequently
an authority view induces both a theory view and NIK's existing covered
operational translation.

This is the theory/profile/view fragment of a modular theory graph.  It does
not claim to provide declaration syntax, meta-theory imports, or a universal
logic by itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uKind uSignature uClaim uCertificate

/-! ## Semantic theory-profile views -/

/-- A translation between two profiles of one authored theory family.

The view contains no certificate format and no checker implementation.  It is
therefore suitable for translations whose semantic content is known before a
particular proof-producing realization has been selected. -/
structure TheoryView {Kind : Type uKind} (theory : TheoryFamily Kind)
    (source target : Kind) where
  mapClaim : theory.Claim source -> theory.Claim target
  scope_preserved : forall claim,
    theory.Scope source claim -> theory.Scope target (mapClaim claim)
  meaning_preserved : forall claim,
    theory.Meaning source claim -> theory.Meaning target (mapClaim claim)

namespace TheoryView

variable {Kind : Type uKind} {theory : TheoryFamily Kind}
    {first middle last : Kind}

/-- Identity view of one theory profile. -/
def identity (kind : Kind) : TheoryView theory kind kind where
  mapClaim := id
  scope_preserved := by intro claim inScope; exact inScope
  meaning_preserved := by intro claim meaningful; exact meaningful

/-- Composition of theory views. -/
def comp (earlier : TheoryView theory first middle)
    (later : TheoryView theory middle last) :
    TheoryView theory first last where
  mapClaim claim := later.mapClaim (earlier.mapClaim claim)
  scope_preserved := by
    intro claim inScope
    exact later.scope_preserved _ (earlier.scope_preserved claim inScope)
  meaning_preserved := by
    intro claim meaningful
    exact later.meaning_preserved _
      (earlier.meaning_preserved claim meaningful)

@[simp] theorem identity_mapClaim (kind : Kind)
    (claim : theory.Claim kind) :
    (identity (theory := theory) kind).mapClaim claim = claim :=
  rfl

@[simp] theorem comp_mapClaim
    (earlier : TheoryView theory first middle)
    (later : TheoryView theory middle last)
    (claim : theory.Claim first) :
    (comp earlier later).mapClaim claim =
      later.mapClaim (earlier.mapClaim claim) :=
  rfl

/-- A view is scope-reflecting when it introduces no new theorem among the
translated source claims. -/
def ScopeReflecting (view : TheoryView theory first middle) : Prop :=
  forall claim, theory.Scope middle (view.mapClaim claim) ->
    theory.Scope first claim

/-- A view is meaning-reflecting when it introduces no new semantic truth
among the translated source claims. -/
def MeaningReflecting (view : TheoryView theory first middle) : Prop :=
  forall claim, theory.Meaning middle (view.mapClaim claim) ->
    theory.Meaning first claim

/-- A conservative view reflects both the independently declared theorem
scope and the authored meaning predicate. -/
structure Conservative (view : TheoryView theory first middle) : Prop where
  scope_reflecting : ScopeReflecting view
  meaning_reflecting : MeaningReflecting view

theorem scope_iff_of_conservative
    (view : TheoryView theory first middle) (conservative : view.Conservative)
    (claim : theory.Claim first) :
    theory.Scope middle (view.mapClaim claim) <-> theory.Scope first claim := by
  constructor
  · exact conservative.scope_reflecting claim
  · exact view.scope_preserved claim

theorem meaning_iff_of_conservative
    (view : TheoryView theory first middle) (conservative : view.Conservative)
    (claim : theory.Claim first) :
    theory.Meaning middle (view.mapClaim claim) <->
      theory.Meaning first claim := by
  constructor
  · exact conservative.meaning_reflecting claim
  · exact view.meaning_preserved claim

end TheoryView

/-! ## Proof-carrying realizations of views -/

/-- A proof-carrying realization of a theory view for one authority contract.

Exact replay is stronger than theorem preservation: it says that translating
one submitted source certificate changes neither its accept/reject decision
nor its retained claim.  The target may still possess additional certificates
for additional theorems. -/
structure AuthorityView {Kind : Type uKind} {theory : TheoryFamily Kind}
    (contract : AuthorityContract theory) (source target : Kind) where
  mapClaim : theory.Claim source -> theory.Claim target
  mapCertificate : contract.Certificate source -> contract.Certificate target
  check_commutes : forall claim certificate,
    (contract.checker target).check (mapClaim claim)
        (mapCertificate certificate) =
      (contract.checker source).check claim certificate
  meaning_preserved : forall claim,
    theory.Meaning source claim -> theory.Meaning target (mapClaim claim)

namespace AuthorityView

variable {Kind : Type uKind} {theory : TheoryFamily Kind}
    {contract : AuthorityContract theory} {first middle last : Kind}

/-- Exact replay derives theorem-scope preservation from the source and target
authority contracts. -/
theorem scope_preserved (view : AuthorityView contract first middle)
    (claim : theory.Claim first) (inScope : theory.Scope first claim) :
    theory.Scope middle (view.mapClaim claim) := by
  obtain ⟨certificate, accepted⟩ :=
    (contract.scopeAuthority first).complete claim inScope
  apply (contract.scopeAuthority middle).sound
    (view.mapClaim claim) (view.mapCertificate certificate)
  rw [view.check_commutes]
  exact accepted

/-- Forget certificate transport only after deriving the semantic theory
view. -/
def toTheoryView (view : AuthorityView contract first middle) :
    TheoryView theory first middle where
  mapClaim := view.mapClaim
  scope_preserved := view.scope_preserved
  meaning_preserved := view.meaning_preserved

/-- An authority view is exactly strong enough to instantiate NIK's existing
checker-translation interface. -/
def toCheckerTranslation (view : AuthorityView contract first middle) :
    CheckerTranslation contract.toAuthorityFamily first middle where
  mapClaim := view.mapClaim
  mapCertificate := view.mapCertificate
  check_commutes := view.check_commutes
  certified_preserved := view.scope_preserved
  meaning_preserved := view.meaning_preserved

/-- Hence every proof-carrying theory view has the existing covered
operational GSLT translation, including both step preservation and lifting of
target steps from translated states. -/
def toCoveredTranslation (view : AuthorityView contract first middle) :=
  view.toCheckerTranslation.toCoveredTranslation

/-- Identity proof-carrying view. -/
def identity (kind : Kind) : AuthorityView contract kind kind where
  mapClaim := id
  mapCertificate := id
  check_commutes := by intro claim certificate; rfl
  meaning_preserved := by intro claim meaningful; exact meaningful

/-- Composition of proof-carrying views. -/
def comp (earlier : AuthorityView contract first middle)
    (later : AuthorityView contract middle last) :
    AuthorityView contract first last where
  mapClaim claim := later.mapClaim (earlier.mapClaim claim)
  mapCertificate certificate :=
    later.mapCertificate (earlier.mapCertificate certificate)
  check_commutes := by
    intro claim certificate
    rw [later.check_commutes, earlier.check_commutes]
  meaning_preserved := by
    intro claim meaningful
    exact later.meaning_preserved _
      (earlier.meaning_preserved claim meaningful)

@[simp] theorem toTheoryView_mapClaim
    (view : AuthorityView contract first middle)
    (claim : theory.Claim first) :
    view.toTheoryView.mapClaim claim = view.mapClaim claim :=
  rfl

@[simp] theorem toCheckerTranslation_mapClaim
    (view : AuthorityView contract first middle)
    (claim : theory.Claim first) :
    view.toCheckerTranslation.mapClaim claim = view.mapClaim claim :=
  rfl

@[simp] theorem toCheckerTranslation_mapCertificate
    (view : AuthorityView contract first middle)
    (certificate : contract.Certificate first) :
    view.toCheckerTranslation.mapCertificate certificate =
      view.mapCertificate certificate :=
  rfl

@[simp] theorem comp_mapClaim
    (earlier : AuthorityView contract first middle)
    (later : AuthorityView contract middle last)
    (claim : theory.Claim first) :
    (comp earlier later).mapClaim claim =
      later.mapClaim (earlier.mapClaim claim) :=
  rfl

@[simp] theorem comp_mapCertificate
    (earlier : AuthorityView contract first middle)
    (later : AuthorityView contract middle last)
    (certificate : contract.Certificate first) :
    (comp earlier later).mapCertificate certificate =
      later.mapCertificate (earlier.mapCertificate certificate) :=
  rfl

end AuthorityView

/-! ## A nontrivial extension canary -/

namespace ExtensionCanary

/-- Two profiles of one theory: the extension proves strictly more. -/
inductive Profile where
  | base
  | extension
deriving DecidableEq, Repr

def theory : TheoryFamily Profile where
  Signature := Profile
  signatureOf := id
  Claim := fun _ => Bool
  Scope
    | .base => fun claim => claim = true
    | .extension => fun _ => True
  Meaning
    | .base => fun claim => claim = true
    | .extension => fun _ => True
  scope_sound := by
    intro profile claim inScope
    cases profile <;> exact inScope

def contract : AuthorityContract theory where
  Certificate
    | .base => Unit
    | .extension => Bool
  checker
    | .base => { check := fun claim _ => claim }
    | .extension => { check := fun claim certificate => certificate || claim }
  scopeAuthority := by
    intro profile
    cases profile with
    | base =>
        exact
          { sound := by
              intro claim certificate accepted
              cases claim <;> simp_all [theory]
            complete := by
              intro claim inScope
              cases claim <;> simp_all [theory] }
    | extension =>
        exact
          { sound := by
              intro claim certificate accepted
              trivial
            complete := by
              intro claim inScope
              exact ⟨true, by simp⟩ }

/-- The old proof token embeds as `false`; the target's `true` token is the
new authority unavailable in the base profile. -/
def inclusion : AuthorityView contract .base .extension where
  mapClaim := id
  mapCertificate := fun _ => false
  check_commutes := by intro claim certificate; cases certificate; simp [contract]
  meaning_preserved := by intro claim meaningful; trivial

/-- Positive control: translated base evidence has exactly the same replay
decision in the extension. -/
theorem inclusion_replays_exactly (claim : Bool) :
    (contract.checker .extension).check
        (inclusion.mapClaim claim) (inclusion.mapCertificate ()) =
      (contract.checker .base).check claim () :=
  inclusion.check_commutes claim ()

/-- Positive control: the extension genuinely has a new proof of the formerly
false claim. -/
theorem extension_proves_more :
    theory.Scope .extension false /\ ¬ theory.Scope .base false := by
  simp [theory]

/-- Negative control: there is no identity-on-claims semantic view back from
the stronger extension to the base theory.  A theory inclusion is therefore
not silently promoted to an equivalence. -/
theorem no_identity_view_back :
    ¬ (exists view : TheoryView theory .extension .base,
      forall claim, view.mapClaim claim = claim) := by
  rintro ⟨view, identityMap⟩
  have mapped := view.meaning_preserved false (by trivial)
  rw [identityMap false] at mapped
  simp [theory] at mapped

/-- The proof-carrying inclusion mechanically yields the exact operational
translation used by NIK's GSLT layer. -/
def operationalInclusion := inclusion.toCoveredTranslation

#print axioms inclusion_replays_exactly
#print axioms extension_proves_more
#print axioms no_identity_view_back

end ExtensionCanary

end Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView
