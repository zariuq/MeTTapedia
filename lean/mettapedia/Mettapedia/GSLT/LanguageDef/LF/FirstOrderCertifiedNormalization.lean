import Mettapedia.GSLT.LanguageDef.LF.FirstOrderOperationalCorrespondence

/-!
# Proof-producing normalization for constant-free LF

The live conversion boundary consumes exact finite conversion trees.  This
module constructs those trees from arbitrary constant-free LF terms rather
than trusting a separately serialized normal form.

The algorithm repeatedly selects the leftmost outermost beta or eta redex.
Every selected edge is compiled through the universal contextual
beta/eta compilers, and finite paths are composed only when their intermediate
runtime endpoints coincide.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderCertifiedNormalization

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFBetaEta
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta
open Mettapedia.GSLT.LanguageDef.LFFirstOrderOperationalCorrespondence

abbrev Certificate := ConversionCertificate

private def betaAt
    (outer : LFContextualBetaEta.Context)
    (domain body argument : Term) : Certificate :=
  .beta outer domain body argument

/-- Find the leftmost outermost beta contraction, retaining its full
one-hole context in the emitted certificate. -/
def firstBetaStep? (outer : LFContextualBetaEta.Context) :
    Term → Option Certificate
  | .srt _ => none
  | .con _ => none
  | .var _ => none
  | .pi domain body =>
      match firstBetaStep?
          (outer.comp (.piDomain .hole body)) domain with
      | some certificate => some certificate
      | none =>
          firstBetaStep?
            (outer.comp (.piBody domain .hole)) body
  | .lam domain body =>
      match firstBetaStep?
          (outer.comp (.lamDomain .hole body)) domain with
      | some certificate => some certificate
      | none =>
          firstBetaStep?
            (outer.comp (.lamBody domain .hole)) body
  | .app (.lam domain body) argument =>
      some (betaAt outer domain body argument)
  | .app function argument =>
      match firstBetaStep?
          (outer.comp (.appFunction .hole argument)) function with
      | some certificate => some certificate
      | none =>
          firstBetaStep?
            (outer.comp (.appArgument function .hole)) argument

theorem firstBetaStep?_sound
    (outer : LFContextualBetaEta.Context)
    (term : Term) (certificate : Certificate)
    (hstep : firstBetaStep? outer term = some certificate) :
    certificate.source = outer.plug term ∧ certificate.Accepted := by
  induction term generalizing outer certificate with
  | srt sort =>
      simp [firstBetaStep?] at hstep
  | con name =>
      simp [firstBetaStep?] at hstep
  | var index =>
      simp [firstBetaStep?] at hstep
  | pi domain body domainIH bodyIH =>
      cases hdomain :
          firstBetaStep?
            (outer.comp (.piDomain .hole body)) domain with
      | some domainCertificate =>
          simp [firstBetaStep?, hdomain] at hstep
          subst certificate
          have hsound :=
            domainIH _ _ hdomain
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩
      | none =>
          cases hbody :
              firstBetaStep?
                (outer.comp (.piBody domain .hole)) body with
          | none =>
              simp [firstBetaStep?, hdomain, hbody] at hstep
          | some bodyCertificate =>
              simp [firstBetaStep?, hdomain, hbody] at hstep
              subst certificate
              have hsound :=
                bodyIH _ _ hbody
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
  | lam domain body domainIH bodyIH =>
      cases hdomain :
          firstBetaStep?
            (outer.comp (.lamDomain .hole body)) domain with
      | some domainCertificate =>
          simp [firstBetaStep?, hdomain] at hstep
          subst certificate
          have hsound :=
            domainIH _ _ hdomain
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩
      | none =>
          cases hbody :
              firstBetaStep?
                (outer.comp (.lamBody domain .hole)) body with
          | none =>
              simp [firstBetaStep?, hdomain, hbody] at hstep
          | some bodyCertificate =>
              simp [firstBetaStep?, hdomain, hbody] at hstep
              subst certificate
              have hsound :=
                bodyIH _ _ hbody
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
  | app function argument functionIH argumentIH =>
      cases function with
      | lam domain body =>
          simp [firstBetaStep?, betaAt] at hstep
          subst certificate
          exact
            ⟨rfl, ConversionCertificate.beta_accepted _ _ _ _⟩
      | srt sort =>
          cases hargument :
              firstBetaStep?
                (outer.comp (.appArgument (.srt sort) .hole)) argument with
          | none =>
              simp [firstBetaStep?, hargument] at hstep
          | some argumentCertificate =>
              simp [firstBetaStep?, hargument] at hstep
              subst certificate
              have hsound := argumentIH _ _ hargument
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
      | con name =>
          cases hargument :
              firstBetaStep?
                (outer.comp (.appArgument (.con name) .hole)) argument with
          | none =>
              simp [firstBetaStep?, hargument] at hstep
          | some argumentCertificate =>
              simp [firstBetaStep?, hargument] at hstep
              subst certificate
              have hsound := argumentIH _ _ hargument
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
      | var index =>
          cases hargument :
              firstBetaStep?
                (outer.comp (.appArgument (.var index) .hole)) argument with
          | none =>
              simp [firstBetaStep?, hargument] at hstep
          | some argumentCertificate =>
              simp [firstBetaStep?, hargument] at hstep
              subst certificate
              have hsound := argumentIH _ _ hargument
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
      | pi functionDomain functionBody =>
          change
            (match
                firstBetaStep?
                  (outer.comp (.appFunction .hole argument))
                  (.pi functionDomain functionBody) with
              | some functionCertificate => some functionCertificate
              | none =>
                  firstBetaStep?
                    (outer.comp
                      (.appArgument
                        (.pi functionDomain functionBody) .hole))
                    argument) =
              some certificate at hstep
          cases hfunction :
              firstBetaStep?
                (outer.comp (.appFunction .hole argument))
                (.pi functionDomain functionBody) with
          | some functionCertificate =>
              simp only [hfunction] at hstep
              cases Option.some.inj hstep
              have hsound := functionIH _ _ hfunction
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
          | none =>
              simp only [hfunction] at hstep
              have hsound := argumentIH _ _ hstep
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
      | app functionFunction functionArgument =>
          change
            (match
                firstBetaStep?
                  (outer.comp (.appFunction .hole argument))
                  (.app functionFunction functionArgument) with
              | some functionCertificate => some functionCertificate
              | none =>
                  firstBetaStep?
                    (outer.comp
                      (.appArgument
                        (.app functionFunction functionArgument) .hole))
                    argument) =
              some certificate at hstep
          cases hfunction :
              firstBetaStep?
                (outer.comp (.appFunction .hole argument))
                (.app functionFunction functionArgument) with
          | some functionCertificate =>
              simp only [hfunction] at hstep
              cases Option.some.inj hstep
              have hsound := functionIH _ _ hfunction
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
          | none =>
              simp only [hfunction] at hstep
              have hsound := argumentIH _ _ hstep
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩

/-- Recognize one eta redex at an abstraction root.  Captured occurrences
remain explicit failures of the certified eta compiler. -/
private def etaAtLam?
    (outer : LFContextualBetaEta.Context)
    (domain body : Term) : Option Certificate :=
  match body with
  | .app function (.var 0) =>
      ConversionCertificate.eta? outer domain function
  | _ => none

private theorem etaAtLam?_sound
    (outer : LFContextualBetaEta.Context)
    (domain body : Term) (certificate : Certificate)
    (hstep : etaAtLam? outer domain body = some certificate) :
    certificate.source = outer.plug (.lam domain body) ∧
      certificate.Accepted := by
  cases body with
  | app function argument =>
      cases argument with
      | var index =>
          cases index with
          | zero =>
              have hsource :=
                ConversionCertificate.eta?_source
                  outer domain function certificate hstep
              have haccepted :=
                ConversionCertificate.eta?_sound
                  outer domain function certificate hstep
              exact ⟨hsource, haccepted⟩
          | succ index =>
              simp [etaAtLam?] at hstep
      | srt sort =>
          simp [etaAtLam?] at hstep
      | con name =>
          simp [etaAtLam?] at hstep
      | pi argumentDomain argumentBody =>
          simp [etaAtLam?] at hstep
      | lam argumentDomain argumentBody =>
          simp [etaAtLam?] at hstep
      | app argumentFunction argumentArgument =>
          simp [etaAtLam?] at hstep
  | srt sort =>
      simp [etaAtLam?] at hstep
  | con name =>
      simp [etaAtLam?] at hstep
  | var index =>
      simp [etaAtLam?] at hstep
  | pi bodyDomain bodyBody =>
      simp [etaAtLam?] at hstep
  | lam bodyDomain bodyBody =>
      simp [etaAtLam?] at hstep

/-- Find the leftmost outermost eta contraction.  Captured root occurrences
fail locally and the search then continues beneath the abstraction. -/
def firstEtaStep? (outer : LFContextualBetaEta.Context) :
    Term → Option Certificate
  | .srt _ => none
  | .con _ => none
  | .var _ => none
  | .pi domain body =>
      match firstEtaStep?
          (outer.comp (.piDomain .hole body)) domain with
      | some certificate => some certificate
      | none =>
          firstEtaStep?
            (outer.comp (.piBody domain .hole)) body
  | .lam domain body =>
      match etaAtLam? outer domain body with
      | some certificate => some certificate
      | none =>
          match firstEtaStep?
              (outer.comp (.lamDomain .hole body)) domain with
          | some certificate => some certificate
          | none =>
              firstEtaStep?
                (outer.comp (.lamBody domain .hole)) body
  | .app function argument =>
      match firstEtaStep?
          (outer.comp (.appFunction .hole argument)) function with
      | some certificate => some certificate
      | none =>
          firstEtaStep?
            (outer.comp (.appArgument function .hole)) argument

theorem firstEtaStep?_sound
    (outer : LFContextualBetaEta.Context)
    (term : Term) (certificate : Certificate)
    (hstep : firstEtaStep? outer term = some certificate) :
    certificate.source = outer.plug term ∧ certificate.Accepted := by
  induction term generalizing outer certificate with
  | srt sort =>
      simp [firstEtaStep?] at hstep
  | con name =>
      simp [firstEtaStep?] at hstep
  | var index =>
      simp [firstEtaStep?] at hstep
  | pi domain body domainIH bodyIH =>
      change
        (match
            firstEtaStep?
              (outer.comp (.piDomain .hole body)) domain with
          | some domainCertificate => some domainCertificate
          | none =>
              firstEtaStep?
                (outer.comp (.piBody domain .hole)) body) =
          some certificate at hstep
      cases hdomain :
          firstEtaStep?
            (outer.comp (.piDomain .hole body)) domain with
      | some domainCertificate =>
          simp only [hdomain] at hstep
          cases Option.some.inj hstep
          have hsound := domainIH _ _ hdomain
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩
      | none =>
          simp only [hdomain] at hstep
          have hsound := bodyIH _ _ hstep
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩
  | lam domain body domainIH bodyIH =>
      change
        (match etaAtLam? outer domain body with
          | some rootCertificate => some rootCertificate
          | none =>
              match
                  firstEtaStep?
                    (outer.comp (.lamDomain .hole body)) domain with
                | some domainCertificate => some domainCertificate
                | none =>
                    firstEtaStep?
                      (outer.comp (.lamBody domain .hole)) body) =
          some certificate at hstep
      cases hroot : etaAtLam? outer domain body with
      | some rootCertificate =>
          simp only [hroot] at hstep
          cases Option.some.inj hstep
          exact etaAtLam?_sound outer domain body certificate hroot
      | none =>
          simp only [hroot] at hstep
          cases hdomain :
              firstEtaStep?
                (outer.comp (.lamDomain .hole body)) domain with
          | some domainCertificate =>
              simp only [hdomain] at hstep
              cases Option.some.inj hstep
              have hsound := domainIH _ _ hdomain
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
          | none =>
              simp only [hdomain] at hstep
              have hsound := bodyIH _ _ hstep
              exact
                ⟨hsound.1.trans (by
                    simp [LFContextualBetaEta.Context.plug_comp,
                      LFContextualBetaEta.Context.plug]),
                  hsound.2⟩
  | app function argument functionIH argumentIH =>
      change
        (match
            firstEtaStep?
              (outer.comp (.appFunction .hole argument)) function with
          | some functionCertificate => some functionCertificate
          | none =>
              firstEtaStep?
                (outer.comp (.appArgument function .hole)) argument) =
          some certificate at hstep
      cases hfunction :
          firstEtaStep?
            (outer.comp (.appFunction .hole argument)) function with
      | some functionCertificate =>
          simp only [hfunction] at hstep
          cases Option.some.inj hstep
          have hsound := functionIH _ _ hfunction
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩
      | none =>
          simp only [hfunction] at hstep
          have hsound := argumentIH _ _ hstep
          exact
            ⟨hsound.1.trans (by
                simp [LFContextualBetaEta.Context.plug_comp,
                  LFContextualBetaEta.Context.plug]),
              hsound.2⟩

/-- One beta phase followed by one eta phase.  Repeating this selector handles
redexes exposed by earlier contractions. -/
def firstStep? (term : Term) : Option Certificate :=
  match firstBetaStep? .hole term with
  | some certificate => some certificate
  | none => firstEtaStep? .hole term

theorem firstStep?_sound
    (term : Term) (certificate : Certificate)
    (hstep : firstStep? term = some certificate) :
    certificate.source = term ∧ certificate.Accepted := by
  change
    (match firstBetaStep? .hole term with
      | some betaCertificate => some betaCertificate
      | none => firstEtaStep? .hole term) =
      some certificate at hstep
  cases hbeta : firstBetaStep? .hole term with
  | some betaCertificate =>
      simp only [hbeta] at hstep
      cases Option.some.inj hstep
      simpa [LFContextualBetaEta.Context.plug] using
        firstBetaStep?_sound .hole term certificate hbeta
  | none =>
      simp only [hbeta] at hstep
      simpa [LFContextualBetaEta.Context.plug] using
        firstEtaStep?_sound .hole term certificate hstep

/-- Bounded chronological edge generation.  Fuel exhaustion is explicit: the
last target is returned with an accepted path, but is not called a normal form
without a separate no-redex check. -/
def normalizationEdges : Nat → Term → List Certificate
  | 0, _ => []
  | fuel + 1, term =>
      match firstStep? term with
      | none => []
      | some certificate =>
          certificate :: normalizationEdges fuel certificate.target

/-- A list starts at the declared term and connects every adjacent endpoint. -/
def Chronological : Term → List Certificate → Prop
  | _, [] => True
  | term, certificate :: rest =>
      certificate.source = term ∧
        Chronological certificate.target rest

/-- Include an explicit reflexive head so even a term with no redex has a
nonempty serializable proof path. -/
def normalizationCertificates (fuel : Nat) (term : Term) :
    List Certificate :=
  .refl term :: normalizationEdges fuel term

/-- Runtime composition remains partial and therefore fail-closed if any
generated intermediate endpoint is corrupted. -/
def normalizationCertificate? (fuel : Nat) (term : Term) :
    Option Certificate :=
  ConversionCertificate.compose? (normalizationCertificates fuel term)

theorem normalizationEdges_allAccepted
    (fuel : Nat) (term : Term) (certificate : Certificate)
    (hmember : certificate ∈ normalizationEdges fuel term) :
    certificate.Accepted := by
  induction fuel generalizing term with
  | zero =>
      simp [normalizationEdges] at hmember
  | succ fuel ih =>
      cases hstep : firstStep? term with
      | none =>
          simp [normalizationEdges, hstep] at hmember
      | some first =>
          simp only [normalizationEdges, hstep, List.mem_cons] at hmember
          rcases hmember with hequal | hmember
          · subst certificate
            exact (firstStep?_sound term first hstep).2
          · exact ih first.target hmember

theorem normalizationEdges_chronological
    (fuel : Nat) (term : Term) :
    Chronological term (normalizationEdges fuel term) := by
  induction fuel generalizing term with
  | zero =>
      simp [normalizationEdges, Chronological]
  | succ fuel ih =>
      cases hstep : firstStep? term with
      | none =>
          simp [normalizationEdges, hstep, Chronological]
      | some first =>
          rw [normalizationEdges, hstep]
          change
            first.source = term ∧
              Chronological first.target
                (normalizationEdges fuel first.target)
          exact ⟨(firstStep?_sound term first hstep).1, ih first.target⟩

theorem normalizationCertificates_allAccepted
    (fuel : Nat) (term : Term) (certificate : Certificate)
    (hmember : certificate ∈ normalizationCertificates fuel term) :
    certificate.Accepted := by
  simp only [normalizationCertificates, List.mem_cons] at hmember
  rcases hmember with rfl | hmember
  · exact ConversionCertificate.refl_accepted term
  · exact normalizationEdges_allAccepted fuel term certificate hmember

theorem normalizationCertificates_chronological
    (fuel : Nat) (term : Term) :
    Chronological term (normalizationCertificates fuel term) := by
  change
    (ConversionCertificate.refl term).source = term ∧
      Chronological (ConversionCertificate.refl term).target
        (normalizationEdges fuel term)
  exact ⟨rfl, normalizationEdges_chronological fuel term⟩

theorem composeFrom?_exists_of_chronological
    (accumulator : Certificate) :
    ∀ (rest : List Certificate),
      Chronological accumulator.target rest →
        ∃ result,
          ConversionCertificate.composeFrom? accumulator rest = some result := by
  intro rest
  induction rest generalizing accumulator with
  | nil =>
      intro hchronological
      exact ⟨accumulator, rfl⟩
  | cons next tail ih =>
      intro hchronological
      rcases hchronological with ⟨hsource, htail⟩
      have hendpoints : accumulator.target = next.source := hsource.symm
      let combined :=
        ConversionCertificate.trans accumulator next hendpoints
      have htrans :
          ConversionCertificate.trans? accumulator next = some combined := by
        simp [ConversionCertificate.trans?, hendpoints, combined]
      have hcombinedChronological :
          Chronological combined.target tail := by
        simpa [combined, ConversionCertificate.trans] using htail
      obtain ⟨result, hresult⟩ :=
        ih combined hcombinedChronological
      exact
        ⟨result, by
          simp [ConversionCertificate.composeFrom?, htrans, hresult]⟩

theorem composeFrom?_source
    (accumulator result : Certificate) (rest : List Certificate)
    (hcompose :
      ConversionCertificate.composeFrom? accumulator rest = some result) :
    result.source = accumulator.source := by
  induction rest generalizing accumulator result with
  | nil =>
      simp [ConversionCertificate.composeFrom?] at hcompose
      subst result
      rfl
  | cons next tail ih =>
      cases htrans :
          ConversionCertificate.trans? accumulator next with
      | none =>
          simp [ConversionCertificate.composeFrom?, htrans] at hcompose
      | some combined =>
          have hcombinedSource :
              combined.source = accumulator.source := by
            by_cases hendpoints : accumulator.target = next.source
            · simp [ConversionCertificate.trans?, hendpoints] at htrans
              subst combined
              rfl
            · simp [ConversionCertificate.trans?, hendpoints] at htrans
          have htail :
              ConversionCertificate.composeFrom? combined tail =
                some result := by
            simpa [ConversionCertificate.composeFrom?, htrans] using hcompose
          exact (ih combined result htail).trans hcombinedSource

theorem normalizationCertificate?_exists
    (fuel : Nat) (term : Term) :
    ∃ certificate,
      normalizationCertificate? fuel term = some certificate := by
  have hchronological :
      Chronological (ConversionCertificate.refl term).target
        (normalizationEdges fuel term) := by
    simpa [ConversionCertificate.refl] using
      normalizationEdges_chronological fuel term
  obtain ⟨certificate, hcertificate⟩ :=
    composeFrom?_exists_of_chronological
      (ConversionCertificate.refl term)
      (normalizationEdges fuel term) hchronological
  exact
    ⟨certificate, by
      simpa [normalizationCertificate?, normalizationCertificates,
        ConversionCertificate.compose?] using hcertificate⟩

theorem normalizationCertificate?_sound
    (fuel : Nat) (term : Term) (certificate : Certificate)
    (hcertificate :
      normalizationCertificate? fuel term = some certificate) :
    certificate.source = term ∧ certificate.Accepted := by
  have haccepted : certificate.Accepted := by
    apply ConversionCertificate.compose?_sound
      (normalizationCertificates fuel term) certificate
    · exact normalizationCertificates_allAccepted fuel term
    · exact hcertificate
  have hcomposeFrom :
      ConversionCertificate.composeFrom?
          (ConversionCertificate.refl term)
          (normalizationEdges fuel term) =
        some certificate := by
    simpa [normalizationCertificate?, normalizationCertificates,
      ConversionCertificate.compose?] using hcertificate
  have hsource :=
    composeFrom?_source
      (ConversionCertificate.refl term) certificate
      (normalizationEdges fuel term) hcomposeFrom
  exact ⟨by simpa [ConversionCertificate.refl] using hsource, haccepted⟩

/-- A completed normal-form certificate is returned only when the terminal
endpoint has no remaining beta or eta step.  Fuel exhaustion therefore fails
closed instead of being confused with normalization. -/
def normalFormCertificate? (fuel : Nat) (term : Term) :
    Option Certificate := do
  let certificate ← normalizationCertificate? fuel term
  if firstStep? certificate.target = none then
    some certificate
  else
    none

theorem normalFormCertificate?_sound
    (fuel : Nat) (term : Term) (certificate : Certificate)
    (hcertificate :
      normalFormCertificate? fuel term = some certificate) :
    certificate.source = term ∧
      certificate.Accepted ∧
      firstStep? certificate.target = none := by
  cases hpath : normalizationCertificate? fuel term with
  | none =>
      simp [normalFormCertificate?, hpath] at hcertificate
  | some path =>
      by_cases hnormal : firstStep? path.target = none
      · simp [normalFormCertificate?, hpath, hnormal] at hcertificate
        subst certificate
        have hsound :=
          normalizationCertificate?_sound fuel term path hpath
        exact ⟨hsound.1, hsound.2, hnormal⟩
      · simp [normalFormCertificate?, hpath, hnormal] at hcertificate

/-- Two independently completed normal-form paths.  No convertibility claim is
made between their endpoints; this is the shape required for normalizing a
term and its expected type before a separate typing proof is checked. -/
structure NormalFormCertificatePair where
  left : Certificate
  right : Certificate

def normalFormCertificatePair?
    (fuel : Nat) (left right : Term) :
    Option NormalFormCertificatePair := do
  let leftCertificate ← normalFormCertificate? fuel left
  let rightCertificate ← normalFormCertificate? fuel right
  pure
    { left := leftCertificate
      right := rightCertificate }

theorem normalFormCertificatePair?_sound
    (fuel : Nat) (left right : Term)
    (certificate : NormalFormCertificatePair)
    (hcertificate :
      normalFormCertificatePair? fuel left right = some certificate) :
    certificate.left.source = left ∧
      certificate.right.source = right ∧
      certificate.left.Accepted ∧
      certificate.right.Accepted ∧
      firstStep? certificate.left.target = none ∧
      firstStep? certificate.right.target = none := by
  cases hleft : normalFormCertificate? fuel left with
  | none =>
      simp [normalFormCertificatePair?, hleft] at hcertificate
  | some leftCertificate =>
      cases hright : normalFormCertificate? fuel right with
      | none =>
          simp [normalFormCertificatePair?, hleft, hright] at hcertificate
      | some rightCertificate =>
          simp [normalFormCertificatePair?, hleft, hright] at hcertificate
          subst certificate
          have hleftSound :=
            normalFormCertificate?_sound fuel left leftCertificate hleft
          have hrightSound :=
            normalFormCertificate?_sound fuel right rightCertificate hright
          exact
            ⟨hleftSound.1, hrightSound.1,
              hleftSound.2.1, hrightSound.2.1,
              hleftSound.2.2, hrightSound.2.2⟩

/-- Two independently generated proof paths with an identical terminal normal
form.  This is data for the live conversion boundary, not a replacement for
checking either proof tree. -/
structure CommonNormalFormCertificate where
  left : Certificate
  right : Certificate

/-- Produce both proof trees and reject if either side exhausts fuel or if the
certified terminal endpoints differ. -/
def commonNormalFormCertificate?
    (fuel : Nat) (left right : Term) :
    Option CommonNormalFormCertificate := do
  let leftCertificate ← normalFormCertificate? fuel left
  let rightCertificate ← normalFormCertificate? fuel right
  if leftCertificate.target = rightCertificate.target then
    some
      { left := leftCertificate
        right := rightCertificate }
  else
    none

theorem commonNormalFormCertificate?_sound
    (fuel : Nat) (left right : Term)
    (certificate : CommonNormalFormCertificate)
    (hcertificate :
      commonNormalFormCertificate? fuel left right = some certificate) :
    certificate.left.source = left ∧
      certificate.right.source = right ∧
      certificate.left.target = certificate.right.target ∧
      certificate.left.Accepted ∧
      certificate.right.Accepted ∧
      firstStep? certificate.left.target = none ∧
      firstStep? certificate.right.target = none := by
  cases hleft : normalFormCertificate? fuel left with
  | none =>
      simp [commonNormalFormCertificate?, hleft] at hcertificate
  | some leftCertificate =>
      cases hright : normalFormCertificate? fuel right with
      | none =>
          simp [commonNormalFormCertificate?, hleft, hright] at hcertificate
      | some rightCertificate =>
          by_cases htargets :
              leftCertificate.target = rightCertificate.target
          · simp [commonNormalFormCertificate?, hleft, hright, htargets]
              at hcertificate
            subst certificate
            have hleftSound :=
              normalFormCertificate?_sound fuel left leftCertificate hleft
            have hrightSound :=
              normalFormCertificate?_sound fuel right rightCertificate hright
            exact
              ⟨hleftSound.1, hrightSound.1, htargets,
                hleftSound.2.1, hrightSound.2.1,
                hleftSound.2.2, hrightSound.2.2⟩
          · simp [commonNormalFormCertificate?, hleft, hright, htargets]
              at hcertificate

private def twoStepInput : Term :=
  .app
    (.lam (.srt .type)
      (.app (.lam (.srt .type) (.var 0)) (.var 0)))
    (.srt .kind)

/-- One unit of fuel exposes but does not discharge the second redex. -/
theorem twoStep_one_fuel_rejects_incomplete :
    normalFormCertificate? 1 twoStepInput = none := by
  rfl

/-- The same generic producer completes the two-step path with sufficient
fuel and exposes its exact terminal endpoint. -/
theorem twoStep_two_fuel_reaches_kind :
    (normalFormCertificate? 2 twoStepInput).map
        (fun certificate => certificate.target) =
      some (.srt .kind) := by
  rfl

#print axioms firstBetaStep?_sound
#print axioms firstEtaStep?_sound
#print axioms normalizationCertificate?_sound
#print axioms normalFormCertificate?_sound
#print axioms normalFormCertificatePair?_sound
#print axioms commonNormalFormCertificate?_sound
#print axioms twoStep_one_fuel_rejects_incomplete
#print axioms twoStep_two_fuel_reaches_kind

end Mettapedia.GSLT.LanguageDef.LFFirstOrderCertifiedNormalization
