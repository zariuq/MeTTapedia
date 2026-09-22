/-
# Classifying every occurrence of a bound name

`OccurrenceDispatch.lean` supplies the mechanism: three routers, one per way a
bound name can be used, with the input clause proved for each. What it did not
supply is the classification — which occurrences of the bound name a body has,
and what each one needs.

This file supplies it, and writing it out produced a distinction the earlier
hand analysis had not separated.

## Four sites, and why quotation is different

```
    dropped, or carried            routed .data              fw
    used as a sending subject      routed .sendingSubject    br
    used as a listening subject    routed .listeningSubject  bl
    inside a quotation             insideQuotation           constructor chain
```

The first three are the routers. The fourth is not a router at all: an
occurrence inside a quotation has to be *rebuilt* into the surrounding code, and
that is what `assemble` does, priced by the arity law.

**The distinction that matters** is between an occurrence inside a *quotation*
and one inside a nested *input's body*. Both are "further in", and the earlier
hand analysis treated them together. They are not the same:

- A quotation is a name being constructed, so an occurrence inside one needs a
  constructor chain. `Src.out` sends `⌜Q⌝`, so every occurrence in its payload
  is a quotation site.
- A nested input's body is stored as a name but reached through the **proxy
  environment**, which `translate` already threads. So occurrences there are
  ordinary routed sites, one binder deeper.

`occurrenceSites` makes that split: the `out` payload contributes
`insideQuotation` sites, and the `inp` body recurses with the level raised.

## Soundness

`length_occurrenceSites` proves the classification finds exactly the
occurrences — its length is the direct count of the bound index, quotation
positions included. So nothing is missed and nothing is double-counted, which is
what a dispatch needs before it can be trusted to install one router per use.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.OccurrenceDispatch

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Sites -/

/-- What an occurrence of the bound name needs.  Three of the four are routers;
the fourth is a constructor chain, because an occurrence inside a quotation is a
name being built rather than a name being used. -/
inductive OccurrenceSite where
  | routed : Occurrence → OccurrenceSite
  | insideQuotation : OccurrenceSite
  deriving DecidableEq

/-! ## Counting the occurrences directly -/

mutual

/-- How many times the bound index occurs, quotation positions included. -/
def bvarCount (level : ℕ) : Src → ℕ
  | Src.nil => 0
  | Src.par p q => bvarCount level p + bvarCount level q
  | Src.out subject payload => bvarCountName level subject + bvarCount level payload
  | Src.inp subject body => bvarCountName level subject + bvarCount (level + 1) body
  | Src.drop subject => bvarCountName level subject

def bvarCountName (level : ℕ) : SrcName → ℕ
  | SrcName.quote p => bvarCount level p
  | SrcName.bvar index => if index = level then 1 else 0

end

/-! ## The classification -/

mutual

/-- **Every occurrence of the bound index, classified, in order.**  A subject
position gives a router; a quotation's contents give constructor sites; a nested
input's body recurses with the level raised, because the proxy environment
reaches it. -/
def occurrenceSites (level : ℕ) : Src → List OccurrenceSite
  | Src.nil => []
  | Src.par p q => occurrenceSites level p ++ occurrenceSites level q
  | Src.out subject payload =>
      occurrenceSitesSubject level Occurrence.sendingSubject subject
        ++ List.replicate (bvarCount level payload) OccurrenceSite.insideQuotation
  | Src.inp subject body =>
      occurrenceSitesSubject level Occurrence.listeningSubject subject
        ++ occurrenceSites (level + 1) body
  | Src.drop subject =>
      occurrenceSitesSubject level Occurrence.data subject

/-- A subject position: the bound index itself is a router site of the given
kind, and a quotation's contents are constructor sites. -/
def occurrenceSitesSubject (level : ℕ) (kind : Occurrence) :
    SrcName → List OccurrenceSite
  | SrcName.quote p =>
      List.replicate (bvarCount level p) OccurrenceSite.insideQuotation
  | SrcName.bvar index =>
      if index = level then [OccurrenceSite.routed kind] else []

end

/-! ## Soundness: the classification finds exactly the occurrences -/

theorem length_occurrenceSitesSubject (level : ℕ) (kind : Occurrence) :
    ∀ subject : SrcName,
      (occurrenceSitesSubject level kind subject).length
        = bvarCountName level subject
  | SrcName.quote p => by
      simp only [occurrenceSitesSubject, bvarCountName, List.length_replicate]
  | SrcName.bvar index => by
      simp only [occurrenceSitesSubject, bvarCountName]
      split <;> simp

/-- **Nothing is missed and nothing is double-counted.** -/
theorem length_occurrenceSites :
    ∀ (level : ℕ) (body : Src),
      (occurrenceSites level body).length = bvarCount level body
  | _, Src.nil => rfl
  | level, Src.par p q => by
      simp only [occurrenceSites, bvarCount, List.length_append,
        length_occurrenceSites level p, length_occurrenceSites level q]
  | level, Src.out subject payload => by
      simp only [occurrenceSites, bvarCount, List.length_append,
        List.length_replicate,
        length_occurrenceSitesSubject level Occurrence.sendingSubject subject]
  | level, Src.inp subject body => by
      simp only [occurrenceSites, bvarCount, List.length_append,
        length_occurrenceSitesSubject level Occurrence.listeningSubject subject,
        length_occurrenceSites (level + 1) body]
  | level, Src.drop subject => by
      simp only [occurrenceSites, bvarCount,
        length_occurrenceSitesSubject level Occurrence.data subject]

/-! ## The four sites, computed -/

theorem sites_drop :
    occurrenceSites 0 (Src.drop (SrcName.bvar 0))
      = [OccurrenceSite.routed Occurrence.data] := rfl

theorem sites_out (payload : Src) :
    occurrenceSites 0 (Src.out (SrcName.bvar 0) payload)
      = OccurrenceSite.routed Occurrence.sendingSubject
        :: List.replicate (bvarCount 0 payload) OccurrenceSite.insideQuotation := rfl

theorem sites_inp (body : Src) :
    occurrenceSites 0 (Src.inp (SrcName.bvar 0) body)
      = OccurrenceSite.routed Occurrence.listeningSubject
        :: occurrenceSites 1 body := rfl

/-- **A quotation position is a constructor site, not a router site.**  Sending
a process quotes it, so an occurrence in the payload has to be rebuilt into the
name being constructed. -/
theorem sites_inside_quotation :
    occurrenceSites 0 (Src.out (SrcName.quote (Src.drop (SrcName.bvar 0))) Src.nil)
      = [OccurrenceSite.insideQuotation] := rfl

/-- **A nested body is not a quotation position.**  It is reached through the
proxy environment, so its occurrences are ordinary router sites one binder
deeper — here the outer name is dropped inside an inner input's body. -/
theorem sites_nested_body :
    occurrenceSites 0
        (Src.inp (SrcName.quote Src.nil) (Src.drop (SrcName.bvar 1)))
      = [OccurrenceSite.routed Occurrence.data] := rfl

/-- No occurrence, no sites. -/
theorem sites_none : occurrenceSites 0 Src.nil = [] := rfl

/-! ## What each site costs -/

/-- A router site is one atom.  A quotation site's cost is the constructor
chain's, which the arity law prices against the shape being rebuilt rather than
by a constant. -/
def routedSiteCount (sites : List OccurrenceSite) : ℕ :=
  (sites.filter fun site =>
    match site with
    | .routed _ => true
    | .insideQuotation => false).length

theorem routedSiteCount_drop :
    routedSiteCount (occurrenceSites 0 (Src.drop (SrcName.bvar 0))) = 1 := rfl

theorem routedSiteCount_quotation :
    routedSiteCount
      (occurrenceSites 0
        (Src.out (SrcName.quote (Src.drop (SrcName.bvar 0))) Src.nil)) = 0 := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
