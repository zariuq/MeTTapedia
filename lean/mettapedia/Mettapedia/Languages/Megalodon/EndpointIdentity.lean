import Mettapedia.GSLT.LanguageDef.EndpointIdentityRealizations
import Mettapedia.Languages.Megalodon.SortedABTRefinement

/-!
# Exact Megalodon endpoint identity

Megalodon proof replay treats arbitrary named constants as term data and
uses the two-sorted ABT representation only for structural term identity and
binder operations.  This module turns the proved ABT lowering into the exact
endpoint identity required by NIK.

Publication hashes remain outside this layer.  A `.mg` or `.pfg` document
codec may wrap canonical content in a verified content envelope, but erasing
that content to a digest requires a separate collision-freedom premise.
-/

namespace Mettapedia.Languages.Megalodon.EndpointIdentity

open Mettapedia.GSLT.LanguageDef.EndpointIdentityRealizations
open Mettapedia.GSLT.LanguageDef.ExactEndpointCodec
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.Megalodon.MathdataKernel

abbrev PhysicalTerm :=
  Mettapedia.Languages.Megalodon.SortedABTRefinement.ABT

/-- Megalodon's sorted ABT lowering is a fail-closed canonical term codec. -/
def termCodec : PartialCodec Tm PhysicalTerm where
  encode := Mettapedia.Languages.Megalodon.SortedABTRefinement.encode
  decode := Mettapedia.Languages.Megalodon.SortedABTRefinement.decode?
  decode_encode :=
    Mettapedia.Languages.Megalodon.SortedABTRefinement.decode_encode

/-- Structural equality of sorted ABTs is exact equality for Megalodon
semantic terms. -/
def termIdentity : ExactEndpointIdentity Tm :=
  ofPartialCodec termCodec

/-- Arbitrary Megalodon names are retained as data below the `termNamed`
constructor, rather than becoming constructors of the checker language. -/
theorem named_term_lowers_as_data (name : Name) :
    termIdentity.identify (.named name) =
      .node .termNamed
        (.cons [] (.node (.dataName name) .nil) .nil) := by
  rfl

/-- The physical ABT identity decodes to the exact semantic term. -/
theorem term_identity_round_trip (term : Tm) :
    termCodec.decode (termIdentity.identify term) = some term := by
  exact Mettapedia.Languages.Megalodon.SortedABTRefinement.decode_encode term

/-! ## Separating canaries -/

namespace Canary

def nameA : Name :=
  "0000000000000000000000000000000000000000000000000000000000000001"

def nameB : Name :=
  "0000000000000000000000000000000000000000000000000000000000000002"

def namedA : Tm := .named nameA
def namedB : Tm := .named nameB

/-- Positive canary: a content-shaped name needs no constructor-table entry
to survive exact ABT lowering and decoding. -/
theorem content_name_round_trip :
    termCodec.decode (termIdentity.identify namedA) = some namedA := by
  exact term_identity_round_trip namedA

/-- Negative canary: distinct opaque names remain distinct endpoints. -/
theorem distinct_content_names_remain_distinct :
    termIdentity.identify namedA ≠ termIdentity.identify namedB := by
  intro sameIdentity
  have sameTerm := termIdentity.identify_injective sameIdentity
  exact (by decide : namedA ≠ namedB) sameTerm

/-- A function and its eta expansion may be related by conversion while
remaining different structural endpoints.  Endpoint identity must not
silently quotient by definitional equality. -/
def etaContracted : Tm := namedA

def etaExpanded : Tm :=
  .lam .prop (.app etaContracted (.db 0))

theorem eta_conversion_does_not_collapse_endpoint_identity :
    termIdentity.identify etaExpanded ≠
      termIdentity.identify etaContracted := by
  intro sameIdentity
  have sameTerm := termIdentity.identify_injective sameIdentity
  exact (by decide : etaExpanded ≠ etaContracted) sameTerm

end Canary

end Mettapedia.Languages.Megalodon.EndpointIdentity
