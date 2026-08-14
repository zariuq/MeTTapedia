import Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCost
import Mettapedia.GSLT.Parsing.HornCertificate
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Independent witnesses for repetition-admitted lookup caching

The cache policy is not justified by Metamath repetition alone.  This module
instantiates the same executable semantics with two existing, independent
MeTTapedia language objects: finite Horn clauses and typed MeTTaIL rewrite
rules.  Their values have unrelated structure; only stable identity lookup and
call-local repetition are shared.
-/

namespace Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheWitnesses

open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation
open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCost
open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.OSLF.MeTTaIL.Syntax

private def hornHead : Atom :=
  { relation := "reachable"
    arguments := .cons (.var 0) .nil }

private def hornBody : Atom :=
  { relation := "edge"
    arguments := .cons (.var 0) .nil }

private def hornRule : Rule :=
  { name := "reachable-from-edge"
    head := hornHead
    body := [hornBody] }

private def hornEnvironment : Environment String Rule where
  lookup
    | "reachable-from-edge" => some hornRule
    | _ => none

private def repeatedLookupCostModel : Model :=
  { classification := 1
    sourceLookup := 100
    cacheHit := 2
    promotion := 20
    retainedValue := 10 }

example : run hornEnvironment initial {}
    ["reachable-from-edge", "reachable-from-edge", "reachable-from-edge"] =
    some ([hornRule, hornRule, hornRule],
      { seen := ["reachable-from-edge"]
        resolved := [("reachable-from-edge", hornRule)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

example : run hornEnvironment initial {} ["unknown-clause"] = none := by
  rfl

example : promote? hornEnvironment
    ["reachable-from-edge", "reachable-from-edge", "reachable-from-edge"]
    repeatedLookupCostModel =
    some ([hornRule, hornRule, hornRule],
      { seen := ["reachable-from-edge"]
        resolved := [("reachable-from-edge", hornRule)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

private def typedRewrite : RewriteRule :=
  RewriteRule.mk "typed-successor-identity"
    [("x", .base "Natural")]
    []
    (.apply "successor" [.fvar "x"])
    (.apply "successor" [.fvar "x"])

private def rewriteEnvironment : Environment String RewriteRule where
  lookup
    | "typed-successor-identity" => some typedRewrite
    | _ => none

example : run rewriteEnvironment initial {}
    ["typed-successor-identity", "typed-successor-identity",
      "typed-successor-identity"] =
    some ([typedRewrite, typedRewrite, typedRewrite],
      { seen := ["typed-successor-identity"]
        resolved := [("typed-successor-identity", typedRewrite)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

example : run rewriteEnvironment initial {} ["unknown-rewrite"] = none := by
  rfl

example : promote? rewriteEnvironment
    ["typed-successor-identity", "typed-successor-identity",
      "typed-successor-identity"] repeatedLookupCostModel =
    some ([typedRewrite, typedRewrite, typedRewrite],
      { seen := ["typed-successor-identity"]
        resolved := [("typed-successor-identity", typedRewrite)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

end Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheWitnesses
