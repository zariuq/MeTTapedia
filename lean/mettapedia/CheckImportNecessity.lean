-- Deliberately does NOT import QuoteBoundaryDivergence.
-- TwoDepthRestorationApex.lean:2 imports it; ColourTagSeparation.lean:1 imports it.
-- Neither file references any declaration from it (only prose mentions).
-- This file checks whether everything they actually need is already reachable
-- from CostRestorationRelation alone.
import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.ContinuationRetyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

-- everything TwoDepthRestorationApex.lean actually uses:
#check @Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.ReflectiveContextSupport.isQuoteConstructor
#check @Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
#check @Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
#check @Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
#check @Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext
#check @Mettapedia.GSLT.LanguageDef.restorationDepthThroughContext
#check @Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan.CommonRestorationApex
#check @Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan.CommonRestorationApex.exists_forall₂_canonical_eq_of_map_perm
#check @List.perm_comp_forall₂
#check @Mettapedia.GSLT.LanguageDef.canonicalizeListByAt_eq_map
#check @Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents

-- everything ColourTagSeparation.lean actually uses:
#check @Mettapedia.GSLT.LanguageDef.costBaseConstructorTag
#check @Mettapedia.GSLT.LanguageDef.costWrappedConstructorTag
#check @Mettapedia.GSLT.LanguageDef.costBaseConstructorName
#check @Mettapedia.GSLT.LanguageDef.costWrappedConstructorName
#check @Mettapedia.GSLT.LanguageDef.costStaticReflectivePresentationDecl
#check @Mettapedia.GSLT.LanguageDef.CostStaticColor.hereditaryConstructorImage
#check @Mettapedia.GSLT.LanguageDef.costBaseConstructorName_ne_wrapped
