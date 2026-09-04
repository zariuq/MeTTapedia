import Mettapedia.Languages.TPTP.StatusSemantics
import Mettapedia.Languages.TPTP.NIKAuthority
import Mettapedia.Languages.TPTP.ProblemAuthority
import Mettapedia.Languages.TPTP.NIKDefault
import Mettapedia.Languages.TPTP.GroundCNFAuthority
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedAgreement
import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedAgreement
import Mettapedia.GSLT.LanguageDef.TptpNamedFofToNnfAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationNTT
import Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitNTT
import Mettapedia.GSLT.LanguageDef.TptpFofNnfShiftLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofPrenexLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofPrenexNormalizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionFileWordMachine
import Mettapedia.GSLT.LanguageDef.TptpOfficialResolvedGroundResolutionFileWordMachine

/-!
# TPTP and TSTP proof authority

This entry point exposes the fail-closed status vocabulary, the open family of
local rule authorities, chronological DAG replay, and whole-problem authority
composition.  Concrete TPTP dialects and rule registries remain responsible
for their own parsing, source authentication, semantic status meanings, and
global discharge theorems.

The FOF path refines the official grammar-shaped AST into a named semantic
formula, resolves binders to de Bruijn indices with fail-closed free-variable
handling, and then exposes normalization as a validated, source-preserving
GSLT with a proved semantic interpretation and generated native types.  The
AST elaborator and binder resolver are authored GSLT transformations with
exact forward agreement and no-invention theorems against independent semantic
functions.  The named and binder-resolved intermediates are validated inert
GSLTs; the binder-resolved carrier is a literal structural sublanguage of the
normalizer, and the composed stages have an end-to-end no-invention theorem.
The named carrier also has generated structural types.  None of these layers
is a proof-search strategy.

Canonical binder-resolved NNF remains the internal transformation carrier.
An authored capture-avoiding shift language traverses that carrier through
ordinary typed premises and agrees exactly with semantic de Bruijn shifting;
prenex conversion can therefore cross binders without a native shift opcode.
For interchange, an optional authored GSLT adds globally fresh binder
identities while preserving the canonical de Bruijn structure.  Its execution
agrees exactly with an independent semantic labeller, erases exactly to the
source NNF, and produces no additional results.  TPTP presentation mechanics
therefore refine the internal representation instead of dictating it.

The semantic clausification ladder now continues through a total prenex stage
and a disjoint-signature Skolem stage.  Prenexing preserves truth and the
principal signature in every nonempty first-order model.  Its inert target
language separates the quantifier-free matrix from the quantifier prefix, so
prenex shape is enforced by constructors rather than an unchecked field.
Skolemization
retains an explicit fresh-symbol frontier and dependency arity, eliminates
existentials, and is proved equisatisfiable with the original closed NNF after
composition.  This semantic core does not yet claim CNF conversion or select a
proof-search strategy.
-/
