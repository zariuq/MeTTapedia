import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.CertifiedMask
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.PrefixProperties

/-!
# Source-derived typed graph decoders

This is the ideal integration boundary.  A compiler consumes an authenticated
checked GSLT, one selected source profile, and a fixed document context.  Its
output carries both the atomic refinement root and the identities of the
inputs that produced it.  There is no language-mode Boolean.

The semantic crowns below compose existing refinement laws with a contextual
admission boundary.  They do not claim that a concrete PeTTa or MM2 compiler
already exists; construction of such a value requires the concrete compiler
and all of its correspondence proofs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SourceDerivedDecoder

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.PrefixProperties

universe uContext uArtifact uState uHole uHead uProgram

/-- Identity-bearing output of a GSLT-to-refinement compiler. -/
structure CompiledRoot where
  sourceIdentity : SourceIdentity
  profileName : String
  profileVersion : String
  contextIdentity : String
  actionEncodingIdentity : String
  root : AtomicRoot

/-- A source compiler is an ordinary fail-closed function.  Concrete
correctness is supplied by the `DerivedDecoder` fields below, not assumed by
this function type. -/
abbrev Compiler (Context : Type uContext) :=
  CheckedGSLT → SourceProfile → Context → Option CompiledRoot

/-- Complete idealized decoder package.  The package is intentionally
contextual: the generated fragment may rely on a fixed PeTTa prelude or MM2
runtime suffix, and only the composed artifact is judged admissible. -/
structure DerivedDecoder where
  Context : Type uContext
  Artifact : Type uArtifact
  checked : CheckedGSLT
  profile : SourceProfile
  profileMember : profile ∈ checked.source.profiles.entries
  context : Context
  contextIdentity : String
  actionEncodingIdentity : String
  compiler : Compiler Context
  package : CompiledRoot
  compiled : compiler checked profile context = some package
  sourceIdentityBound : package.sourceIdentity = checked.source.identity
  profileNameBound : package.profileName = profile.name
  profileVersionBound : package.profileVersion = profile.version
  contextIdentityBound : package.contextIdentity = contextIdentity
  actionEncodingBound :
    package.actionEncodingIdentity = actionEncodingIdentity
  laws : AtomicRootLaws package.root
  compose : Context → package.root.Program → Artifact
  admitted : Artifact → Prop
  contextual_iff : ∀ program,
    package.root.wellFormed program ↔ admitted (compose context program)

/-!
The refinement interface has a budget-indexed terminal-decode property, so a
single fixed-budget field would be the wrong abstraction.  The helper
structure below supplies the correctly quantified version and is the public
ideal decoder used by the crowns.
-/

/-- Quantified terminal decoding supplement for a source-derived package. -/
structure IdealDecoder extends DerivedDecoder where
  terminalDecodeTotalAll : ∀ budget,
    TerminalDecodeTotalAt package.root.asRefinementInterface budget

namespace IdealDecoder

variable (decoder : IdealDecoder)

abbrev interface : RefinementInterface :=
  decoder.package.root.asRefinementInterface

def contextualProperty (program : decoder.package.root.Program) : Prop :=
  decoder.admitted (decoder.compose decoder.context program)

/-- Accepted generated fragments are admissible only after composition with
the fixed source context recorded by the decoder package. -/
theorem accepts_contextuallyAdmissible
    {budget : Nat}
    {trace : List decoder.package.root.asRefinementInterface.Action}
    {program : decoder.package.root.Program}
    (accepted : decoder.package.root.asRefinementInterface.Accepts
      budget trace program) :
    decoder.admitted (decoder.compose decoder.context program) := by
  have wellFormed : decoder.package.root.wellFormed program :=
    RefinementLaws.accepts_sound decoder.laws.interfaceLaws accepted
  exact (decoder.contextual_iff program).mp wellFormed

/-- Every contextually admitted in-budget artifact has its canonical trace. -/
theorem contextuallyAdmissible_canonical
    {budget : Nat} (budgetOK : decoder.package.root.budgetOK budget)
    (program : decoder.package.root.Program)
    (admitted : decoder.admitted (decoder.compose decoder.context program))
    (cost : decoder.package.root.programCost program ≤ budget) :
    decoder.package.root.asRefinementInterface.Accepts budget
      (decoder.package.root.encode program) program := by
  have wellFormed : decoder.package.root.wellFormed program :=
    (decoder.contextual_iff program).mpr admitted
  exact RefinementLaws.wellFormed_reachable decoder.laws.interfaceLaws
    budgetOK wellFormed cost

/-- The ideal package supplies exact accepted-prefix semantics, not merely
terminal-state productivity. -/
theorem prefixExactAt (budget : Nat)
    (budgetOK : decoder.package.root.budgetOK budget) :
    PrefixProperties.PrefixExactAt
      decoder.package.root.asRefinementInterface budget :=
  laws_prefixExactAt decoder.laws.interfaceLaws budgetOK
    (decoder.terminalDecodeTotalAll budget)

/-- Every canonical contextual artifact retains every prefix. -/
theorem canonicalPrefixesPreservedAt (budget : Nat)
    (budgetOK : decoder.package.root.budgetOK budget) :
    PrefixProperties.CanonicalPrefixesPreservedAt
      decoder.package.root.asRefinementInterface budget :=
  laws_canonicalPrefixesPreservedAt decoder.laws.interfaceLaws budgetOK

/-- A certified semantic hard mask cannot remove an accepted contextual
trace.  This combines source-derived admission with the existing certified
mask recall theorem. -/
theorem certifiedMask_preserves_contextual_trace
    (hardMask : SearchNode decoder.interface → Prop)
    (certified : CertifiedHardMask decoder.contextualProperty hardMask)
    {budget : Nat}
    {trace : List decoder.package.root.asRefinementInterface.Action}
    {program : decoder.package.root.Program}
    (accepted : decoder.package.root.asRefinementInterface.Accepts
      budget trace program) :
    EveryPrefixRetained hardMask budget trace := by
  apply certifiedHardMask_preserves_accepted_trace certified accepted
  exact decoder.accepts_contextuallyAdmissible accepted

/-- A complete legal-action ranking may change search order but not the set of
accepted contextual artifacts. -/
theorem ranking_invariant
    (first second : decoder.package.root.State →
      List (RefineAction decoder.package.root.Hole decoder.package.root.Head))
    (firstExact : ∀ state action,
      action ∈ first state ↔
        action ∈ decoder.package.root.legalActions state)
    (permutation : ∀ state, (first state).Perm (second state))
    {budget : Nat}
    {trace : List
      (RefineAction decoder.package.root.Hole decoder.package.root.Head)}
    {program : decoder.package.root.Program} :
    decoder.package.root.asRefinementInterface.RankedAccepts
        first budget trace program ↔
      decoder.package.root.asRefinementInterface.RankedAccepts
        second budget trace program :=
  decoder.laws.rankedAcceptance_invariant_of_legalActions
    first second firstExact permutation

/-- An authenticated package cannot simultaneously claim a different source
identity. -/
theorem rejects_different_source_identity
    (different : SourceIdentity)
    (changed : different ≠ decoder.checked.source.identity) :
    decoder.package.sourceIdentity ≠ different := by
  rw [decoder.sourceIdentityBound]
  exact Ne.symm changed

/-- The action linearization is part of the compiled artifact identity; a
different encoding cannot be silently substituted. -/
theorem rejects_different_action_encoding
    (different : String)
    (changed : different ≠ decoder.actionEncodingIdentity) :
    decoder.package.actionEncodingIdentity ≠ different := by
  rw [decoder.actionEncodingBound]
  exact Ne.symm changed

#print axioms accepts_contextuallyAdmissible
#print axioms contextuallyAdmissible_canonical
#print axioms prefixExactAt
#print axioms canonicalPrefixesPreservedAt
#print axioms certifiedMask_preserves_contextual_trace
#print axioms ranking_invariant
#print axioms rejects_different_source_identity
#print axioms rejects_different_action_encoding

end IdealDecoder

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SourceDerivedDecoder
