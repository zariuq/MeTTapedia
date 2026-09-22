/-!
# Current CeTTa runtime: inspected artifacts, not a language determination

`prime` and `metta-prime` are existing runtime selector spellings. Their
presence does not select the mathematical design of Prime. This module
records limited source inspections, separately from `PrimeCandidates`.

The snapshots below are provenance data, not soundness certificates. No theorem
identifies the C implementation with a candidate calculus. No runtime tests
are claimed by this snapshot. Source digests are required because a commit
identifier alone does not describe a concurrently edited worktree.

Inspected facts at the first snapshot:

* `src/lang.c` registers the two selector spellings.
* `src/prime_need.h` declares persistent branch-local snapshots, explicit
  cell/cache states, and receipt event kinds.
* `src/prime_semantics.h` distinguishes canonicalizing a telescope from
  proving its formation and declares a conversion-certificate replay API.

These are API/source observations, not exhaustive semantic characterization.
The later snapshot inspects computed conversion, mathematical formation,
typed inhabitant publication, and an imported unit-superposition checker.
Source inspection and unexecuted experiment proposals do not establish native
J, HOL interpretation, or qualification of all reasoning-service interfaces.
The `Calibration` subdirectory preserves named V1 package and certificate
specimens and their wire spellings. Their fragment-level adequacy must not be
promoted into a claim about the complete runtime or an adopted type theory.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent

structure SourceDigest where
  relativeFile : String
  sha256 : String
  deriving DecidableEq, Repr

structure InspectedSourceSnapshot where
  date : String
  repositoryRevision : String
  files : List SourceDigest
  deriving Repr

def inspected20260909 : InspectedSourceSnapshot where
  date := "2026-09-09"
  repositoryRevision := "12da03b4"
  files := [
    ⟨"src/lang.c", "ee151029360adb46991874a29f638e759fbe064913a780cb60c670330ec6e99b"⟩,
    ⟨"src/prime_need.h", "aaca5de7705a768a62b0b24a379254aa74a9c706d1873a8ded8278b22c31967f"⟩,
    ⟨"src/prime_need.c", "d0c7b4200e74e1d8f1ce2cf0a327740af4b2f93a1da7c046e3187add8592807e"⟩,
    ⟨"src/prime_semantics.h", "88b26ea2f067f3db46a982b6f90ffcbe1f825c28d129be8b4a051710fa282d26"⟩,
    ⟨"src/prime_semantics.c", "fe3c71ace7378efcddded9dfc453367abdf2462f3211f28af67193f2a0e422c4"⟩]

/-- The five earlier file digests were rechecked and unchanged. Added files
describe further source surfaces; no executable or test result is pinned. -/
def inspected20260910 : InspectedSourceSnapshot where
  date := "2026-09-10"
  repositoryRevision := "12da03b4b055bfecff2add505e7e1ad4125bb352"
  files := inspected20260909.files ++ [
    ⟨"src/he_typing.c", "3177b49be55ba5ebfc3cefccf572492d066dc7c87ef8115265cf10efcb8bfe7d"⟩,
    ⟨"src/session.c", "6204d9b9041d9c8cc64dd40419d16097d74e360ce1b3bf2ad8d33eadc41a72be"⟩,
    ⟨"lib/lib_atp.metta", "fca40d0f8ee3f727c0fbd33d56af78beb75c734bbd8e2db73dc5ae1cdcde31d9"⟩,
    ⟨"lib/atp/superposition.metta", "e01bcd2650999f17de69e97b63b859ad69b845b83a6fe8b093b46343c43f2c37"⟩]

/-- A source-level observation is tied to a file in its snapshot. The
membership proof certifies provenance bookkeeping, not truth of the prose
observation or conformance of the native implementation. -/
structure SourceObservation (snapshot : InspectedSourceSnapshot) where
  source : SourceDigest
  sourceInSnapshot : source ∈ snapshot.files
  symbols : List String
  observation : String
  limitation : String

def needAPI20260909 : SourceObservation inspected20260909 where
  source := ⟨"src/prime_need.h", "aaca5de7705a768a62b0b24a379254aa74a9c706d1873a8ded8278b22c31967f"⟩
  sourceInSnapshot := by decide
  symbols := ["PrimeNeedSnapshot", "PrimeNeedReceiptEvent", "PrimeOccurrence"]
  observation := "The API exposes branch snapshots, cell identities, receipt occurrence IDs, resampling and effect events."
  limitation := "Header declarations and comments do not prove execution equations, event preservation or revision-safe reuse."

def conversionAPI20260909 : SourceObservation inspected20260909 where
  source := ⟨"src/prime_semantics.h", "88b26ea2f067f3db46a982b6f90ffcbe1f825c28d129be8b4a051710fa282d26"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_semantics_canonicalize_type", "prime_semantics_replay_conversion_certificate"]
  observation := "The API distinguishes a canonical Pi/Var ABT from evidence of source formation and declares conversion-certificate replay."
  limitation := "This observation neither selects a logical judgment nor establishes that C implements a particular Lean conversion checker."

def observations20260909 : List (SourceObservation inspected20260909) :=
  [needAPI20260909, conversionAPI20260909]

def computedConversion20260910 : SourceObservation inspected20260910 where
  source := ⟨"src/prime_semantics.c", "fe3c71ace7378efcddded9dfc453367abdf2462f3211f28af67193f2a0e422c4"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_convert", "prime_replay_conversion_certificate_budgeted",
    "prime_semantics_replay_conversion_certificate"]
  observation := "Convert recomputes two normal forms and calls atom_eq; replay checks the certificate's Original, NormalForms, Equal/Distinct and fixed fragment fields with marked user type functions disabled. Successful replay may certify Distinct with equal_out false."
  limitation := "The replay API has no separately supplied expected claim, premise revision or package digest. Certificate-internal conversion is not native J, K/UIP, or an object-HOL derivation; callers must supply any additional claim/currentness binding."

def mathematicalFormation20260910 : SourceObservation inspected20260910 where
  source := ⟨"src/prime_semantics.c", "fe3c71ace7378efcddded9dfc453367abdf2462f3211f28af67193f2a0e422c4"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_form_type", "prime_semantics_canonicalize_type",
    "prime_check_or_analyze"]
  observation := "Form accepts the listed primitive type symbols, checks named telescope domains before extending binder scope, and can return a closed canonical Pi/idx ABT. Every expression headed by Type returns Undetermined with universes-deferred; Check first requires expected-type formation and then exact/structural checking."
  limitation := "Bare Type formation and declared-type inference do not establish a universe hierarchy, a simple/dependent/set-model interpretation or HOL induction. Canonicalization alone remains separate from formation; no native inhabitant of a represented HOL proposition is established."

def judgmentOperations20260910 : SourceObservation inspected20260910 where
  source := ⟨"src/prime_semantics.c", "fe3c71ace7378efcddded9dfc453367abdf2462f3211f28af67193f2a0e422c4"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_judge_raw", "prepare_answer_bag", "prime_may_or_must"]
  observation := "The dispatcher handles Form/Synth/Check/Analyze/Convert/Refine/May/Must with Established/Refuted/Undetermined/Incomplete. Producer-authored Complete bags do not certify closure. May accepts a typed value witness; Must checks successful values, counts failures separately, and requires evaluator-certified completion and at least one value."
  limitation := "Unknown judgments are Undetermined, not refutations. These value-type verdicts are not the generated OSLF meaning of the candidate service protocol, and source branches are not a tested all-input runtime refinement. Explicit budgets bound producers; structural work is not uniformly rejected at small budgets."

def dependentProfiles20260910 : SourceObservation inspected20260910 where
  source := ⟨"src/session.c", "6204d9b9041d9c8cc64dd40419d16097d74e360ce1b3bf2ad8d33eadc41a72be"⟩
  sourceInSnapshot := by decide
  symbols := ["CETTA_PROFILE_HE_PRIME_VALUE", "CETTA_PROFILE_PRIME_DEFAULT_VALUE"]
  observation := "The HE he-prime profile and the separate Prime default profile both enable dependent-telescope operations. The two records retain distinct language identifiers and profile names."
  limitation := "A shared operation flag neither identifies these dialects nor selects the candidate's mathematical host or admission judgment."

def inhabitantRechecking20260910 : SourceObservation inspected20260910 where
  source := ⟨"src/he_typing.c", "3177b49be55ba5ebfc3cefccf572492d066dc7c87ef8115265cf10efcb8bfe7d"⟩
  sourceInSnapshot := by decide
  symbols := ["chain_proof_checked", "chain_unify_must", "chain_process_result",
    "answer_identity_v2_make", "he_typing_dispatch"]
  observation := "Before publishing a typed search result, the implementation re-infers the candidate proof's types and requires exact/structural matching to the goal, rejecting cyclic bindings. It then canonicalizes proof, answer substitution and type together. Native and ATP-guided scheduling share this rechecking path; finite depth misses and incomplete search have separate results."
  limitation := "This is checked inhabitation over supplied declarations, not an external HOL proof-byte checker. Its returned answer has no premise-revision field. The generic check-type operation permits consistency edges that this inhabitant path excludes; neither surface is silently equated with Prime Check or the candidate intrinsic proof service."

def importedATPLibrary20260910 : SourceObservation inspected20260910 where
  source := ⟨"lib/lib_atp.metta", "fca40d0f8ee3f727c0fbd33d56af78beb75c734bbd8e2db73dc5ae1cdcde31d9"⟩
  sourceInSnapshot := by decide
  symbols := ["import!", "./atp/resolution", "./atp/kbo", "./atp/superposition"]
  observation := "The explicit ATP library imports separate resolution, ordering and unit-superposition modules. These are imported library programs rather than extra prime-judge cases."
  limitation := "An import list is not proof of the library algorithms or their translation into the candidate source theory. No library execution was performed for this inspection."

def unitSuperposition20260910 : SourceObservation inspected20260910 where
  source := ⟨"lib/atp/superposition.metta", "e01bcd2650999f17de69e97b63b859ad69b845b83a6fe8b093b46343c43f2c37"⟩
  sourceInSnapshot := by decide
  symbols := ["atp:superposition:check-unit-step", "atp:superposition:check-unit-original",
    "atp:superposition:check-unit-rewrite"]
  observation := "The imported unit-clause checker applies an explicit substitution, requires its position and ordering validators, rejects original-variable rewrite positions, reconstructs the replacement, and compares the claimed child clause."
  limitation := "This is a unit-clause certificate algorithm, not unrestricted proof search, a general HOL checker or a native J eliminator. Its source inspection and existing control fixtures do not provide a Lean correspondence theorem or fresh test result."

def observations20260910 : List (SourceObservation inspected20260910) :=
  [computedConversion20260910, mathematicalFormation20260910,
    judgmentOperations20260910, dependentProfiles20260910,
    inhabitantRechecking20260910, importedATPLibrary20260910,
    unitSuperposition20260910]

end Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent
