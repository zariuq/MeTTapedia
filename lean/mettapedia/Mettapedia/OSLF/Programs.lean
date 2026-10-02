import Mettapedia.OSLF.Programs.NativeType
import Mettapedia.OSLF.Programs.LanguageDefInstance
import Mettapedia.OSLF.Programs.Completion
import Mettapedia.OSLF.Programs.GradualTypes
import Mettapedia.OSLF.Programs.GradualGuarantee
import Mettapedia.OSLF.Programs.DynamicGuarantee
import Mettapedia.OSLF.Programs.HoleEvaluation
import Mettapedia.OSLF.Programs.Composition

/-!
# OSLF applied to programs

OSLF generates a type system from a language.  These modules read that type
system at the level of individual programs, partial programs and their
compositions.

* `Programs.NativeType`: the native type of a program (its principal native
  predicate), its native and modal theories, the context-decorated modality,
  and how translation, forgetting and restriction act on them.
* `Programs.LanguageDefInstance`: the same facts for programs of a
  `LanguageDef`, with controls (native types finer than modal theories, steps
  not lifted through contexts, restriction gaining step-past formulas,
  language extension not reflecting steps).
* `Programs.Completion`: completion as satisfaction; completion spaces,
  refinement, consistency and abstraction as the theory–model Galois
  connection; typed holes whose completion types and obligations are OSLF's
  direct image and pullback.
* `Programs.GradualTypes`: Abstracting Gradual Typing as an instance:
  concretisation, precision, consistency, meet, abstraction, the Helly
  property and its failure with shared unknowns.
* `Programs.GradualGuarantee`: the static gradual guarantee, conservative
  extension and the dynamic embedding for a gradually typed λ-calculus.
* `Programs.DynamicGuarantee`: an evidence semantics for the same calculus,
  with evidence combined by meets, and both parts of the dynamic gradual
  guarantee.
* `Programs.HoleEvaluation`: evaluation around holes, hole closures,
  fill-and-resume, and its two failure modes.
* `Programs.Composition`: joint completions as global sections,
  holonomy-invariant completions, and joint realisability of observational
  views as amalgamation.
-/
