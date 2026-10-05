import Mettapedia.Languages.VibeITP.Spec.Basic
import Mettapedia.Languages.VibeITP.Spec.Kernel
import Mettapedia.Languages.VibeITP.Spec.Derivation
import Mettapedia.Languages.VibeITP.Spec.Instr
import Mettapedia.Languages.VibeITP.Spec.Encode
import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mettapedia.Languages.VibeITP.Spec.Controls
import Mettapedia.GSLT.LanguageDef.FirstOrderRules
import Mettapedia.Languages.VibeITP.Presentation.Syntax
import Mettapedia.Languages.VibeITP.Presentation.Rules
import Mettapedia.Languages.VibeITP.Presentation.Package
import Mettapedia.Languages.VibeITP.Presentation.Authority
import Mettapedia.Languages.VibeITP.Presentation.Decode
import Mettapedia.Languages.VibeITP.Presentation.Instances
import Mettapedia.Languages.VibeITP.Presentation.SpecFacts
import Mettapedia.Languages.VibeITP.Presentation.Meaning
import Mettapedia.Languages.VibeITP.Presentation.RuleShapes
import Mettapedia.Languages.VibeITP.Presentation.Theory
import Mettapedia.Languages.VibeITP.Presentation.SoundArith
import Mettapedia.Languages.VibeITP.Presentation.SoundTerms
import Mettapedia.Languages.VibeITP.Presentation.SoundTheorems
import Mettapedia.Languages.VibeITP.Presentation.SoundDefinitions
import Mettapedia.Languages.VibeITP.Presentation.SoundAdmissions
import Mettapedia.Languages.VibeITP.Presentation.KernelSoundness
import Mettapedia.Languages.VibeITP.Presentation.Validation
import Mettapedia.Languages.VibeITP.Presentation.Soundness
import Mettapedia.Languages.VibeITP.Presentation.TermShape
import Mettapedia.Languages.VibeITP.Presentation.CompleteArithmetic
import Mettapedia.Languages.VibeITP.Presentation.CompleteLists
import Mettapedia.Languages.VibeITP.Presentation.CompleteTerms
import Mettapedia.Languages.VibeITP.Presentation.OperationsWf
import Mettapedia.Languages.VibeITP.Presentation.CompleteLiterals
import Mettapedia.Languages.VibeITP.Presentation.CompleteShift
import Mettapedia.Languages.VibeITP.Presentation.CompleteSubstitution
import Mettapedia.Languages.VibeITP.Presentation.CompleteInstantiation
import Mettapedia.Languages.VibeITP.Presentation.CompleteDefinitions
import Mettapedia.Languages.VibeITP.Presentation.DerivedTermShape
import Mettapedia.Languages.VibeITP.Presentation.CompleteCorrespondence
import Mettapedia.Languages.VibeITP.Presentation.KernelControls

/-!
# Vibe-ITP

An independent specification of the Vibe-ITP proof kernel and its binary
checker protocol (`Spec`), and the kernel as an admitted NIK rule package
with soundness, constructive completeness, exact term-operation correspondence
and raw-article controls (`Presentation`). Static kernel derivability is
equivalent to acceptance by the actual theory-extended NIK checker.
-/
