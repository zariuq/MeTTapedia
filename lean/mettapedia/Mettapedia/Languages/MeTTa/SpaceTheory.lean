import Mettapedia.Languages.MeTTa.SpaceTheory.Presentation
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeValidation
import Mettapedia.Languages.MeTTa.SpaceTheory.EquationalPresentation
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeEquality
import Mettapedia.Languages.MeTTa.SpaceTheory.BagMatching
import Mettapedia.Languages.MeTTa.SpaceTheory.DialectBase
import Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveOnTheStep
import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform
import Mettapedia.Languages.MeTTa.SpaceTheory.HEArgumentPaths
import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotPaths
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalOnTheStep
import Mettapedia.Languages.MeTTa.SpaceTheory.Modules
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleOccurrences
import Mettapedia.Languages.MeTTa.SpaceTheory.EffectfulModules
import Mettapedia.Languages.MeTTa.SpaceTheory.HEModuleModes
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaModuleModes
import Mettapedia.Languages.MeTTa.SpaceTheory.HeadWriteProtocol
import Mettapedia.Languages.MeTTa.SpaceTheory.Renaming
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeRenaming
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection
import Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaObservationReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.HEObservationReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledEquationalFrontier
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalExamples
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveExamples
import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExamples
import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotExamples
import Mettapedia.Languages.MeTTa.SpaceTheory.LiteralExamples
import Mettapedia.Languages.MeTTa.SpaceTheory.GroundEquationBoundary
import Mettapedia.Languages.MeTTa.SpaceTheory.RhoDirectComparison
import Mettapedia.Languages.MeTTa.SpaceTheory.RhoEncoded
import Mettapedia.Languages.MeTTa.SpaceTheory.Extension
import Mettapedia.GSLT.Contracts.OccurrenceSupports
import Mettapedia.GSLT.LanguageDef.EquationComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportSimulation

/-!
# A MeTTa space as a theory

Atoms can be inspected as written, interpreted as function definitions and
type assignments, or read modulo the declared equations. These observations
need not identify the same atoms. The presented space supplies declarations
to the dialect's own evaluation rules; there is no common default evaluation
strategy. The imports below keep the distinct logical, operational, and
module judgments over that common source.
-/
