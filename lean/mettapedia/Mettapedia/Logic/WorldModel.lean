import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.Logic.WorldModel.Generative
import Mettapedia.Logic.WorldModel.Algorithmic
import Mettapedia.Logic.WorldModel.FeatureContainment
import Mettapedia.Logic.WorldModel.ContainmentEncoding
import Mettapedia.Logic.WorldModel.FeatureContainmentConstruction
import Mettapedia.Logic.WorldModel.FeatureContainmentCompilation
import Mettapedia.Logic.WorldModel.AlgorithmicConceptFormation
import Mettapedia.Logic.WorldModel.OpenEnded
import Mettapedia.Logic.WorldModel.OpenEndedAlgorithmic
import Mettapedia.Logic.WorldModel.CompressionTransfer
import Mettapedia.Logic.WorldModel.InferenceControl
import Mettapedia.Logic.WorldModel.GibbsCompletion

/-!
# General world-model calculus

This namespace contains the representation-neutral world-model interfaces.
They require neither probabilistic values nor PLN evidence.  Particular
revision disciplines—additive evidence, chronological updates, overlap-aware
fusion, and others—are downstream structures or instances.
-/
