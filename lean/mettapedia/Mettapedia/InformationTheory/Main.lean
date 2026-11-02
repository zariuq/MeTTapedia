import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.FiniteRecovery
import Mettapedia.InformationTheory.MarkovRecovery
import Mettapedia.InformationTheory.MutualInformation
import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mettapedia.InformationTheory.ConditionalMutualInformationBridges
import Mettapedia.InformationTheory.ShannonEntropy.Main
import Mettapedia.InformationTheory.EntropyKL
import Mettapedia.InformationTheory.FiniteBrierInformation
import Mettapedia.InformationTheory.CodebookRelativity
import Mettapedia.InformationTheory.FinitePriorCoding
import Mettapedia.InformationTheory.CountablePriorCoding
import Mettapedia.InformationTheory.AdditiveMessageValuation
import Mettapedia.InformationTheory.KnowledgeQuantification.Main

/-!
# Information Theory (Entry Point)

This module collects the stable public entry points for the information-theory subproject.

At the moment, the main focus is finite Shannon entropy, mutual information / log-ratio
separation, and a curated bridge to the Knuth–Skilling (variational/KL) derivation.
`KnowledgeQuantification` measures knowledge as standardized compression (Fanelli's `K`).
-/
