import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.MutualInformation
import Mettapedia.InformationTheory.ShannonEntropy.Main
import Mettapedia.InformationTheory.EntropyKL
import Mettapedia.InformationTheory.FiniteBrierInformation
import Mettapedia.InformationTheory.CodebookRelativity
import Mettapedia.InformationTheory.FinitePriorCoding
import Mettapedia.InformationTheory.CountablePriorCoding
import Mettapedia.InformationTheory.AdditiveMessageValuation

/-!
# Information Theory (Entry Point)

This module collects the stable public entry points for the information-theory subproject.

At the moment, the main focus is finite Shannon entropy, mutual information / log-ratio
separation, and a curated bridge to the Knuth–Skilling (variational/KL) derivation.
-/
