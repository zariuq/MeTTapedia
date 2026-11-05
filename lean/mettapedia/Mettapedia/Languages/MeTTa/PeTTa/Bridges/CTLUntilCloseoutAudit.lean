import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanupControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundSyntax
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundData
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedViews
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedLoop
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverNegative
import Mettapedia.Machines.CTLUntilFiniteSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAuthoredProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceIteration
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRecursion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceResult
import Mettapedia.Logic.KernelFoundationManifest

/-! Joined foundation inventory for the bounded EU source close-out.

This audit includes the composed authored source-to-result theorem and its
initial-state and resource conditions. The full loop composition is proved
from actual source phases, not supplied as a law or a successful-run premise.
-/

set_option autoImplicit false

#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanupControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundSyntax
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundData
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedViews
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedLoop
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverNegative
#foundation_manifest_module Mettapedia.Machines.CTLUntilFiniteSupport
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAuthoredProgram
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopRound
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceIteration
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRecursion
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceResult

