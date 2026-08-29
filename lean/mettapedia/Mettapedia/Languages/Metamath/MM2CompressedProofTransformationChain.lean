import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

/-!
# Composable GSLT stages of compressed-verifier activation

The compressed verifier is assembled from small machines.  This module places
the first completed semantic seam in the general path-valued realization
category:

```text
finite ordered verifier inventory
              |
              | exact linked-row lowering
              v
successor-checked linked inventory
              |
              | reachability closure, then OSLF
              v
native modal theory of loader macro-steps
```

The stage processes the supplied verifier-rule presentation.  It does not
recognize a fixture identity, and it does not claim that the later compact
byte scanner or assertion machine is already connected by a general
realization.  Those are subsequent arrows in the same category.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofTransformationChain

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.FiniteInventoryLoader
open Mettapedia.GSLT.LinkedInventoryLoader
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.OSLF.Framework.IndexedModalFunctor

/-- The exact linked-row lowering, viewed in the more general category where
one source action may map to a finite target execution. -/
def verifierInventoryRealization :
    OperationalRealization
      (FiniteInventoryLoader.gslt Atom)
      (LinkedInventoryLoader.gslt Atom) :=
  OperationalRealization.ofTranslation
    compressedVerifierRulePresentation.linkedLowering.toOperational

/-- The complete authored rule-inventory route as a free-category execution
path. -/
def abstractInventoryRoute :
    ExecutionPath (FiniteInventoryLoader.gslt Atom)
      compressedVerifierRulePresentation.loaderInitial
      compressedVerifierRulePresentation.loaderTerminal :=
  rewritePathToExecutionPath compressedVerifierRulePresentation.loaderPath

/-- The complete successor-checked linked route as a free-category execution
path. -/
def linkedInventoryRoute :
    ExecutionPath (LinkedInventoryLoader.gslt Atom)
      compressedVerifierRulePresentation.linkedLoaderInitial
      compressedVerifierRulePresentation.linkedLoaderTerminal :=
  rewritePathToExecutionPath
    compressedVerifierRulePresentation.linkedLoaderPath

/-- The existing strict linked lowering maps a retained abstract path to the
independently defined linked path, step for step. -/
theorem lowerPath_agrees_translation :
    {source target : FiniteInventoryLoader.State Atom} ->
    (path : (FiniteInventoryLoader.gslt Atom).RewritePath source target) ->
    compressedVerifierRulePresentation.linkedLowering.toOperational.mapRoute
        (rewritePathToExecutionPath path) =
      rewritePathToExecutionPath (LinkedInventoryLoader.lowerPath path)
  | _, _, .nil _ => rfl
  | _, _, .cons step rest => by
      change
        Mettapedia.GSLT.Ultrainfinite.Route.cons
            ⟨LinkedInventoryLoader.lower_step step⟩
            (compressedVerifierRulePresentation.linkedLowering.toOperational.mapRoute
              (rewritePathToExecutionPath rest)) =
          Mettapedia.GSLT.Ultrainfinite.Route.cons
            ⟨LinkedInventoryLoader.lower_step step⟩
            (rewritePathToExecutionPath (LinkedInventoryLoader.lowerPath rest))
      exact congrArg
        (fun route => Mettapedia.GSLT.Ultrainfinite.Route.cons
          ⟨LinkedInventoryLoader.lower_step step⟩ route)
        (lowerPath_agrees_translation rest)

/-- The generic realization maps every retained abstract occurrence step to
the exact linked-row path already used by compressed-verifier activation. -/
theorem lowerPath_agrees_realization
    {source target : FiniteInventoryLoader.State Atom}
    (path : (FiniteInventoryLoader.gslt Atom).RewritePath source target) :
    verifierInventoryRealization.mapRoute
        (rewritePathToExecutionPath path) =
      rewritePathToExecutionPath (LinkedInventoryLoader.lowerPath path) := by
  change
    (OperationalRealization.ofTranslation
      compressedVerifierRulePresentation.linkedLowering.toOperational).mapRoute
        (rewritePathToExecutionPath path) =
      rewritePathToExecutionPath (LinkedInventoryLoader.lowerPath path)
  rw [OperationalRealization.mapRoute_ofTranslation]
  exact lowerPath_agrees_translation path

/-- The actual compressed-verifier inventory is therefore a living instance
of the reusable GSLT-to-GSLT stage, not a packet carried beside it. -/
theorem verifierInventoryRoute_maps_exactly :
    verifierInventoryRealization.mapRoute abstractInventoryRoute =
      linkedInventoryRoute := by
  exact lowerPath_agrees_realization
    compressedVerifierRulePresentation.loaderPath

/-- One-to-one linked lowering retains the number of proof-relevant
occurrence steps. -/
theorem verifierInventoryRoute_preserves_length :
    linkedInventoryRoute.length = abstractInventoryRoute.length := by
  calc
    linkedInventoryRoute.length =
        compressedVerifierRulePresentation.linkedLoaderPath.length :=
      rewritePathToExecutionPath_length
        compressedVerifierRulePresentation.linkedLoaderPath
    _ = compressedVerifierRulePresentation.loaderPath.length :=
      compressedVerifierRulePresentation.linkedLoaderPath_length
    _ = abstractInventoryRoute.length :=
      (rewritePathToExecutionPath_length
        compressedVerifierRulePresentation.loaderPath).symm

/-- OSLF applied after reachability closure yields the native modal transport
for the complete path-valued loader stage. -/
def verifierInventoryReachabilityNTT :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (LinkedInventoryLoader.gslt Atom).closure)
      (oslfForwardModalObject (FiniteInventoryLoader.gslt Atom).closure) :=
  verifierInventoryRealization.closureOSLFPullback

/-- A mutation of the supplied ordered rule inventory changes the terminal
state observed by this stage. -/
theorem mutated_inventory_changes_terminal
    {left right : FiniteVerifierRulePresentation}
    (different : left.rules ≠ right.rules) :
    left.loaderTerminal ≠ right.loaderTerminal :=
  FiniteVerifierRulePresentation.loaderTerminal_ne_of_rules_ne different

/-- Negative control: a skipped successor is not a linked-loader step and
therefore cannot be licensed by the realization. -/
theorem skipped_successor_is_not_a_stage_step
    (loaded : List Atom) (cursor wrong : Nat) (value : Atom)
    (remaining : List (LinkedInventoryLoader.Row Atom)) (terminal : Nat)
    (wrongSuccessor : wrong ≠ cursor + 1) :
    Not (Exists fun target => LinkedInventoryLoader.Step
      { loaded := loaded
        cursor := cursor
        remaining :=
          { position := cursor, successor := wrong, value := value } :: remaining
        terminal := terminal }
      target) :=
  LinkedInventoryLoader.wrong_successor_cannot_load loaded cursor wrong value
    remaining terminal wrongSuccessor

#print axioms verifierInventoryRoute_maps_exactly
#print axioms verifierInventoryRoute_preserves_length
#print axioms verifierInventoryReachabilityNTT
#print axioms mutated_inventory_changes_terminal
#print axioms skipped_successor_is_not_a_stage_step

end Mettapedia.Languages.Metamath.MM2CompressedProofTransformationChain
