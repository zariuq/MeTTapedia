import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationControls

/-!
# Nontrivial inhabitants and the unrestricted authority-copying obstruction

The positive source consists of authored compiler-image code and one external
purse.  Its actual split COMM duplicates nonempty output code while consuming
the one funding cell.  In contrast, the existing unrestricted accepted grammar
admits a communicated purse whose duplication creates two active resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open ActivationCodeImage

def channel : CostName String := .quote .nil

def copyBody : CostTerm String :=
  .par (.drop (.bvar 0)) (.par (.drop (.bvar 0)) .nil)

def authoredSender : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PZero" []], authoredNonemptyPayload]

def sender : CostTerm String :=
  .signed (.send channel wrappedNonemptyPayload) {"a"}

def source : CostConfig String :=
  {wrappedCopyReceiver} + {sender} +
    {CostTerm.purse channel (.cons ({"a"} + {"a"}) .empty)}

def target : CostConfig String :=
  (copyBody.commSubst wrappedNonemptyPayload).components + {CostTerm.purse channel .empty}

/-- The sending endpoint is also an actual nonempty authored compiler image. -/
theorem sender_authored_image :
    AuthoredCodeImage exampleEncoding exampleSeal FreeSortContext.empty [] authoredSender sender := by
  refine ⟨.output (.quote .unit) authored_nonempty_payload_sorted, 12, ?_⟩
  decide +kernel

/-- Authored compiler-image endpoints plus separate located funding inhabit
the preserved operational domain. -/
theorem compiler_funded_source_separated : source.ResourceSeparated := by
  intro term member
  simp only [source, Multiset.mem_add, Multiset.mem_singleton] at member
  rcases member with (rfl | rfl) | rfl
  · exact authored_examples_admitted.1.purseFree
  · exact sender_authored_image.purseFree
  · rfl

/-- This inhabitant also meets the independent runtime and closed-scope
requirements; separation was not obtained by choosing unsupported code. -/
theorem compiler_funded_source_supported :
    ∀ term ∈ source, term.RuntimeSupported ∧ term.BinderSafe := by
  intro term member
  simp only [source, Multiset.mem_add, Multiset.mem_singleton] at member
  rcases member with (rfl | rfl) | rfl
  · exact ⟨authored_examples_runtime_admitted.1, authored_examples_runtime_admitted.2.1⟩
  · refine ⟨?_, .signed (.send (.quote .nil) authored_examples_runtime_admitted.2.2.2)⟩
    exact ⟨⟨trivial, authored_examples_runtime_admitted.2.2.1⟩, by simp [CostSig.RuntimeValid]⟩
  · exact ⟨⟨trivial, by simp [CostStack.RuntimeSupported, CostSig.RuntimeValid]⟩, .purse⟩

/-- The existing split rule communicates and duplicates the nonempty code. -/
theorem compiler_funded_source_fires :
    CostStep source channel ({"a"} + {"a"}) target := by
  simpa [source, target, sender, wrappedCopyReceiver, channel, copyBody,
    LocatedPurse.configComponents, LocatedPurse.toTerm] using
    (CostStep.split (context := (0 : CostConfig String)) (channel := channel)
      (body := copyBody) (payload := wrappedNonemptyPayload)
      (recvSeal := {"a"}) (sendSeal := {"a"})
      (by simp [CostSig.RuntimeValid]) (by simp [CostSig.RuntimeValid])
      (LocatedTokenCover.singleHead channel ({"a"} + {"a"})
        (by simp [CostSig.RuntimeValid]) .empty))

/-- Separation is inhabited after a real duplication, not just initially. -/
theorem compiler_funded_target_separated : target.ResourceSeparated :=
  compiler_funded_source_fires.preserves_resourceSeparated compiler_funded_source_separated

/-- The duplicated outputs remain sealed code; the one external purse is
depleted.  Two demanded atoms were supplied by a single physical cell. -/
theorem compiler_funded_physical_counts :
    source.physicalPurseCells = 1 ∧ target.physicalPurseCells = 0 ∧
      source.physicalPurseOccurrences = 1 ∧ target.physicalPurseOccurrences = 1 ∧
      ({"a"} + {"a"} : CostSig String).card = 2 := by
  simp [source, target, copyBody, sender, wrappedCopyReceiver, wrappedNonemptyPayload,
    CostTerm.commSubst, CostTerm.substitute, CostTerm.components,
    CostConfig.physicalPurseCells, CostConfig.physicalPurseOccurrences,
    CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure, CostStack.cellCount]

def unrestrictedOuter : CostName String := .signature {"o"}

def unrestrictedInner : CostName String := .signature {"i"}

def authorityPayload : CostTerm String :=
  .purse unrestrictedInner (.cons {"b"} .empty)

def unrestrictedRedex : CostTerm String :=
  .signed (.par (.recv unrestrictedOuter (.par (.drop (.bvar 0)) (.drop (.bvar 0))))
    (.send unrestrictedOuter authorityPayload)) {"a"}

def unrestrictedSource : CostConfig String :=
  {unrestrictedRedex} + {CostTerm.purse unrestrictedOuter (.cons {"a"} .empty)}

def unrestrictedTarget : CostConfig String :=
  {authorityPayload} + {authorityPayload} + {CostTerm.purse unrestrictedOuter .empty}

/-- The unrestricted relation really creates two active authority occurrences. -/
theorem unrestricted_source_fires :
    CostStep unrestrictedSource unrestrictedOuter {"a"} unrestrictedTarget := by
  simpa [unrestrictedSource, unrestrictedTarget, unrestrictedRedex,
    unrestrictedOuter, unrestrictedInner, authorityPayload] using
    ActivationControls.declarative_authority_payload_is_duplicated

/-- The accepted raw profile alone does not imply the physical invariant.
The declarative counterpart increases its active cells and purse occurrences. -/
theorem accepted_profile_does_not_imply_separation :
    ActivationControls.authorityDuplication.supported = true ∧
      ¬ unrestrictedSource.ResourceSeparated ∧
      unrestrictedSource.physicalPurseCells = 1 ∧ unrestrictedTarget.physicalPurseCells = 2 ∧
      unrestrictedSource.physicalPurseOccurrences = 1 ∧
      unrestrictedTarget.physicalPurseOccurrences = 3 := by
  refine ⟨ActivationControls.accepted_authority_payload_is_duplicated.1, ?_, ?_⟩
  · intro separated
    have free : unrestrictedRedex.PurseFree := separated unrestrictedRedex (by simp [unrestrictedSource])
    have cards := congrArg Multiset.card free
    simp [unrestrictedRedex, authorityPayload, unrestrictedOuter, unrestrictedInner,
      CostTerm.purseInventory, CostProc.purseInventory, CostName.purseInventory] at cards
  · simp [unrestrictedSource, unrestrictedTarget, unrestrictedRedex, authorityPayload,
      CostConfig.physicalPurseCells, CostConfig.physicalPurseOccurrences,
      CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure, CostStack.cellCount]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparationControls
