import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelCodeSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource

/-! Concrete actor linkage with the generated kernel before rho and actor
sources. Each extension checks its actual namespace and inherited bodies.
The kernel's exact heads leave mailbox-request to the rho adapter. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedSource

open SpaceSemantics (Program)
open BridgeKit Eval
open ErlangMailboxKernelSource (name emitted program)

def emittedPrefixes : List String := [name ++ ":"]
def kernelPrefixes : List String :=
  ["gslt:er-rho:mailbox-begin", "gslt:er-rho:mailbox-resume", "gslt:er-rho:mailbox-kernel"]
def rhoPrefixes : List String :=
  ["gslt:er-rho:perform", "gslt:er-rho:mailbox-request", "gslt:er-rho:complete-task"]
def actorPrefixes : List String := ["gslt:er-actor:"]
def portablePrefixes : List String := ["gslt:er-actor:choices-portable", "gslt:er-actor:continue-portable"]

def headAllowed (prefixes : List String) (head : String) : Bool :=
  !(prefixes.any fun start => head.startsWith start)

def rowAllowed (prefixes : List String) (row : SpaceSemantics.Equation) : Bool :=
  headAllowed prefixes row.head && codeWithin (headAllowed prefixes) row.body

def emittedLibrary : Library := ⟨ErlangControllerSource.library.runtime, emitted, emittedPrefixes⟩
def kernelLibrary : Library := ⟨emittedLibrary.runtime, program, kernelPrefixes⟩
def rhoLibrary : Library := ⟨kernelLibrary.runtime, ErlangControllerSource.rhoSource.program, rhoPrefixes⟩
def actorLibrary : Library := ⟨rhoLibrary.runtime, ErlangControllerSource.actorSource.program, actorPrefixes⟩
def portableLibrary : Library := ⟨actorLibrary.runtime, ErlangControllerSource.portableSource.program, portablePrefixes⟩

def runtime : Program := actorLibrary.runtime
def portableRuntime : Program := portableLibrary.runtime

private theorem emitted_rows (prefixes : List String)
    (wire : WirePlanSupport.Supported (headAllowed prefixes))
    (wrappers : CompleteEmissionSupport.wrapperHeads.all (headAllowed prefixes) = true)
    (heads : (CompleteEmission.entries name).all (headAllowed prefixes) = true) :
    emitted.equations.all (rowAllowed prefixes) = true := by
  have bodies := CompleteEmissionCodeSupport.entry_bodies_supported ErlangMailboxKernelSource.spec name
    (headAllowed prefixes) wire rfl wrappers
  apply List.all_eq_true.mpr
  intro row member
  have labels : row.head ∈ CompleteEmission.entries name := by
    simp only [emitted, CompleteEmission.program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [CompleteEmission.entries, CompleteEmission.beginEquation, CompleteEmission.runEquation,
      CompleteEmission.exploreEquation, CompleteEmission.edgesEquation]
  exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mp heads _ labels,
    List.all_eq_true.mp bodies row member⟩

private theorem kernel_rows (prefixes : List String)
    (wire : WirePlanSupport.Supported (headAllowed prefixes))
    (calls : ErlangMailboxKernelCodeSupport.heads.all (headAllowed prefixes) = true)
    (heads : program.equations.all (fun row => headAllowed prefixes row.head) = true) :
    program.equations.all (rowAllowed prefixes) = true := by
  have bodies := ErlangMailboxKernelCodeSupport.bodies_supported (headAllowed prefixes) wire calls
  apply List.all_eq_true.mpr
  intro row member
  exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mp heads row member, List.all_eq_true.mp bodies row member⟩

private theorem wire_supported (prefixes : List String)
    (checked : WirePlanSupport.tags.all (headAllowed prefixes) = true) :
    WirePlanSupport.Supported (headAllowed prefixes) := List.all_eq_true.mp checked

private theorem check_parts (library : Library) (prefixes : List String)
    (same : library.prefixes = prefixes)
    (binding : headAllowed prefixes "let" = true)
    (base : library.base.equations.all (rowAllowed prefixes) = true)
    (equations : library.source.equations.all (fun row => library.owns row.head) = true)
    (declarations : library.source.declarations.all (fun declaration =>
      (arrowHead declaration).all library.owns) = true) : library.check = true := by
  have inherited : library.inherited = headAllowed prefixes := by
    funext head
    simp only [Library.inherited, Library.owns, headAllowed, same]
  unfold Library.check
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, declarations⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, equations⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [inherited]
    exact binding
  · rw [inherited]
    exact base

theorem emitted_checked : emittedLibrary.check = true := by
  apply check_parts emittedLibrary emittedPrefixes rfl (by decide +kernel)
  · have plain : ErlangControllerSource.library.runtime.equations.all (rowAllowed emittedPrefixes) = true := by decide +kernel
    exact plain
  · decide +kernel
  · decide +kernel

theorem kernel_checked : kernelLibrary.check = true := by
  apply check_parts kernelLibrary kernelPrefixes rfl (by decide +kernel)
  · have plain : ErlangControllerSource.library.runtime.equations.all (rowAllowed kernelPrefixes) = true := by decide +kernel
    have emittedPart := emitted_rows kernelPrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    change (ErlangControllerSource.library.runtime.equations ++ emitted.equations).all (rowAllowed kernelPrefixes) = true
    simp only [List.all_append, plain, emittedPart, Bool.true_and]
  · decide +kernel
  · decide +kernel

theorem rho_checked : rhoLibrary.check = true := by
  apply check_parts rhoLibrary rhoPrefixes rfl (by decide +kernel)
  · have plain : ErlangControllerSource.library.runtime.equations.all (rowAllowed rhoPrefixes) = true := by decide +kernel
    have emittedPart := emitted_rows rhoPrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have kernelPart := kernel_rows rhoPrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    change ((ErlangControllerSource.library.runtime.equations ++ emitted.equations) ++ program.equations).all (rowAllowed rhoPrefixes) = true
    simp only [List.all_append, plain, emittedPart, kernelPart, Bool.true_and]
  · decide +kernel
  · decide +kernel

theorem actor_checked : actorLibrary.check = true := by
  apply check_parts actorLibrary actorPrefixes rfl (by decide +kernel)
  · have plain : ErlangControllerSource.library.runtime.equations.all (rowAllowed actorPrefixes) = true := by decide +kernel
    have emittedPart := emitted_rows actorPrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have kernelPart := kernel_rows actorPrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have rhoPart : ErlangControllerSource.rhoSource.program.equations.all (rowAllowed actorPrefixes) = true := by decide +kernel
    change (((ErlangControllerSource.library.runtime.equations ++ emitted.equations) ++ program.equations) ++ ErlangControllerSource.rhoSource.program.equations).all (rowAllowed actorPrefixes) = true
    simp only [List.all_append, plain, emittedPart, kernelPart, rhoPart, Bool.true_and]
  · decide +kernel
  · decide +kernel

theorem portable_checked : portableLibrary.check = true := by
  apply check_parts portableLibrary portablePrefixes rfl (by decide +kernel)
  · have plain : ErlangControllerSource.library.runtime.equations.all (rowAllowed portablePrefixes) = true := by decide +kernel
    have emittedPart := emitted_rows portablePrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have kernelPart := kernel_rows portablePrefixes (wire_supported _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have rhoPart : ErlangControllerSource.rhoSource.program.equations.all (rowAllowed portablePrefixes) = true := by decide +kernel
    have actorPart : ErlangControllerSource.actorSource.program.equations.all (rowAllowed portablePrefixes) = true := by decide +kernel
    change ((((ErlangControllerSource.library.runtime.equations ++ emitted.equations) ++ program.equations) ++ ErlangControllerSource.rhoSource.program.equations) ++ ErlangControllerSource.actorSource.program.equations).all (rowAllowed portablePrefixes) = true
    simp only [List.all_append, plain, emittedPart, kernelPart, rhoPart, actorPart, Bool.true_and]
  · decide +kernel
  · decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedSource
