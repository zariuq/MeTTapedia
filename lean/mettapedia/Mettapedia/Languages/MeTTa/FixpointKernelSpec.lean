import Mettapedia.Languages.MeTTa.InductiveKernelHook

/-!
# Minimal Structural Fixpoint Contract Above Ordinary Families

This file adds the first future-facing structural recursion / fixpoint contract
above the ordinary strictly-positive family hook.

It does **not** implement fixpoints in `MeTTa-Pure`.
It only packages the smallest theoremic interface we would want the future
kernel extension to expose:

- structural recursion on one designated argument
- a named recursor contract
- a named equation theorem contract
- an explicit erasure/relevance declaration

We intentionally defer:
- general recursion
- cofixpoints
- guarded/corecursive productivity
- induction-recursion
- quotient/HIT eliminators
- semantic normalization for recursive definitions
-/

namespace Mettapedia.Languages.MeTTa

/-- The first minimal recursion discipline we are willing to expose. -/
inductive FixpointRecursionKind where
  | structural
deriving DecidableEq, Repr

/-- Very small erasure contract for the first recursive definitions. -/
inductive FixpointErasureKind where
  | proofOnly
  | runtimeRelevant
deriving DecidableEq, Repr

/-- Kernel-facing hook for the first structural recursive definitions. -/
structure StructuralFixpointKernelHook where
  functionName : String
  codomainFamilyName : String
  recursionKind : FixpointRecursionKind
  majorArgumentIndex : Nat
  recursorContractStub : String
  equationTheoremStub : String
  erasureKind : FixpointErasureKind
deriving DecidableEq, Repr

/-- Ordinary-family interfaces admit the first fixpoint hook exactly when they
already allow structural recursion. -/
def PureInductiveKernelInterface.admitsStructuralFixpoint
    (iface : PureInductiveKernelInterface) : Prop :=
  iface.hook.allowsStructuralRecursion = true

instance (iface : PureInductiveKernelInterface) :
    Decidable iface.admitsStructuralFixpoint := by
  unfold PureInductiveKernelInterface.admitsStructuralFixpoint
  infer_instance

/-- The first future-facing interface for structurally recursive definitions
over ordinary families. -/
structure StructuralFixpointKernelInterface where
  domain : PureInductiveKernelInterface
  hook : StructuralFixpointKernelHook
  admissible : domain.admitsStructuralFixpoint
  recursor_stub_agrees :
    hook.recursorContractStub = domain.recursorContractStub

theorem StructuralFixpointKernelInterface.domainFamilyName_eq
    (iface : StructuralFixpointKernelInterface) :
    iface.domain.hook.familyName = iface.domain.family.name := by
  exact iface.domain.familyName_eq

theorem StructuralFixpointKernelInterface.structural_only
    (iface : StructuralFixpointKernelInterface) :
    iface.hook.recursionKind = .structural := by
  cases iface with
  | mk domain hook admissible recursor_stub_agrees =>
      cases hook
      rfl

/-- Build the first structural fixpoint interface from an admissible ordinary
family interface. -/
def mkStructuralFixpointKernelInterface
    (domain : PureInductiveKernelInterface)
    (h : domain.admitsStructuralFixpoint)
    (functionName codomainFamilyName equationTheoremStub : String)
    (majorArgumentIndex : Nat)
    (erasureKind : FixpointErasureKind := .runtimeRelevant) :
    StructuralFixpointKernelInterface :=
  { domain := domain
    hook :=
      { functionName := functionName
        codomainFamilyName := codomainFamilyName
        recursionKind := .structural
        majorArgumentIndex := majorArgumentIndex
        recursorContractStub := domain.recursorContractStub
        equationTheoremStub := equationTheoremStub
        erasureKind := erasureKind }
    admissible := h
    recursor_stub_agrees := rfl }

/-- Starter fixpoint candidate: `Nat.isZero : Nat -> Bool`. -/
def natIsZeroFixpointInterface : StructuralFixpointKernelInterface :=
  mkStructuralFixpointKernelInterface
    natPureKernelInterface
    (by simpa [PureInductiveKernelInterface.admitsStructuralFixpoint]
      using natPureKernelInterface.structuralRecursion_enabled)
    "Nat.isZero"
    boolPureKernelInterface.family.name
    "Nat.isZero.eqns"
    0
    .runtimeRelevant

/-- Starter fixpoint candidate: `Nat.pred : Nat -> Nat`. -/
def natPredFixpointInterface : StructuralFixpointKernelInterface :=
  mkStructuralFixpointKernelInterface
    natPureKernelInterface
    (by simpa [PureInductiveKernelInterface.admitsStructuralFixpoint]
      using natPureKernelInterface.structuralRecursion_enabled)
    "Nat.pred"
    natPureKernelInterface.family.name
    "Nat.pred.eqns"
    0
    .runtimeRelevant

/-- Starter recursion inventory. -/
def starterStructuralFixpoints : List StructuralFixpointKernelInterface :=
  [natIsZeroFixpointInterface, natPredFixpointInterface]

theorem natPureKernelInterface_admitsStructuralFixpoint :
    natPureKernelInterface.admitsStructuralFixpoint := by
  simpa [PureInductiveKernelInterface.admitsStructuralFixpoint]
    using natPureKernelInterface.structuralRecursion_enabled

theorem natIsZeroFixpoint_domain :
    natIsZeroFixpointInterface.domain.family.name = "Nat" := by
  change natPureKernelInterface.family.name = "Nat"
  exact natPureKernelInterface_familyName

theorem natIsZeroFixpoint_codomain :
    natIsZeroFixpointInterface.hook.codomainFamilyName = "Bool" := by
  rw [show natIsZeroFixpointInterface.hook.codomainFamilyName =
      boolPureKernelInterface.family.name by rfl]
  exact boolPureKernelInterface_familyName

theorem natIsZeroFixpoint_recursor :
    natIsZeroFixpointInterface.hook.recursorContractStub = "Nat.rec" := by
  rw [show natIsZeroFixpointInterface.hook.recursorContractStub =
      natPureKernelInterface.recursorContractStub by rfl]
  exact natPureKernelInterface_recursorStub

theorem natIsZeroFixpoint_equations :
    natIsZeroFixpointInterface.hook.equationTheoremStub = "Nat.isZero.eqns" := by
  rfl

theorem natIsZeroFixpoint_majorArgument :
    natIsZeroFixpointInterface.hook.majorArgumentIndex = 0 := by
  rfl

theorem natPredFixpoint_domain :
    natPredFixpointInterface.domain.family.name = "Nat" := by
  exact natPureKernelInterface_familyName

theorem natPredFixpoint_codomain :
    natPredFixpointInterface.hook.codomainFamilyName = "Nat" := by
  rw [show natPredFixpointInterface.hook.codomainFamilyName =
      natPureKernelInterface.family.name by rfl]
  exact natPureKernelInterface_familyName

theorem natPredFixpoint_recursor :
    natPredFixpointInterface.hook.recursorContractStub = "Nat.rec" := by
  rw [show natPredFixpointInterface.hook.recursorContractStub =
      natPureKernelInterface.recursorContractStub by rfl]
  exact natPureKernelInterface_recursorStub

theorem natPredFixpoint_equations :
    natPredFixpointInterface.hook.equationTheoremStub = "Nat.pred.eqns" := by
  rfl

theorem natPredFixpoint_majorArgument :
    natPredFixpointInterface.hook.majorArgumentIndex = 0 := by
  rfl

theorem starterStructuralFixpoints_nonempty :
    starterStructuralFixpoints ≠ [] := by
  decide

theorem starterStructuralFixpoints_structural :
    ∀ iface ∈ starterStructuralFixpoints, iface.hook.recursionKind = .structural := by
  intro iface hiface
  simp [starterStructuralFixpoints] at hiface
  rcases hiface with hiface | hiface
  · subst hiface
    exact natIsZeroFixpointInterface.structural_only
  · subst hiface
    exact natPredFixpointInterface.structural_only

end Mettapedia.Languages.MeTTa
