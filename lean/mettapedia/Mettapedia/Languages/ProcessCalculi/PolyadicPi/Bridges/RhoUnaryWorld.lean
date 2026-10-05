import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryExecution
import Mettapedia.OSLF.Syntax.VariablePosition

/-!
# Nominal worlds for the concrete unary-to-rho spine

Source-name positions receive distinct quoted seeds below the allocator's
current seed. Extending a world uses the actual next seed and advances that
bound. Allocating a private implementation channel advances the same bound
without adding a source variable. The construction exists for every source
context, so the injectivity and freshness contracts have positive instances.

The shared infrastructure channels are free reserved names, whereas source
and allocated implementation names are quoted seeds. The actual rho channel
comparator separates these representations and reflects source-name identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryWorld

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryExecution
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-- A finite source context names distinct seeds already allocated. -/
structure SeedWorld (Γ : Ctx sig) where
  index : Var Γ .nm → Nat
  injective : Function.Injective index
  available : Nat
  below : ∀ name, index name < available

def SeedWorld.world {Γ : Ctx sig} (world : SeedWorld Γ) : World Γ 0 :=
  fun name => .allocated (world.index name)

/-- Every source context has an explicit initial nominal world. -/
def initial (Γ : Ctx sig) : SeedWorld Γ where
  index := fun name => (varIdx name).val
  injective := by
    intro first second same
    exact varIdx_injective first second (Fin.ext same)
  available := Γ.length
  below := fun name => (varIdx name).isLt

/-- Consuming one private implementation name does not change source names. -/
def SeedWorld.advance {Γ : Ctx sig} (world : SeedWorld Γ) : SeedWorld Γ where
  index := world.index
  injective := world.injective
  available := world.available + 1
  below := fun name => by have := world.below name; omega

/-- Extending the source context binds precisely the returned fresh seed. -/
def SeedWorld.extend {Γ : Ctx sig} (world : SeedWorld Γ) : SeedWorld (.nm :: Γ) where
  index := fun name => match name with
    | .zero => world.available
    | .succ old => world.index old
  injective := by
    intro first second same
    cases first with
    | zero =>
        cases second with
        | zero => rfl
        | succ old =>
            have below := world.below old
            change world.available = world.index old at same
            omega
    | succ old =>
        cases second with
        | zero =>
            have below := world.below old
            change world.index old = world.available at same
            omega
        | succ other =>
            exact congrArg Var.succ (world.injective same)
  available := world.available + 1
  below := by
    intro name
    cases name with
    | zero => change world.available < world.available + 1; omega
    | succ old => have below := world.below old; exact Nat.lt_trans below (Nat.lt_succ_self _)

@[simp] theorem SeedWorld.advance_world {Γ : Ctx sig} (world : SeedWorld Γ) :
    world.advance.world = world.world := rfl

@[simp] theorem SeedWorld.extend_world {Γ : Ctx sig} (world : SeedWorld Γ) :
    world.extend.world = allocatedWorld world.world world.available := by
  funext name
  cases name <;> rfl

/-- A reply may reach any pending source restriction. Its returned seed is
already below the current allocator token and must not name an earlier
source variable. The receiving binder, rather than a presumed request
ordering, determines this extension. -/
def SeedWorld.extendAt {Γ : Ctx sig} (world : SeedWorld Γ) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name) :
    SeedWorld (.nm :: Γ) where
  index := fun name => match name with
    | .zero => seed
    | .succ old => world.index old
  injective := by
    intro first second same
    cases first with
    | zero =>
        cases second with
        | zero => rfl
        | succ old => exact False.elim (fresh old same)
    | succ old =>
        cases second with
        | zero => exact False.elim (fresh old same.symm)
        | succ other => exact congrArg Var.succ (world.injective same)
  available := world.available
  below := by
    intro name
    cases name with
    | zero => exact returned
    | succ old => exact world.below old

@[simp] theorem SeedWorld.extendAt_world {Γ : Ctx sig} (world : SeedWorld Γ)
    (seed : Nat) (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name) :
    (world.extendAt seed returned fresh).world = allocatedWorld world.world seed := by
  funext name
  cases name <;> rfl

/-- The new private name cannot coincide with any currently available
source name, even under rho's structural name equations. -/
theorem SeedWorld.fresh {Γ : Ctx sig} (world : SeedWorld Γ) (name : Var Γ .nm) :
    ¬ StructuralCongruence (allocatedName world.available) (world.world name).term := by
  rw [SeedWorld.world, NameValue.term, allocatedName_equiv_iff]
  have below := world.below name
  omega

private theorem canonical_seed (index : Nat) : Canonical.canonicalize (seedCode index) = seedCode index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      rw [seedCode]
      change Canonical.canonicalize (.apply "POutput" [.apply "NQuote" [seedCode index], .apply "PZero" []]) = _
      rw [CanonicalStepperCompleteness.canonicalize_output]
      simp only [Canonical.canonicalize, ih]
      cases index <;> simp [seedCode, Canonical.normalizeQuote] <;> rfl

private theorem canonical_allocated (index : Nat) :
    Canonical.canonicalize (allocatedName index) = allocatedName index := by
  unfold allocatedName
  simp only [Canonical.canonicalize, canonical_seed]
  cases index <;> rfl

/-- The real rho channel comparator preserves the distinct seed identities. -/
theorem seed_match_iff (first second : Nat) :
    rhoCanonicalEquivalent (allocatedName first) (allocatedName second) = true ↔ first = second := by
  rw [rhoCanonicalEquivalent_iff, canonical_allocated, canonical_allocated]
  constructor
  · intro same
    exact (allocatedName_equiv_iff first second).mp (.alpha _ _ same)
  · rintro rfl
    rfl

/-- An actual matching user-channel pair names the same intrinsic source
variable, rather than merely two unrelated equal ground encodings. -/
theorem SeedWorld.match_iff {Γ : Ctx sig} (world : SeedWorld Γ) (first second : Var Γ .nm) :
    rhoCanonicalEquivalent (world.world first).term (world.world second).term = true ↔ first = second := by
  change rhoCanonicalEquivalent (allocatedName (world.index first)) (allocatedName (world.index second)) = true ↔ _
  rw [seed_match_iff]
  exact ⟨fun same => world.injective same, fun same => congrArg world.index same⟩

/-- Generated source names cannot synchronize with reserved allocator
infrastructure channels in the actual runtime comparator. -/
theorem seed_reserved_no_match (seed : Nat) (reserved : Reserved) :
    rhoCanonicalEquivalent (allocatedName seed) (reservedChannel reserved).term = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [rhoCanonicalEquivalent_iff, canonical_allocated]
  change (.apply "NQuote" [seedCode seed] : Pattern) ≠ .fvar reserved.label
  intro impossible
  cases impossible

/-- Fresh implementation-channel allocation remains outside the existing
source-name world after the allocator advances. -/
theorem SeedWorld.self_disjoint {Γ : Ctx sig} (world : SeedWorld Γ) (name : Var Γ .nm) :
    rhoCanonicalEquivalent (allocatedName world.available) (world.advance.world name).term = false := by
  apply Bool.eq_false_of_not_eq_true
  change rhoCanonicalEquivalent (allocatedName world.available) (allocatedName (world.index name)) ≠ true
  intro matched
  have same := (seed_match_iff world.available (world.index name)).mp matched
  have below := world.below name
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryWorld
