import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofFamily
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDeclarationSpine

/-!
# Proof decoding preserves typing in every host

A host presentation receives the generic proof family by a rules morphism.
If its conversion separates dependent products and the connectives of the
interface are declared constants, decoding `Holds (p ⇒ q)` and
`Holds (∀ x : τ. φ)` preserves every displayed type.  The arguments of a
connective are recovered from its declaration, not from an assumed inversion
principle.

The same declaration spines recover the arguments of any declared constant of
simple type; preservation for first-order defining equations over the
interface uses them in the same way.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLGenericProofPreservation

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface FormationSensitiveHOLGenericProofFamily Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The connectives of an interface are declared constants at their simple
types. -/
structure DeclaredConnectives (source : LogicalSignature Base Const) where
  implicationName : DeclName
  implication_eq : source.implication = .const implicationName
  implication_lookup : source.rules.constantType implicationName =
    some (typeAt source.types 0 (.arr .prop (.arr .prop .prop)))
  universalName : HOL.Ty Base → DeclName
  universal_eq : ∀ type, source.universal type = .const (universalName type)
  universal_lookup : ∀ type, source.rules.constantType (universalName type) =
    some (typeAt source.types 0 (.arr (.arr type .prop) .prop))

section Host

variable (source : LogicalSignature Base Const) (proofName : DeclName)
  {R : Rules Tower.Head}

/-- Typings of the proof family hold in the host. -/
theorem host_typed (host : (rules source proofName).Morphism R (fun head => head))
    {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing (rules source proofName) Γ term type) : Typing R Γ term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead host

/-- A declared constant of the interface roots a declaration spine at its
simple type in the host. -/
theorem constantSpine (host : (rules source proofName).Morphism R (fun head => head))
    {name : DeclName} {type : HOL.Ty Base}
    (known : source.rules.constantType name = some (typeAt source.types 0 type))
    {n : Nat} (Γ : Tower.Ctx n) :
    DeclarationSpine R Γ (.const name) (typeAt source.types n type) := by
  have lookup : R.constantType name = some (typeAt source.types 0 type) := by
    simpa only [Tm.mapHead_id] using
      host.constantType ((sourceMorphism source proofName).constantType known)
  have formed : Typing R .nil (typeAt source.types 0 type) (sortTm Tower.zero) :=
    host_typed source proofName host
      (include_typed source proofName (typeAt_formed source type .nil))
  have spine := DeclarationSpine.constant (Γ := Γ) lookup formed
    (host.isUniverse (LevelTower.IsUniverse.sort Tower.zero))
  simpa only [liftClosed, typeAt_rename] using spine

/-- The proof family roots a declaration spine at `prop → Type` in the host. -/
theorem proofSpine (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none) {n : Nat} (Γ : Tower.Ctx n) :
    DeclarationSpine R Γ (.const proofName)
      (.pi (typeAt source.types n .prop) (sortTm Tower.zero)) := by
  have lookup : (rules source proofName).constantType proofName = some (proofType source) :=
    combinedType_of_signature source.rules (declarations source proofName) fresh
      (Signature.typeOf_insert_eq _ _ _)
  have hostLookup : R.constantType proofName = some (proofType source) := by
    simpa only [Tm.mapHead_id] using host.constantType lookup
  exact DeclarationSpine.constant (Γ := Γ) hostLookup
    (host_typed source proofName host (proofType_formed source proofName))
    (host.isUniverse (LevelTower.IsUniverse.sort (.max Tower.zero (.succ Tower.zero))))

end Host

/-- Applying a function declared at a simple arrow type recovers the argument
at the domain, the next spine at the codomain, and replay of the observed
adjustment. -/
theorem simpleArgument {source : LogicalSignature Base Const} {R : Rules Tower.Head}
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation R Γ)
    {function argument displayed : Tower.Tm n} {domain codomain : HOL.Ty Base}
    (spine : DeclarationSpine R Γ function (typeAt source.types n (.arr domain codomain)))
    (observed : Typing R Γ (.app function argument) displayed) :
    Typing R Γ argument (typeAt source.types n domain) ∧
      DeclarationSpine R Γ (.app function argument) (typeAt source.types n codomain) ∧
      ∀ {replacement}, Typing R Γ replacement (typeAt source.types n codomain) →
        Typing R Γ replacement displayed := by
  obtain ⟨typed, next, _, replay⟩ := spine.recoverApplication universes boundary formed observed
  simp only [inst0, typeAt_subst] at next replay
  exact ⟨typed, next, replay⟩

/-- A function declared at a simple arrow type, applied in its domain. -/
theorem simpleApp {source : LogicalSignature Base Const} {R : Rules Tower.Head}
    {n : Nat} {Γ : Tower.Ctx n} {function argument : Tower.Tm n}
    {domain codomain : HOL.Ty Base}
    (functionTyped : Typing R Γ function (typeAt source.types n (.arr domain codomain)))
    (argumentTyped : Typing R Γ argument (typeAt source.types n domain)) :
    Typing R Γ (.app function argument) (typeAt source.types n codomain) := by
  have applied := Typing.appElim functionTyped argumentTyped
  simpa only [inst0, typeAt_subst] using applied

section Formation

variable (source : LogicalSignature Base Const) (proofName : DeclName) {R : Rules Tower.Head}

/-- A dependent function type between small types is small. -/
theorem pi_zero_at (host : (rules source proofName).Morphism R (fun head => head)) {n : Nat} {Γ : Tower.Ctx n} {domain : Tower.Tm n}
    {codomain : Tower.Tm (n + 1)}
    (domainTyped : Typing R Γ domain (sortTm Tower.zero))
    (codomainTyped : Typing R (.snoc Γ domain) codomain (sortTm Tower.zero)) :
    Typing R Γ (.pi domain codomain) (sortTm Tower.zero) :=
  Typing.cumul
    (.piForm domainTyped (host.isUniverse (LevelTower.IsUniverse.sort Tower.zero)) codomainTyped
      (host.isUniverse (LevelTower.IsUniverse.sort Tower.zero))
      (host.join (LevelTower.Join.sorts Tower.zero Tower.zero)))
    (host.cumulative (fun valuation => by simp [LevelExpr.eval, LevelTower.zero]))

/-- The proof family at a proposition of the host is a small type. -/
theorem proof_formed_at (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none)
    {n : Nat} {Γ : Tower.Ctx n} {proposition : Tower.Tm n}
    (typed : Typing R Γ proposition (typeAt source.types n .prop)) :
    Typing R Γ (proof proofName proposition) (sortTm Tower.zero) :=
  Typing.appElim (proofSpine source proofName host fresh Γ).typing typed

theorem implication_formed_at (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none)
    {n : Nat} {Γ : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing R Γ p (typeAt source.types n .prop))
    (hq : Typing R Γ q (typeAt source.types n .prop)) :
    Typing R Γ (implicationFamily proofName p q) (sortTm Tower.zero) :=
  pi_zero_at source proofName host (proof_formed_at source proofName host fresh hp)
    ((proof_formed_at source proofName host fresh hq).weaken)

theorem universal_formed_at (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none)
    {n : Nat} {Γ : Tower.Ctx n} {type : HOL.Ty Base} {predicate : Tower.Tm n}
    (typed : Typing R Γ predicate (typeAt source.types n (.arr type .prop))) :
    Typing R Γ (universalFamily source proofName type predicate) (sortTm Tower.zero) := by
  have domain : Typing R Γ (typeAt source.types n type) (sortTm Tower.zero) :=
    host_typed source proofName host
      (include_typed source proofName (typeAt_formed source type Γ))
  have applied := Typing.appElim
    (typed.weaken (extension := typeAt source.types n type)) (Typing.var 0)
  have atVariable : Typing R (.snoc Γ (typeAt source.types n type))
      (.app (Presentation.rename wk predicate) (.var 0))
      (typeAt source.types (n + 1) .prop) := by
    simpa only [Presentation.rename, inst0, Presentation.subst, typeAt_rename,
      typeAt_subst] using applied
  exact pi_zero_at source proofName host domain
    (proof_formed_at source proofName host fresh atVariable)

end Formation

/-- Both decoder contractions preserve every displayed type in any host that
receives the proof family and separates dependent products. -/
theorem decoder_preserves (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none)
    (connectives : DeclaredConnectives source)
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {n : Nat} {Γ : Tower.Ctx n} {left right displayed : Tower.Tm n}
    (formed : ContextFormation R Γ) (observed : Typing R Γ left displayed)
    (decoder : DecoderStep source proofName left right) : Typing R Γ right displayed := by
  cases decoder with
  | implication p q =>
      obtain ⟨proposition, _, _, replay⟩ :=
        (proofSpine source proofName host fresh Γ).recoverApplication universes boundary
          formed observed
      have shape : rawImp source p q = .app (.app (.const connectives.implicationName) p) q := by
        simp only [rawImp, connectives.implication_eq, liftClosed, Presentation.rename]
      rw [shape] at proposition
      obtain ⟨_, _, inner, _, _, _⟩ := proposition.appGeneration
      obtain ⟨hp, next, _⟩ := simpleArgument universes boundary formed
        (constantSpine source proofName host connectives.implication_lookup Γ) inner
      obtain ⟨hq, _, _⟩ := simpleArgument universes boundary formed next proposition
      exact replay (implication_formed_at source proofName host fresh hp hq)
  | universal type predicate =>
      obtain ⟨proposition, _, _, replay⟩ :=
        (proofSpine source proofName host fresh Γ).recoverApplication universes boundary
          formed observed
      have shape : universalProposition source type predicate =
          .app (.const (connectives.universalName type)) predicate := by
        simp only [universalProposition, connectives.universal_eq, liftClosed,
          Presentation.rename]
      rw [shape] at proposition
      obtain ⟨typed, _, _⟩ := simpleArgument universes boundary formed
        (constantSpine source proofName host (connectives.universal_lookup type) Γ) proposition
      exact replay (universal_formed_at source proofName host fresh typed)

#print axioms constantSpine
#print axioms proofSpine
#print axioms simpleArgument
#print axioms simpleApp
#print axioms universal_formed_at
#print axioms decoder_preserves

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLGenericProofPreservation
