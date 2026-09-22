import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypingGeneration

/-!
# Declaration-aware presentations

Global constants and declaration-specific computation extend the same
parameterized typing judgment. A signature does not define a second typing calculus: it
supplies the `constantType` and `RootComputation` fields of `Rules`.

The construction is deliberately monotone.  Extending a signature preserves
every old entry and every old root computation, so typing derivations transport
by theorem.  Conversely, the empty signature recovers the underlying rules.
-/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration

/-- A closed global declaration.  A missing value denotes an opaque constant. -/
structure Entry (Head : Type) where
  type : Tm Head 0
  value? : Option (Tm Head 0) := none
  deriving Repr

/-- A raw global signature.  Its root computation must already carry the
renaming and substitution closure needed by conversion under binders. -/
structure Signature (Head : Type) where
  entries : DeclName → Option (Entry Head)
  computation : RootComputation Head := RootComputation.empty

/-- The empty signature adds neither constants nor computation. -/
def Signature.empty : Signature Head where
  entries := fun _ => none

/-- Look up the declared type of a global constant. -/
def Signature.typeOf? (signature : Signature Head) (name : DeclName) :
    Option (Tm Head 0) :=
  (signature.entries name).map Entry.type

/-- Look up the optional definiens of a global constant. -/
def Signature.valueOf? (signature : Signature Head) (name : DeclName) :
    Option (Tm Head 0) :=
  (signature.entries name).bind Entry.value?

/-- Insert or replace one global declaration without changing the licensed
root-computation family. -/
def Signature.insert (signature : Signature Head) (name : DeclName)
    (entry : Entry Head) : Signature Head where
  entries := fun candidate =>
    if candidate = name then some entry else signature.entries candidate
  computation := signature.computation

/-- Earlier declarations shadow later declarations. -/
def Signature.ofList (declarations : List (DeclName × Entry Head)) :
    Signature Head :=
  declarations.foldr (fun declaration signature =>
    signature.insert declaration.1 declaration.2) Signature.empty

@[simp] theorem Signature.computation_ofList (declarations : List (DeclName × Entry Head)) :
    (Signature.ofList declarations).computation = RootComputation.empty := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      simpa only [Signature.ofList, List.foldr, Signature.insert] using ih

/-- A successful selected value lookup comes from a name in the finite
declaration inventory, with the existing first-match shadowing policy. -/
theorem Signature.valueOf_name_mem (declarations : List (DeclName × Entry Head))
    {name : DeclName} {value : Tm Head 0}
    (known : (Signature.ofList declarations).valueOf? name = some value) :
    name ∈ declarations.map Prod.fst := by
  induction declarations with
  | nil => simp [Signature.ofList, Signature.empty, Signature.valueOf?] at known
  | cons declaration declarations ih =>
      by_cases same : name = declaration.1
      · simp [same]
      · apply List.mem_cons_of_mem
        apply ih
        simpa [Signature.ofList, Signature.valueOf?, Signature.insert, same] using known

@[simp] theorem Signature.typeOf_empty (name : DeclName) :
    Signature.empty.typeOf? (Head := Head) name = none := rfl

@[simp] theorem Signature.valueOf_empty (name : DeclName) :
    Signature.empty.valueOf? (Head := Head) name = none := rfl

@[simp] theorem Signature.typeOf_insert_eq (signature : Signature Head)
    (name : DeclName) (entry : Entry Head) :
    (signature.insert name entry).typeOf? name = some entry.type := by
  simp [Signature.typeOf?, Signature.insert]

@[simp] theorem Signature.valueOf_insert_eq (signature : Signature Head)
    (name : DeclName) (entry : Entry Head) :
    (signature.insert name entry).valueOf? name = entry.value? := by
  simp [Signature.valueOf?, Signature.insert]

/-- Signature extension preserves declaration identity, not merely the type
readout, and includes every previously licensed root-computation step. -/
structure Signature.Extends (prior later : Signature Head) : Prop where
  entries : ∀ {name : DeclName} {entry : Entry Head},
    prior.entries name = some entry → later.entries name = some entry
  computation : ∀ {n : Nat} {left right : Tm Head n},
    prior.computation.step left right → later.computation.step left right

theorem Signature.Extends.refl (signature : Signature Head) :
    signature.Extends signature where
  entries := fun equality => equality
  computation := fun step => step

theorem Signature.Extends.trans {first second third : Signature Head}
    (firstSecond : first.Extends second) (secondThird : second.Extends third) :
    first.Extends third where
  entries := fun equality => secondThird.entries (firstSecond.entries equality)
  computation := fun step =>
    secondThird.computation (firstSecond.computation step)

/-- Appending a source suffix retains every selected prefix declaration,
including an opaque declaration shadowing a later transparent one. -/
theorem Signature.entries_ofList_append (priorEntries suffix : List (DeclName × Entry Head))
    (name : DeclName) :
    (Signature.ofList (priorEntries ++ suffix)).entries name =
      ((Signature.ofList priorEntries).entries name).orElse
        (fun _ => (Signature.ofList suffix).entries name) := by
  induction priorEntries with
  | nil => rfl
  | cons declaration priorEntries ih =>
      by_cases same : name = declaration.1 <;>
        simp [Signature.ofList, Signature.insert, same] at ih ⊢ <;> exact ih

theorem Signature.ofList_extends_append (priorEntries suffix : List (DeclName × Entry Head)) :
    (Signature.ofList priorEntries).Extends (Signature.ofList (priorEntries ++ suffix)) where
  entries := by
    intro name entry selected
    rw [Signature.entries_ofList_append, selected]
    rfl
  computation := by
    intro n left right impossible
    rw [Signature.computation_ofList] at impossible
    exact impossible.elim

theorem Signature.entries_ofList_mem (entries : List (DeclName × Entry Head))
    {name : DeclName} {entry : Entry Head}
    (selected : (Signature.ofList entries).entries name = some entry) :
    (name, entry) ∈ entries := by
  induction entries with
  | nil => simp [Signature.ofList, Signature.empty] at selected
  | cons declaration entries ih =>
      by_cases same : name = declaration.1
      · have value : declaration.2 = entry := by
          simpa [Signature.ofList, Signature.insert, same] using selected
        exact List.mem_cons.mpr (Or.inl (Prod.ext same value.symm))
      · exact List.mem_cons.mpr (Or.inr (ih (by
          simpa [Signature.ofList, Signature.insert, same] using selected)))

theorem Signature.Extends.typeOf {prior later : Signature Head}
    (extension : prior.Extends later) {name : DeclName} {type : Tm Head 0}
    (typing : prior.typeOf? name = some type) :
    later.typeOf? name = some type := by
  unfold Signature.typeOf? at typing ⊢
  cases priorEntry : prior.entries name with
  | none => simp [priorEntry] at typing
  | some entry =>
      have typeEquality : entry.type = type := by
        simpa [priorEntry] using typing
      have laterEntry := extension.entries priorEntry
      simp [laterEntry, typeEquality]

theorem Signature.Extends.valueOf {prior later : Signature Head}
    (extension : prior.Extends later) {name : DeclName} {value : Tm Head 0}
    (unfolding : prior.valueOf? name = some value) :
    later.valueOf? name = some value := by
  unfold Signature.valueOf? at unfolding ⊢
  cases priorEntry : prior.entries name with
  | none => simp [priorEntry] at unfolding
  | some entry =>
      have valueEquality : entry.value? = some value := by
        simpa [priorEntry] using unfolding
      have laterEntry := extension.entries priorEntry
      simp [laterEntry, valueEquality]

/-! ## Extending one rules package -/

/-- Declaration computation consists of inherited computation, delta
unfolding for declared values, and additional signature-licensed equations. -/
inductive RootStep (base : Rules Head) (signature : Signature Head) (n : Nat) :
    Tm Head n → Tm Head n → Prop where
  | inherited {left right : Tm Head n} :
      base.computation.step left right → RootStep base signature n left right
  | delta {name : DeclName} {value : Tm Head 0} :
      signature.valueOf? name = some value →
      RootStep base signature n (.const name) (liftClosed value)
  | declared {left right : Tm Head n} :
      signature.computation.step left right →
      RootStep base signature n left right

/-- The structurally closed root computation induced by a signature. -/
def rootComputation (base : Rules Head) (signature : Signature Head) :
    RootComputation Head where
  step := RootStep base signature _
  rename := by
    intro n m rho left right step
    cases step with
    | inherited inherited =>
        exact .inherited (base.computation.rename rho inherited)
    | delta unfolding =>
        simpa only [rename, rename_liftClosed] using
          (RootStep.delta (n := m) unfolding)
    | declared declared =>
        exact .declared (signature.computation.rename rho declared)
  substitute := by
    intro n m sigma left right step
    cases step with
    | inherited inherited =>
        exact .inherited (base.computation.substitute sigma inherited)
    | delta unfolding =>
        simpa only [subst, subst_liftClosed] using
          (RootStep.delta (n := m) unfolding)
    | declared declared =>
        exact .declared (signature.computation.substitute sigma declared)

/-- Base declarations have priority.  A signature can extend a calculus but
cannot silently replace a constant already owned by its base rules. -/
def combinedType (base : Rules Head) (signature : Signature Head)
    (name : DeclName) : Option (Tm Head 0) :=
  match base.constantType name with
  | some type => some type
  | none => signature.typeOf? name

/-- Install a declaration signature in an existing presentation. -/
def extendRules (base : Rules Head) (signature : Signature Head) :
    Rules Head where
  headTyping := base.headTyping
  isUniverse := base.isUniverse
  join := base.join
  cumulative := base.cumulative
  headEq := base.headEq
  constantType := combinedType base signature
  computation := rootComputation base signature

@[simp] theorem withSignature_headTyping (base : Rules Head)
    (signature : Signature Head) :
    (extendRules base signature).headTyping = base.headTyping := rfl

@[simp] theorem withSignature_isUniverse (base : Rules Head)
    (signature : Signature Head) :
    (extendRules base signature).isUniverse = base.isUniverse := rfl

theorem combinedType_of_base (base : Rules Head) (signature : Signature Head)
    {name : DeclName} {type : Tm Head 0}
    (typing : base.constantType name = some type) :
    combinedType base signature name = some type := by
  simp [combinedType, typing]

theorem combinedType_of_signature (base : Rules Head)
    (signature : Signature Head) {name : DeclName} {type : Tm Head 0}
    (fresh : base.constantType name = none)
    (typing : signature.typeOf? name = some type) :
    combinedType base signature name = some type := by
  simp [combinedType, fresh, typing]

theorem Signature.Extends.preservesCombinedType {prior later : Signature Head}
    (extension : prior.Extends later) (base : Rules Head)
    {name : DeclName} {type : Tm Head 0}
    (typing : combinedType base prior name = some type) :
    combinedType base later name = some type := by
  cases baseType : base.constantType name with
  | none =>
      unfold Declaration.combinedType at typing ⊢
      rw [baseType] at typing ⊢
      exact extension.typeOf typing
  | some inheritedType =>
      unfold Declaration.combinedType at typing ⊢
      rw [baseType] at typing ⊢
      exact typing

/-! ## Conservativity and monotonicity -/

/-- Every base derivation remains valid after installing a signature. -/
theorem includeMorphism (base : Rules Head) (signature : Signature Head) :
    base.Morphism (extendRules base signature) (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun join => join
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type typing
    change combinedType base signature name = some (type.mapHead fun head => head)
    simpa only [Tm.mapHead_id] using combinedType_of_base base signature typing
  computation := by
    intro n left right step
    change RootStep base signature n (left.mapHead fun head => head)
      (right.mapHead fun head => head)
    simpa only [Tm.mapHead_id] using
      (RootStep.inherited (signature := signature) step)

/-- A base computation step is one of the generators of every declaration
extension. -/
theorem StepCore.includeSignature (base : Rules Head)
    (signature : Signature Head) {left right : Tm Head n}
    (step : Step base.headEq left right base.computation) :
    Step (extendRules base signature).headEq left right
      (extendRules base signature).computation := by
  change Step base.headEq left right (rootComputation base signature)
  simpa only [Tm.mapHead_id] using step.mapHead (fun head => head)
    (fun equality => equality)
    (by
      intro n sourceLeft sourceRight inherited
      change RootStep base signature n
        (sourceLeft.mapHead fun head => head)
        (sourceRight.mapHead fun head => head)
      simpa only [Tm.mapHead_id] using
        (RootStep.inherited (signature := signature) inherited))

/-- Base conversion embeds in every declaration extension. -/
theorem Conv.includeSignature (base : Rules Head)
    (signature : Signature Head) {left right : Tm Head n}
    (conversion : Conv base.headEq left right base.computation) :
    Conv (extendRules base signature).headEq left right
      (extendRules base signature).computation := by
  change Conv base.headEq left right (rootComputation base signature)
  simpa only [Tm.mapHead_id] using conversion.mapHead (fun head => head)
    (fun equality => equality)
    (by
      intro n sourceLeft sourceRight inherited
      change RootStep base signature n
        (sourceLeft.mapHead fun head => head)
        (sourceRight.mapHead fun head => head)
      simpa only [Tm.mapHead_id] using
        (RootStep.inherited (signature := signature) inherited))

/-- Typing is monotone from a base presentation into any signature extension. -/
theorem HasType.includeSignature (base : Rules Head)
    (signature : Signature Head) {context : Ctx Head n}
    {term type : Tm Head n} (typing : HasType base context term type) :
    HasType (extendRules base signature) context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    typing.mapHead (includeMorphism base signature)

/-- A signature extension induces a rule morphism on the same syntax. -/
theorem extensionMorphism (base : Rules Head) {prior later : Signature Head}
    (extension : prior.Extends later) :
    (extendRules base prior).Morphism (extendRules base later)
      (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun join => join
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type typing
    change combinedType base prior name = some type at typing
    change combinedType base later name = some (type.mapHead fun head => head)
    simpa only [Tm.mapHead_id] using
      extension.preservesCombinedType base typing
  computation := by
    intro n left right step
    change RootStep base prior n left right at step
    change RootStep base later n (left.mapHead fun head => head)
      (right.mapHead fun head => head)
    cases step with
    | inherited inherited =>
        simpa only [Tm.mapHead_id] using
          (RootStep.inherited (signature := later) inherited)
    | delta unfolding =>
        simpa only [Tm.mapHead_id] using
          (RootStep.delta (n := n) (extension.valueOf unfolding))
    | declared declared =>
        simpa only [Tm.mapHead_id] using
          (RootStep.declared (base := base) (extension.computation declared))

/-- Extending a signature preserves every existing typing derivation. -/
theorem HasType.monoSignature (base : Rules Head) {prior later : Signature Head}
    (extension : prior.Extends later) {context : Ctx Head n}
    {term type : Tm Head n}
    (typing : HasType (extendRules base prior) context term type) :
    HasType (extendRules base later) context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    typing.mapHead (extensionMorphism base extension)

/-- Removing the empty signature recovers the base rules. -/
theorem emptyMorphism (base : Rules Head) :
    (extendRules base Signature.empty).Morphism base (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun join => join
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type typing
    cases baseType : base.constantType name with
    | none =>
        simp [extendRules, combinedType, baseType, Signature.typeOf?,
          Signature.empty] at typing
    | some inheritedType =>
        simpa [extendRules, combinedType, baseType, Tm.mapHead_id] using typing
  computation := by
    intro n left right step
    change RootStep base Signature.empty n left right at step
    cases step with
    | inherited inherited => simpa only [Tm.mapHead_id] using inherited
    | delta unfolding =>
        simp [Signature.valueOf?, Signature.empty] at unfolding
    | declared declared => exact declared.elim

/-- The empty signature is exactly conservative, in both directions. -/
theorem hasType_empty_iff (base : Rules Head) {context : Ctx Head n}
    {term type : Tm Head n} :
    HasType (extendRules base Signature.empty) context term type ↔
      HasType base context term type := by
  constructor
  · intro typing
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      typing.mapHead (emptyMorphism base)
  · exact HasType.includeSignature base Signature.empty

/-! ## Proof-carrying signatures and contexts -/

/-- Context well-formedness is defined over the same `HasType` relation as
term typing.  Each telescope extension carries its formation derivation. -/
inductive ContextWellFormed (rules : Rules Head) :
    {n : Nat} → Ctx Head n → Prop where
  | nil : ContextWellFormed rules (.nil : Ctx Head 0)
  | snoc {n : Nat} {context : Ctx Head n} {type : Tm Head n} {level : Head} :
      ContextWellFormed rules context →
      HasType rules context type (.head level) →
      rules.isUniverse level →
      ContextWellFormed rules (.snoc context type)

/-- A formed signature proves freshness, type formation, value typing,
and the absence of self-delta definitions. Computational preservation is a
separate obligation; a raw `Signature` alone is syntax and computation data. -/
structure Signature.Formed (base : Rules Head)
    (signature : Signature Head) : Prop where
  fresh : ∀ {name : DeclName} {entry : Entry Head},
    signature.entries name = some entry → base.constantType name = none
  types : ∀ {name : DeclName} {type : Tm Head 0},
    signature.typeOf? name = some type →
      ∃ level : Head,
        base.isUniverse level ∧
        HasType (extendRules base signature) (.nil : Ctx Head 0)
          type (.head level)
  values : ∀ {name : DeclName} {type value : Tm Head 0},
    signature.typeOf? name = some type →
    signature.valueOf? name = some value →
      HasType (extendRules base signature) (.nil : Ctx Head 0) value type
  noSelfDelta : ∀ {name : DeclName} {value : Tm Head 0},
    signature.valueOf? name = some value → value ≠ .const name

/-- A formed dependent-function declaration has a genuinely formed domain.
Freshness and structural positivity alone cannot supply this premise. -/
theorem Signature.Formed.piDomainFormation
    {base : Rules Head} {signature : Signature Head}
    (formed : signature.Formed base)
    {name : DeclName} {domain : Tm Head 0} {codomain : Tm Head 1}
    (lookup : signature.typeOf? name = some (.pi domain codomain)) :
    ∃ level : Head, base.isUniverse level ∧
      HasType (extendRules base signature) (.nil : Ctx Head 0)
        domain (.head level) := by
  rcases formed.types lookup with ⟨_level, _universe, typing⟩
  rcases typing.piFormationGeneration with
    ⟨u, _v, _w, domainTyping, domainUniverse, _codomainTyping,
      _codomainUniverse, _join⟩
  exact ⟨u, domainUniverse, domainTyping⟩

/-- Missing field declarations prevent formation even when computation
equations make the constructor's result types convertible. -/
theorem Signature.notFormedOfMissingPiDomain
    {base : Rules Head} {signature : Signature Head}
    {name missingName : DeclName} {codomain : Tm Head 1}
    (lookup : signature.typeOf? name =
      some (.pi (.const missingName) codomain))
    (missing : (extendRules base signature).constantType missingName = none) :
    ¬ signature.Formed base := by
  intro formed
  rcases formed.piDomainFormation lookup with ⟨_level, _universe, typing⟩
  exact typing.constantImpossibleWhenMissing missing

/-- Preservation is deliberately separated from declaration formation.
This lets an intrinsic family expose fully checked types, constructors, and
eliminator schemas before a confluence or inversion theorem licenses every
raw computation instance. -/
abbrev Signature.DeclaredPreserves (base : Rules Head)
    (signature : Signature Head) : Prop :=
  ∀ {n : Nat} {context : Ctx Head n} {left right type : Tm Head n},
    signature.computation.step left right →
    HasType (extendRules base signature) context left type →
      HasType (extendRules base signature) context right type

structure Signature.WellFormed (base : Rules Head)
    (signature : Signature Head) : Prop where
  fresh : ∀ {name : DeclName} {entry : Entry Head},
    signature.entries name = some entry → base.constantType name = none
  types : ∀ {name : DeclName} {type : Tm Head 0},
    signature.typeOf? name = some type →
      ∃ level : Head,
        base.isUniverse level ∧
        HasType (extendRules base signature) (.nil : Ctx Head 0)
          type (.head level)
  values : ∀ {name : DeclName} {type value : Tm Head 0},
    signature.typeOf? name = some type →
    signature.valueOf? name = some value →
      HasType (extendRules base signature) (.nil : Ctx Head 0) value type
  noSelfDelta : ∀ {name : DeclName} {value : Tm Head 0},
    signature.valueOf? name = some value → value ≠ .const name
  declaredPreserves : ∀ {n : Nat} {context : Ctx Head n}
      {left right type : Tm Head n},
    signature.computation.step left right →
    HasType (extendRules base signature) context left type →
      HasType (extendRules base signature) context right type

/-- Forget only computation authority from a checked signature. -/
theorem Signature.WellFormed.formed
    {base : Rules Head} {signature : Signature Head}
    (wellFormed : signature.WellFormed base) : signature.Formed base where
  fresh := wellFormed.fresh
  types := wellFormed.types
  values := wellFormed.values
  noSelfDelta := wellFormed.noSelfDelta

/-- Formation plus preservation reconstructs the complete checked
signature.  Neither component can masquerade as the other. -/
theorem Signature.Formed.withPreservation
    {base : Rules Head} {signature : Signature Head}
    (formed : signature.Formed base)
    (preserves : signature.DeclaredPreserves base) :
    signature.WellFormed base where
  fresh := formed.fresh
  types := formed.types
  values := formed.values
  noSelfDelta := formed.noSelfDelta
  declaredPreserves := preserves

theorem Signature.wellFormed_iff_formed_and_preserves
    (base : Rules Head) (signature : Signature Head) :
    signature.WellFormed base ↔
      signature.Formed base ∧ signature.DeclaredPreserves base := by
  constructor
  · intro wellFormed
    exact ⟨wellFormed.formed, wellFormed.declaredPreserves⟩
  · rintro ⟨formed, preserves⟩
    exact formed.withPreservation preserves

/-- A checked signature packages declaration data with its semantic
obligations.  Consumers that exercise authority should accept this carrier,
not a raw signature. -/
structure CheckedSignature (base : Rules Head) where
  signature : Signature Head
  wellFormed : signature.WellFormed base

def CheckedSignature.rules {Head : Type} {base : Rules Head}
    (checked : CheckedSignature base) : Rules Head :=
  extendRules base checked.signature

theorem Signature.empty_wellFormed (base : Rules Head) :
    Signature.empty.WellFormed base where
  fresh := by
    intro name entry lookup
    simp [Signature.empty] at lookup
  types := by
    intro name type lookup
    simp at lookup
  values := by
    intro name type value typeLookup valueLookup
    simp at typeLookup
  noSelfDelta := by
    intro name value lookup
    simp at lookup
  declaredPreserves := by
    intro n context left right type step typing
    exact step.elim

/-- Well-formed contexts transport along any presentation morphism. -/
theorem ContextWellFormed.mapHead {source : Rules HeadOne}
    {target : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : source.Morphism target map) {context : Ctx HeadOne n}
    (wellFormed : ContextWellFormed source context) :
    ContextWellFormed target (context.mapHead map) := by
  induction wellFormed with
  | nil => exact .nil
  | snoc prior typeTyping isUniverse ih =>
      exact .snoc ih (typeTyping.mapHead morphism)
        (morphism.isUniverse isUniverse)

/-- Context formation is monotone under declaration extension. -/
theorem ContextWellFormed.monoSignature (base : Rules Head)
    {prior later : Signature Head} (extension : prior.Extends later)
    {context : Ctx Head n}
    (wellFormed : ContextWellFormed (extendRules base prior) context) :
    ContextWellFormed (extendRules base later) context := by
  simpa only [Ctx.mapHead_id] using
    wellFormed.mapHead (extensionMorphism base extension)

/-- The generic substitution development supplies the identity context
morphism for every well-formed declaration-aware context. -/
theorem ContextWellFormed.identitySubstitution {rules : Rules Head}
    {context : Ctx Head n} (_ : ContextWellFormed rules context) :
    CtxMor rules context context (ids (Head := Head)) :=
  CtxMor.identity rules context

end Declaration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
