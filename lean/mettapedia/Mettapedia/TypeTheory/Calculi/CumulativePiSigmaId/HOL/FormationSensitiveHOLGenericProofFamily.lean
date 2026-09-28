import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation

/-!
# Proof-family extension for a declared HOL interface

A declared HOL interface can be extended with a native proof family without
rebuilding or replacing the source declaration signature.  The source rules
are the base presentation; the new signature contains only the proof constant
and the two decoding equations.  Consequently all source computation is
inherited by `Declaration.RootStep.inherited`, while proof decoding enters by
`Declaration.RootStep.declared`.

The construction is parameterized by the source base types, constants,
logical declarations, and the fresh proof-constant name.  Universal decoding
uses the source HOL type as its index, so its native domain is derived from the
same `TypeInterpretation` used by term representation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLGenericProofFamily

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def proofType (source : LogicalSignature Base Const) : Tower.Tm 0 :=
  .pi source.types.proposition (sortTm Tower.zero)

def proof (proofName : DeclName) {n : Nat} (proposition : Tower.Tm n) : Tower.Tm n :=
  .app (.const proofName) proposition

def rawImp (source : LogicalSignature Base Const) {n : Nat}
    (p q : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed source.implication) p) q

def universalProposition (source : LogicalSignature Base Const)
    (type : HOL.Ty Base) {n : Nat} (predicate : Tower.Tm n) : Tower.Tm n :=
  .app (liftClosed (source.universal type)) predicate

def implicationFamily (proofName : DeclName) {n : Nat}
    (p q : Tower.Tm n) : Tower.Tm n :=
  .pi (proof proofName p) (Presentation.rename wk (proof proofName q))

def universalFamily (source : LogicalSignature Base Const) (proofName : DeclName)
    (type : HOL.Ty Base) {n : Nat} (predicate : Tower.Tm n) : Tower.Tm n :=
  .pi (typeAt source.types n type)
    (proof proofName (.app (Presentation.rename wk predicate) (.var 0)))

/-- The source representation of implication is exactly the proposition code
used by the proof-family decoder. -/
theorem represent_imp (source : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} (left right : HOL.Formula Const gamma) :
    FormationSensitiveHOLInterface.represent source (.imp left right) = (do
      let leftCode ← FormationSensitiveHOLInterface.represent source left
      let rightCode ← FormationSensitiveHOLInterface.represent source right
      pure (rawImp source leftCode rightCode)) := by
  simpa only [rawImp] using
    FormationSensitiveHOLInterface.represent_imp source left right

/-- The source representation of universal quantification is exactly the
proposition code used by the proof-family decoder. -/
theorem represent_all (source : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (body : HOL.Formula Const (type :: gamma)) :
    FormationSensitiveHOLInterface.represent source (.all body) =
      (FormationSensitiveHOLInterface.represent source body).map
        (fun code => universalProposition source type (.lam code)) := by
  simp only [FormationSensitiveHOLInterface.represent, universalProposition]
  cases FormationSensitiveHOLInterface.represent source body <;> rfl

@[simp] theorem proof_rename (proofName : DeclName) {n m : Nat}
    (rho : Ren n m) (p : Tower.Tm n) :
    Presentation.rename rho (proof proofName p) =
      proof proofName (Presentation.rename rho p) := rfl

@[simp] theorem proof_subst (proofName : DeclName) {n m : Nat}
    (sigma : Sub Tower.Head n m) (p : Tower.Tm n) :
    Presentation.subst sigma (proof proofName p) =
      proof proofName (Presentation.subst sigma p) := rfl

@[simp] theorem rawImp_rename (source : LogicalSignature Base Const) {n m : Nat}
    (rho : Ren n m) (p q : Tower.Tm n) :
    Presentation.rename rho (rawImp source p q) =
      rawImp source (Presentation.rename rho p) (Presentation.rename rho q) := by
  simp [rawImp, Presentation.rename]

@[simp] theorem rawImp_subst (source : LogicalSignature Base Const) {n m : Nat}
    (sigma : Sub Tower.Head n m) (p q : Tower.Tm n) :
    Presentation.subst sigma (rawImp source p q) =
      rawImp source (Presentation.subst sigma p) (Presentation.subst sigma q) := by
  simp [rawImp, Presentation.subst]

@[simp] theorem universalProposition_rename
    (source : LogicalSignature Base Const) (type : HOL.Ty Base) {n m : Nat}
    (rho : Ren n m) (predicate : Tower.Tm n) :
    Presentation.rename rho (universalProposition source type predicate) =
      universalProposition source type (Presentation.rename rho predicate) := by
  simp [universalProposition, Presentation.rename]

@[simp] theorem universalProposition_subst
    (source : LogicalSignature Base Const) (type : HOL.Ty Base) {n m : Nat}
    (sigma : Sub Tower.Head n m) (predicate : Tower.Tm n) :
    Presentation.subst sigma (universalProposition source type predicate) =
      universalProposition source type (Presentation.subst sigma predicate) := by
  simp [universalProposition, Presentation.subst]

@[simp] theorem implicationFamily_rename (proofName : DeclName) {n m : Nat}
    (rho : Ren n m) (p q : Tower.Tm n) :
    Presentation.rename rho (implicationFamily proofName p q) =
      implicationFamily proofName (Presentation.rename rho p)
        (Presentation.rename rho q) := by
  simp [implicationFamily, Presentation.rename, rename_comp, liftRen, wk]

@[simp] theorem implicationFamily_subst (proofName : DeclName) {n m : Nat}
    (sigma : Sub Tower.Head n m) (p q : Tower.Tm n) :
    Presentation.subst sigma (implicationFamily proofName p q) =
      implicationFamily proofName (Presentation.subst sigma p)
        (Presentation.subst sigma q) := by
  simp [implicationFamily, Presentation.subst,
    subst_rename, rename_subst, liftSub, wk]

@[simp] theorem universalFamily_rename (source : LogicalSignature Base Const)
    (proofName : DeclName) (type : HOL.Ty Base) {n m : Nat}
    (rho : Ren n m) (predicate : Tower.Tm n) :
    Presentation.rename rho (universalFamily source proofName type predicate) =
      universalFamily source proofName type (Presentation.rename rho predicate) := by
  simp [universalFamily, Presentation.rename, rename_comp, liftRen, wk]

@[simp] theorem universalFamily_subst (source : LogicalSignature Base Const)
    (proofName : DeclName) (type : HOL.Ty Base) {n m : Nat}
    (sigma : Sub Tower.Head n m) (predicate : Tower.Tm n) :
    Presentation.subst sigma (universalFamily source proofName type predicate) =
      universalFamily source proofName type (Presentation.subst sigma predicate) := by
  simp [universalFamily, Presentation.subst,
    subst_rename, rename_subst, liftSub, wk]

/-- The proof decoder adds exactly implication and type-indexed universal
decoding.  It does not absorb the source signature's own computation. -/
inductive DecoderStep (source : LogicalSignature Base Const) (proofName : DeclName) :
    {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | implication {n : Nat} (p q : Tower.Tm n) :
      DecoderStep source proofName (proof proofName (rawImp source p q))
        (implicationFamily proofName p q)
  | universal {n : Nat} (type : HOL.Ty Base) (predicate : Tower.Tm n) :
      DecoderStep source proofName
        (proof proofName (universalProposition source type predicate))
        (universalFamily source proofName type predicate)

def computation (source : LogicalSignature Base Const) (proofName : DeclName) :
    RootComputation Tower.Head where
  step := DecoderStep source proofName
  rename := by
    intro n m rho left right step
    cases step with
    | implication p q =>
        simpa only [proof_rename, rawImp_rename, implicationFamily_rename] using
          DecoderStep.implication
            (Presentation.rename rho p) (Presentation.rename rho q)
    | universal type predicate =>
        simpa only [proof_rename, universalProposition_rename,
          universalFamily_rename] using
          DecoderStep.universal type
            (Presentation.rename rho predicate)
  substitute := by
    intro n m sigma left right step
    cases step with
    | implication p q =>
        simpa only [proof_subst, rawImp_subst, implicationFamily_subst] using
          DecoderStep.implication
            (Presentation.subst sigma p) (Presentation.subst sigma q)
    | universal type predicate =>
        simpa only [proof_subst, universalProposition_subst,
          universalFamily_subst] using
          DecoderStep.universal type
            (Presentation.subst sigma predicate)

/-- Only the proof-family declaration and decoder equations are new. -/
def declarations (source : LogicalSignature Base Const) (proofName : DeclName) :
    Signature Tower.Head where
  entries := (Signature.empty.insert proofName ⟨proofType source, none⟩).entries
  computation := computation source proofName

/-- Layer the proof family over the already declared HOL interface. -/
def rules (source : LogicalSignature Base Const) (proofName : DeclName) : Rules Tower.Head :=
  extendRules source.rules (declarations source proofName)

theorem sourceMorphism (source : LogicalSignature Base Const) (proofName : DeclName) :
    source.rules.Morphism (rules source proofName) (fun head => head) :=
  includeMorphism source.rules (declarations source proofName)

/-- A target presentation implements the layered proof family precisely when
it already receives the source declarations, declares the same proof-family
constant, and realizes both decoder steps.  The resulting morphism transports
all formation, typing, and conversion judgments; clients do not need a second
copy of the logical proof rules for each richer host presentation. -/
theorem morphismTo (source : LogicalSignature Base Const) (proofName : DeclName)
    (target : Rules Tower.Head)
    (sourceMap : source.rules.Morphism target (fun head => head))
    (proofKnown : target.constantType proofName = some (proofType source))
    (decoder : ∀ {n : Nat} {left right : Tower.Tm n},
      DecoderStep source proofName left right → target.computation.step left right) :
    (rules source proofName).Morphism target (fun head => head) where
  headTyping := sourceMap.headTyping
  isUniverse := sourceMap.isUniverse
  join := sourceMap.join
  cumulative := sourceMap.cumulative
  headEq := sourceMap.headEq
  constantType := by
    intro name type known
    change combinedType source.rules (declarations source proofName) name = some type at known
    cases inherited : source.rules.constantType name with
    | some inheritedType =>
        have shape : inheritedType = type := by
          simpa [combinedType, inherited] using known
        subst type
        simpa only [Tm.mapHead_id] using sourceMap.constantType inherited
    | none =>
        have declared : (declarations source proofName).typeOf? name = some type := by
          simpa [combinedType, inherited] using known
        have named : name = proofName ∧ proofType source = type := by
          simpa [declarations, Signature.typeOf?, Signature.empty,
            Signature.insert] using declared
        rcases named with ⟨rfl, rfl⟩
        simpa only [Tm.mapHead_id] using proofKnown
  computation := by
    intro n left right step
    change RootStep source.rules (declarations source proofName) n left right at step
    cases step with
    | inherited prior =>
        simpa only [Tm.mapHead_id] using sourceMap.computation prior
    | @delta name value known =>
        by_cases named : name = proofName
        · subst name
          simp [declarations, Signature.valueOf?, Signature.empty,
            Signature.insert] at known
        · simp [declarations, Signature.valueOf?, Signature.empty,
            Signature.insert, named] at known
    | declared added =>
        simpa only [Tm.mapHead_id] using decoder added

theorem include_typed (source : LogicalSignature Base Const) (proofName : DeclName)
    {n : Nat} {gamma : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing source.rules gamma term type) :
    Typing (rules source proofName) gamma term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    typed.mapHead (sourceMorphism source proofName)

theorem include_context (source : LogicalSignature Base Const) (proofName : DeclName)
    {n : Nat} {gamma : Tower.Ctx n}
    (formed : ContextFormation source.rules gamma) :
    ContextFormation (rules source proofName) gamma := by
  simpa only [Ctx.mapHead_id] using
    formed.mapHead (sourceMorphism source proofName)

/-- Source computation is retained as an inherited root step.  No emptiness
assumption on the source computation is used. -/
theorem source_computation_step (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {left right : Tower.Tm n}
    (step : source.rules.computation.step left right) :
    (rules source proofName).computation.step left right :=
  RootStep.inherited step

/-- Decoder computation enters through the new declaration layer. -/
theorem decoder_computation_step (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {left right : Tower.Tm n}
    (step : DecoderStep source proofName left right) :
    (rules source proofName).computation.step left right :=
  RootStep.declared step

theorem proofType_formed (source : LogicalSignature Base Const) (proofName : DeclName) :
    Typing (rules source proofName) .nil (proofType source)
      (sortTm (.max Tower.zero (.succ Tower.zero))) :=
  .piForm (include_typed source proofName source.proposition_formed)
    (.sort Tower.zero) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    (.sorts Tower.zero (.succ Tower.zero))

theorem proofConstant_typed (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} (gamma : Tower.Ctx n) :
    Typing (rules source proofName) gamma (.const proofName)
      (liftClosed (proofType source)) := by
  apply Typing.const
  · apply combinedType_of_signature source.rules (declarations source proofName) fresh
    exact Signature.typeOf_insert_eq _ _ _
  · exact proofType_formed source proofName
  · exact .sort (.max Tower.zero (.succ Tower.zero))

theorem proof_formed (source : LogicalSignature Base Const) (proofName : DeclName)
    (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {p : Tower.Tm n}
    (typed : Typing (rules source proofName) gamma p
      (typeAt source.types n .prop)) :
    Typing (rules source proofName) gamma (proof proofName p) (sortTm Tower.zero) := by
  have applied := Typing.appElim (proofConstant_typed source proofName fresh gamma) typed
  simpa only [proofType, proof, sortTm, liftClosed, Presentation.rename, inst0,
    Presentation.subst] using applied

theorem pi_zero (source : LogicalSignature Base Const) (proofName : DeclName)
    {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing (rules source proofName) gamma a (sortTm Tower.zero))
    (codomain : Typing (rules source proofName) (.snoc gamma a) b (sortTm Tower.zero)) :
    Typing (rules source proofName) gamma (.pi a b) (sortTm Tower.zero) := by
  apply Typing.cumul (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

theorem implication_proposition (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing (rules source proofName) gamma p (typeAt source.types n .prop))
    (hq : Typing (rules source proofName) gamma q (typeAt source.types n .prop)) :
    Typing (rules source proofName) gamma (rawImp source p q)
      (typeAt source.types n .prop) := by
  have symbol := include_typed source proofName
    (closed_typed source.implication_typed gamma)
  simp only [liftClosed, typeAt_rename] at symbol
  have first := Typing.appElim symbol hp
  simp only [inst0, typeAt_subst] at first
  have second := Typing.appElim first hq
  simpa only [rawImp, liftClosed, typeAt_rename, inst0, typeAt_subst] using second

theorem implication_formed (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typing (rules source proofName) gamma p (typeAt source.types n .prop))
    (hq : Typing (rules source proofName) gamma q (typeAt source.types n .prop)) :
    Typing (rules source proofName) gamma (implicationFamily proofName p q)
      (sortTm Tower.zero) :=
  pi_zero (source := source) (proofName := proofName)
    (proof_formed source proofName fresh hp)
    ((proof_formed source proofName fresh hq).weaken)

theorem implication_conversion (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} (p q : Tower.Tm n) :
    Conv (rules source proofName).headEq (proof proofName (rawImp source p q))
      (implicationFamily proofName p q) (rules source proofName).computation :=
  .rel _ _ (.root (.declared (.implication p q)))

theorem predicate_at_variable (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {gamma : Tower.Ctx n}
    {type : HOL.Ty Base} {predicate : Tower.Tm n}
    (typed : Typing (rules source proofName) gamma predicate
      (.pi (typeAt source.types n type) (typeAt source.types (n + 1) .prop))) :
    Typing (rules source proofName)
      (.snoc gamma (typeAt source.types n type))
      (.app (Presentation.rename wk predicate) (.var 0))
      (typeAt source.types (n + 1) .prop) := by
  have applied := Typing.appElim
    (typed.weaken (extension := typeAt source.types n type)) (Typing.var 0)
  simpa only [Presentation.rename, inst0, Presentation.subst, typeAt_rename,
    typeAt_subst] using applied

theorem universal_proposition_formed (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {gamma : Tower.Ctx n}
    {type : HOL.Ty Base} {predicate : Tower.Tm n}
    (typed : Typing (rules source proofName) gamma predicate
      (.pi (typeAt source.types n type) (typeAt source.types (n + 1) .prop))) :
    Typing (rules source proofName) gamma
      (universalProposition source type predicate)
      (typeAt source.types n .prop) := by
  have symbol := include_typed source proofName
    (closed_typed (source.universal_typed type) gamma)
  simp only [liftClosed, typeAt_rename] at symbol
  have applied := Typing.appElim symbol typed
  simpa only [universalProposition, liftClosed, typeAt_rename, inst0, typeAt_subst]
    using applied

theorem universal_formed (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {type : HOL.Ty Base}
    {predicate : Tower.Tm n}
    (typed : Typing (rules source proofName) gamma predicate
      (.pi (typeAt source.types n type) (typeAt source.types (n + 1) .prop))) :
    Typing (rules source proofName) gamma
      (universalFamily source proofName type predicate) (sortTm Tower.zero) := by
  apply pi_zero (source := source) (proofName := proofName)
  · exact include_typed source proofName (typeAt_formed source type gamma)
  · exact proof_formed source proofName fresh
      (predicate_at_variable source proofName typed)

theorem universal_conversion (source : LogicalSignature Base Const)
    (proofName : DeclName) (type : HOL.Ty Base) {n : Nat}
    (predicate : Tower.Tm n) :
    Conv (rules source proofName).headEq
      (proof proofName (universalProposition source type predicate))
      (universalFamily source proofName type predicate)
      (rules source proofName).computation :=
  .rel _ _ (.root (.declared (.universal type predicate)))

/-! ## Proof construction through the generic decoder -/

/-- Implication introduction is native lambda formation followed by the
generic decoder conversion. -/
theorem implication_intro (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (hp : Typing (rules source proofName) gamma p
      (typeAt source.types n .prop))
    (hq : Typing (rules source proofName) gamma q
      (typeAt source.types n .prop))
    (hb : Typing (rules source proofName)
      (.snoc gamma (proof proofName p)) body
      (Presentation.rename wk (proof proofName q))) :
    Typing (rules source proofName) gamma (.lam body)
      (proof proofName (rawImp source p q)) :=
  .conv (.lamIntro (implication_formed source proofName fresh hp hq)
      (.sort Tower.zero) hb)
    (proof_formed source proofName fresh (implication_proposition source proofName hp hq))
    (.sort Tower.zero) (.symm _ _ (implication_conversion source proofName p q))

/-- Implication elimination is native application after exposing the decoded
dependent function type. -/
theorem implication_elim (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {p q major minor : Tower.Tm n}
    (hp : Typing (rules source proofName) gamma p
      (typeAt source.types n .prop))
    (hq : Typing (rules source proofName) gamma q
      (typeAt source.types n .prop))
    (hm : Typing (rules source proofName) gamma major
      (proof proofName (rawImp source p q)))
    (ha : Typing (rules source proofName) gamma minor (proof proofName p)) :
    Typing (rules source proofName) gamma (.app major minor) (proof proofName q) := by
  have converted := Typing.conv hm
    (implication_formed source proofName fresh hp hq) (.sort Tower.zero)
    (implication_conversion source proofName p q)
  simpa only [implicationFamily, inst0_rename_wk] using Typing.appElim converted ha

/-- Instantiating a weakened binder body at the newest variable restores it. -/
theorem instantiate_shifted_body {n : Nat} (body : Tower.Tm (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) body) = body := by
  unfold inst0
  rw [subst_rename]
  calc
    Presentation.subst (fun index => subst0 (.var 0) (liftRen wk index)) body =
        Presentation.subst ids body := by
      apply subst_ext
      intro index
      refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
    _ = body := subst_ids body

/-- Universal decoding followed by native beta exposes the dependent proof
family of the represented predicate body. -/
theorem universal_lambda_conversion (source : LogicalSignature Base Const)
    (proofName : DeclName) (type : HOL.Ty Base) {n : Nat}
    (body : Tower.Tm (n + 1)) :
    Conv (rules source proofName).headEq
      (proof proofName (universalProposition source type (.lam body)))
      (.pi (typeAt source.types n type) (proof proofName body))
      (rules source proofName).computation := by
  refine .trans _ _ _ (universal_conversion source proofName type (.lam body)) ?_
  apply Conv.congPi (.refl _)
  apply Conv.congApp (.refl _)
  change Conv (rules source proofName).headEq
    (.app (.lam (Presentation.rename (liftRen wk) body)) (.var 0)) body
    (rules source proofName).computation
  simpa only [instantiate_shifted_body] using
    (Relation.EqvGen.rel _ _ (Step.betaPi
      (root := (rules source proofName).computation)
      (headEq := (rules source proofName).headEq)
      (Presentation.rename (liftRen wk) body) (.var 0)))

theorem universal_lambda_proposition (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {gamma : Tower.Ctx n}
    {type : HOL.Ty Base} {body : Tower.Tm (n + 1)}
    (domainTyped : Typing (rules source proofName) gamma
      (typeAt source.types n type) (sortTm Tower.zero))
    (bodyTyped : Typing (rules source proofName)
      (.snoc gamma (typeAt source.types n type)) body
      (typeAt source.types (n + 1) .prop)) :
    Typing (rules source proofName) gamma
      (universalProposition source type (.lam body))
      (typeAt source.types n .prop) := by
  apply universal_proposition_formed source proofName
  exact .lamIntro
    (pi_zero source proofName domainTyped
      (include_typed source proofName (typeAt_formed source .prop _)))
    (.sort Tower.zero) bodyTyped

/-- Universal introduction is native lambda formation followed by the
generic universal decoder conversion. -/
theorem universal_intro (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {type : HOL.Ty Base}
    {proposition body : Tower.Tm (n + 1)}
    (domainTyped : Typing (rules source proofName) gamma
      (typeAt source.types n type) (sortTm Tower.zero))
    (propositionTyped : Typing (rules source proofName)
      (.snoc gamma (typeAt source.types n type)) proposition
      (typeAt source.types (n + 1) .prop))
    (bodyTyped : Typing (rules source proofName)
      (.snoc gamma (typeAt source.types n type)) body
      (proof proofName proposition)) :
    Typing (rules source proofName) gamma (.lam body)
      (proof proofName
        (universalProposition source type (.lam proposition))) :=
  .conv
    (.lamIntro
      (pi_zero source proofName domainTyped
        (proof_formed source proofName fresh propositionTyped))
      (.sort Tower.zero) bodyTyped)
    (proof_formed source proofName fresh
      (universal_lambda_proposition source proofName domainTyped propositionTyped))
    (.sort Tower.zero)
    (.symm _ _ (universal_lambda_conversion source proofName type proposition))

/-- Universal elimination is native application after exposing the decoded
dependent proof family. -/
theorem universal_elim (source : LogicalSignature Base Const)
    (proofName : DeclName) (fresh : source.rules.constantType proofName = none)
    {n : Nat} {gamma : Tower.Ctx n} {type : HOL.Ty Base}
    {proposition : Tower.Tm (n + 1)} {major argument : Tower.Tm n}
    (domainTyped : Typing (rules source proofName) gamma
      (typeAt source.types n type) (sortTm Tower.zero))
    (propositionTyped : Typing (rules source proofName)
      (.snoc gamma (typeAt source.types n type)) proposition
      (typeAt source.types (n + 1) .prop))
    (majorTyped : Typing (rules source proofName) gamma major
      (proof proofName
        (universalProposition source type (.lam proposition))))
    (argumentTyped : Typing (rules source proofName) gamma argument
      (typeAt source.types n type)) :
    Typing (rules source proofName) gamma (.app major argument)
      (proof proofName (inst0 argument proposition)) := by
  have converted := Typing.conv majorTyped
    (pi_zero source proofName domainTyped
      (proof_formed source proofName fresh propositionTyped))
    (.sort Tower.zero)
    (universal_lambda_conversion source proofName type proposition)
  simpa only [inst0, proof_subst] using Typing.appElim converted argumentTyped

/-! The construction itself is free of additional axioms. -/

#print axioms sourceMorphism
#print axioms morphismTo
#print axioms source_computation_step
#print axioms decoder_computation_step
#print axioms proofType_formed
#print axioms implication_conversion
#print axioms universal_conversion
#print axioms implication_intro
#print axioms implication_elim
#print axioms universal_intro
#print axioms universal_elim

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLGenericProofFamily
