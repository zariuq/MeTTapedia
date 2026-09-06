import Mettapedia.Languages.Megalodon.HenkinTermSubstitution
import Mettapedia.Languages.Megalodon.MathdataTypeFormation
import Mettapedia.Logic.HOL.Syntax.PartialConstSubstitution

/-!
# Checked definitions and native delta interpretation

Finite-fuel native unfolding is interpreted in the existing intrinsic HOL
syntax. A definition body is reconstructed from native inference and independent
formation checks in the final environment. This is a local condition on the
definitions with representable types; unrelated prefix-polymorphic declarations
are not excluded.

The partial interpretation follows the native fuel convention: ordinary syntax
does not consume fuel, and unfolding one named definition does. The semantic
construction does not replace the native evaluator or introduce another IR.
Definition equations in a chosen model are separate from these typing checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

universe w

variable {environment : Environment} {Γ : Ctx Base} {τ : Ty Base}

/-- Native checks on a closed definition body, in the environment in which it
will actually unfold. Earlier admission in a shadowed environment is insufficient. -/
structure DefinitionBodyChecked (environment : Environment) (declaration : TermDecl)
    (body : Tm) : Prop where
  type_formed : declaration.type.plainWellFormed 0 = true
  annotations : plainAnnotations 0 body = true
  lookups : PlainLookups environment 0 body
  inferred : inferTerm environment 0 [] body = some declaration.type

/-- Every defined constant eligible for the constructorwise HOL interpretation
has a checked closed body. This does not assert acyclicity or eventual success. -/
structure CheckedPlainDefinitions (environment : Environment) : Prop where
  body : ∀ name declaration body,
    environment.lookupTerm? name = some declaration →
    declaration.definition = some body →
    (∃ type : Ty Base, reifyType type = declaration.type) →
    DefinitionBodyChecked environment declaration body

theorem CheckedPlainDefinitions.exists_body
    (checked : CheckedPlainDefinitions environment) (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType τ) (body : Tm)
    (defined : declaration.definition = some body) :
    ∃ term : ClosedTerm (Constant environment) τ, erase term = some body := by
  have valid := checked.body name declaration body lookup defined ⟨τ, typed.symm⟩
  obtain ⟨type, term, htype, erased⟩ := interpret_of_plainLookups
    (context := []) valid.lookups (supported_of_plainAnnotations valid.annotations) valid.inferred
  have equal : type = τ := reifyType_injective (htype.trans typed)
  subst type
  exact ⟨term, erased⟩

/-- The body interpretation is obtained from the independent native checks. -/
noncomputable def CheckedPlainDefinitions.interpretBody
    (checked : CheckedPlainDefinitions environment) (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType τ) (body : Tm)
    (defined : declaration.definition = some body) : ClosedTerm (Constant environment) τ :=
  Classical.choose (checked.exists_body name declaration lookup typed body defined)

theorem CheckedPlainDefinitions.erase_interpretBody
    (checked : CheckedPlainDefinitions environment) (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType τ) (body : Tm)
    (defined : declaration.definition = some body) :
    erase (checked.interpretBody name declaration lookup typed body defined) = some body :=
  Classical.choose_spec (checked.exists_body name declaration lookup typed body defined)

/-- An erased closed term has no free native term indices to shift. -/
theorem erase_closed_shift (term : ClosedTerm (Constant environment) τ)
    (cutoff amount : Nat) :
    (erase term).map (Tm.shift cutoff amount) = erase term := by
  rw [← erase_rename_shift term (Rename.id (Base := Base) (Γ := [])) cutoff amount
    (by intro a v; nomatch v), rename_id]

/-- Weakening a closed body changes only its intrinsic context, not its native erasure. -/
theorem erase_weakenCtx (term : ClosedTerm (Constant environment) τ) (context : Ctx Base) :
    erase (weakenCtx context term) = erase term := by
  induction context with
  | nil => rfl
  | cons a context ih =>
      rw [weakenCtx_cons, erase_weaken, ih, erase_closed_shift]

/-- Already-expanded replacements at the requested definition-dependency depth. -/
noncomputable def deltaConstants (checked : CheckedPlainDefinitions environment) :
    Nat → {type : Ty Base} → Constant environment type →
      Option (ClosedTerm (Constant environment) type)
  | 0, _, .named name declaration lookup typed =>
      match declaration.definition with
      | none => some (.const (.named name declaration lookup typed))
      | some _ => none
  | fuel + 1, _, .named name declaration lookup typed =>
      match defined : declaration.definition with
      | none => some (.const (.named name declaration lookup typed))
      | some body => substConst? (deltaConstants checked fuel)
          (checked.interpretBody name declaration lookup typed body defined)
  | _, _, .primitive index lookup => some (.const (.primitive index lookup))

/-- Partial delta expansion in the existing typed syntax. The executable source
of truth remains `MathdataKernel.deltaNormalize`. -/
noncomputable def deltaInterpretation (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) (term : Term (Constant environment) Γ τ) :
    Option (Term (Constant environment) Γ τ) :=
  substConst? (deltaConstants checked fuel) term

/-- A constant-level comparison lifts through all supported native constructors.
The replacement table already contains any recursive expansion of each body. -/
theorem erase_substConst?_delta
    (replacements : ∀ {type}, Constant environment type →
      Option (ClosedTerm (Constant environment) type)) (fuel : Nat)
    (constants : ∀ {type} (constant : Constant environment type),
      (replacements constant).bind erase = deltaNormalize environment fuel constant.erase)
    (term : Term (Constant environment) Γ τ) :
    (substConst? replacements term).bind erase =
      (erase term).bind (deltaNormalize environment fuel) := by
  induction term with
  | var v => simp [substConst?, erase, deltaNormalize]
  | const constant =>
      simp only [substConst?, erase, Option.bind_some, Option.bind_map]
      simpa only [Function.comp_def, erase_weakenCtx] using constants constant
  | app f a ihf iha =>
      calc
        _ = (do return Tm.app (← (substConst? replacements f).bind erase) (← (substConst? replacements a).bind erase)) := by
          cases hf : substConst? replacements f <;> cases ha : substConst? replacements a <;>
            simp [substConst?, erase, hf, ha]
        _ = (do return Tm.app (← (erase f).bind (deltaNormalize environment fuel)) (← (erase a).bind (deltaNormalize environment fuel))) := by rw [ihf, iha]
        _ = _ := by
          cases ef : erase f <;> cases ea : erase a <;>
            simp [erase, ef, ea, deltaNormalize]
  | imp f a ihf iha =>
      calc
        _ = (do return Tm.imp (← (substConst? replacements f).bind erase) (← (substConst? replacements a).bind erase)) := by
          cases hf : substConst? replacements f <;> cases ha : substConst? replacements a <;>
            simp [substConst?, erase, hf, ha]
        _ = (do return Tm.imp (← (erase f).bind (deltaNormalize environment fuel)) (← (erase a).bind (deltaNormalize environment fuel))) := by rw [ihf, iha]
        _ = _ := by
          cases ef : erase f <;> cases ea : erase a <;>
            simp [erase, ef, ea, deltaNormalize]
  | @lam domain context codomain body ih =>
      calc
        _ = ((substConst? replacements body).bind erase).map (Tm.lam (reifyType domain)) := by
          cases hb : substConst? replacements body <;> simp [substConst?, erase, hb, Option.map_eq_bind]
        _ = ((erase body).bind (deltaNormalize environment fuel)).map (Tm.lam (reifyType domain)) :=
          congrArg (Option.map (Tm.lam (reifyType domain))) ih
        _ = _ := by cases eb : erase body <;> simp [erase, eb, deltaNormalize, Option.map_eq_bind]
  | @all domain context body ih =>
      calc
        _ = ((substConst? replacements body).bind erase).map (Tm.all (reifyType domain)) := by
          cases hb : substConst? replacements body <;> simp [substConst?, erase, hb, Option.map_eq_bind]
        _ = ((erase body).bind (deltaNormalize environment fuel)).map (Tm.all (reifyType domain)) :=
          congrArg (Option.map (Tm.all (reifyType domain))) ih
        _ = _ := by cases eb : erase body <;> simp [erase, eb, deltaNormalize, Option.map_eq_bind]
  | top | bot => rfl
  | and f a _ _ | or f a _ _ | eq f a _ _ =>
      cases hf : substConst? replacements f <;> cases ha : substConst? replacements a <;>
        simp [substConst?, erase, hf, ha]
  | not body _ | ex body _ =>
      cases hb : substConst? replacements body <;> simp [substConst?, erase, hb]

/-- Exact erasure of the fuel-indexed replacement table, including failure. -/
theorem erase_deltaConstants (checked : CheckedPlainDefinitions environment) (fuel : Nat)
    {type : Ty Base} (constant : Constant environment type) :
    (deltaConstants checked fuel constant).bind erase =
      deltaNormalize environment fuel constant.erase := by
  induction fuel generalizing type with
  | zero =>
      cases constant with
      | primitive index lookup => simp [deltaConstants, erase, Constant.erase, deltaNormalize]
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition <;>
            simp [deltaConstants, erase, Constant.erase, deltaNormalize, lookup]
  | succ fuel ih =>
      cases constant with
      | primitive index lookup => simp [deltaConstants, erase, Constant.erase, deltaNormalize]
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition with
          | none => simp [deltaConstants, Constant.erase, deltaNormalize, lookup, erase]
          | some body =>
              simp only [deltaConstants]
              rw [erase_substConst?_delta (deltaConstants checked fuel) fuel
                (fun c => ih c), checked.erase_interpretBody, Option.bind_some]
              simp [Constant.erase, deltaNormalize, lookup]

/-- Native delta evaluation and intrinsic expansion have exactly the same erased
result. Neither operation is defined by reference to the other. -/
theorem erase_deltaInterpretation (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) (term : Term (Constant environment) Γ τ) :
    (deltaInterpretation checked fuel term).bind erase =
      (erase term).bind (deltaNormalize environment fuel) :=
  erase_substConst?_delta (deltaConstants checked fuel) fuel
    (erase_deltaConstants checked fuel) term

theorem deltaNormalize_eq_some_iff (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) (term : Term (Constant environment) Γ τ) {source result : Tm}
    (erased : erase term = some source) :
    deltaNormalize environment fuel source = some result ↔
      ∃ output, deltaInterpretation checked fuel term = some output ∧ erase output = some result := by
  have comparison := erase_deltaInterpretation checked fuel term
  rw [erased, Option.bind_some] at comparison
  rw [← comparison, Option.bind_eq_some_iff]

/-- Successful substitution of representable closed bodies cannot introduce an
unsupported logical constructor into a representable source term. -/
theorem erase_substConst?_isSome
    (replacements : ∀ {type}, Constant environment type →
      Option (ClosedTerm (Constant environment) type))
    (representable : ∀ {type} (constant : Constant environment type) replacement,
      replacements constant = some replacement → (erase replacement).isSome = true)
    (term : Term (Constant environment) Γ τ) (input : (erase term).isSome = true)
    (output : Term (Constant environment) Γ τ)
    (success : substConst? replacements term = some output) :
    (erase output).isSome = true := by
  induction term with
  | var v =>
      simp only [substConst?, Option.some.injEq] at success
      rw [← success]
      rfl
  | const constant =>
      cases hc : replacements constant with
      | none => simp [substConst?, hc] at success
      | some body =>
          simp only [substConst?, hc, Option.map_some, Option.some.injEq] at success
          rw [← success, erase_weakenCtx]
          exact representable constant body hc
  | app f a ihf iha | imp f a ihf iha =>
      cases ef : erase f <;> cases ea : erase a <;>
        cases hf : substConst? replacements f <;> cases ha : substConst? replacements a <;>
        simp_all [erase, substConst?]
      all_goals
        rw [← success]
        obtain ⟨rawf, hrawf⟩ := Option.isSome_iff_exists.mp ihf
        obtain ⟨rawa, hrawa⟩ := Option.isSome_iff_exists.mp iha
        simp [erase, hrawf, hrawa]
  | lam body ih | all body ih =>
      cases eb : erase body <;> cases hb : substConst? replacements body <;>
        simp_all [erase, substConst?]
      all_goals
        rw [← success]
        obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.mp ih
        simp [erase, hraw]
  | top | bot | and | or | not | eq | ex => simp [erase] at input

theorem erase_deltaConstants_isSome (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) {type : Ty Base} (constant : Constant environment type) output
    (success : deltaConstants checked fuel constant = some output) :
    (erase output).isSome = true := by
  induction fuel generalizing type with
  | zero =>
      cases constant with
      | primitive index lookup =>
          simp only [deltaConstants, Option.some.injEq] at success
          rw [← success]
          rfl
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition <;> simp_all [deltaConstants]
          rw [← success]
          rfl
  | succ fuel ih =>
      cases constant with
      | primitive index lookup =>
          simp only [deltaConstants, Option.some.injEq] at success
          rw [← success]
          rfl
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition with
          | none =>
              simp only [deltaConstants, Option.some.injEq] at success
              rw [← success]
              rfl
          | some body =>
              simp only [deltaConstants] at success
              exact erase_substConst?_isSome (deltaConstants checked fuel)
                (fun c output h => ih c output h) _
                (by rw [checked.erase_interpretBody]; rfl) output success

theorem erase_deltaInterpretation_isSome (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) (term : Term (Constant environment) Γ τ)
    (input : (erase term).isSome = true) output
    (success : deltaInterpretation checked fuel term = some output) :
    (erase output).isSome = true :=
  erase_substConst?_isSome (deltaConstants checked fuel)
    (erase_deltaConstants_isSome checked fuel) term input output success

/-- On the supported fragment the two evaluators fail at exactly the same fuel;
failure is not confused with success followed by an unsupported erasure. -/
theorem deltaInterpretation_eq_none_iff (checked : CheckedPlainDefinitions environment)
    (fuel : Nat) (term : Term (Constant environment) Γ τ) {source : Tm}
    (erased : erase term = some source) :
    deltaInterpretation checked fuel term = none ↔
      deltaNormalize environment fuel source = none := by
  have comparison := erase_deltaInterpretation checked fuel term
  rw [erased, Option.bind_some] at comparison
  constructor
  · intro failed
    simpa only [failed, Option.bind_none] using comparison.symm
  · intro failed
    cases success : deltaInterpretation checked fuel term with
    | none => rfl
    | some output =>
        obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.mp
          (erase_deltaInterpretation_isSome checked fuel term (by simp [erased]) output success)
        rw [success, Option.bind_some, hraw, failed] at comparison
        contradiction

/-- More definition-dependency fuel preserves an already successful replacement. -/
theorem deltaConstants_succ (checked : CheckedPlainDefinitions environment) (fuel : Nat)
    {type : Ty Base} (constant : Constant environment type) output
    (success : deltaConstants checked fuel constant = some output) :
    deltaConstants checked (fuel + 1) constant = some output := by
  induction fuel generalizing type with
  | zero =>
      cases constant with
      | primitive index lookup => simpa only [deltaConstants] using success
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition <;> simp_all [deltaConstants]
  | succ fuel ih =>
      cases constant with
      | primitive index lookup => simpa only [deltaConstants] using success
      | named name declaration lookup typed =>
          rcases declaration with ⟨declName, declType, definition⟩
          cases definition with
          | none => simpa only [deltaConstants] using success
          | some body =>
              simp only [deltaConstants] at success ⊢
              exact substConst?_mono (deltaConstants checked fuel)
                (deltaConstants checked (fuel + 1)) (fun c output h => ih c output h)
                _ output success

/-- A successful typed expansion remains identical when more fuel is supplied. -/
theorem deltaInterpretation_mono (checked : CheckedPlainDefinitions environment)
    {fuel more : Nat} (bound : fuel ≤ more) (term : Term (Constant environment) Γ τ)
    output (success : deltaInterpretation checked fuel term = some output) :
    deltaInterpretation checked more term = some output := by
  induction bound with
  | refl => exact success
  | @step more bound ih =>
      exact substConst?_mono (deltaConstants checked more) (deltaConstants checked (more + 1))
        (deltaConstants_succ checked more) term output ih

#print axioms erase_deltaConstants
#print axioms erase_deltaInterpretation
#print axioms deltaNormalize_eq_some_iff
#print axioms deltaInterpretation_eq_none_iff
#print axioms deltaInterpretation_mono

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
