import Mettapedia.Languages.Megalodon.HenkinTypeFragment

/-!
# Intrinsic HOL interpretation of native Megalodon terms

The monomorphic term constructors are interpreted in the existing intrinsic HOL
syntax. Free type variables and declared base names remain distinct schematic
base symbols. Constants retain their native name or primitive index and the
actual environment lookup that establishes their type. Prefix polymorphism is
outside this constructorwise interpretation; specializing a schematic type is
a separate operation.

Raw type inference trusts its context and environment lookups. The interpretation
therefore requires plain types for the symbols actually used, and reconstructs
an intrinsic context from a plain native context. Unrelated polymorphic symbols
are allowed. Exact partial erasure records the native syntax and binder types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

abbrev Base := Nat ⊕ Nat

/-- Reify a schematic HOL type without identifying type variables with base names. -/
def reifyType : Ty Base → Tp
  | .prop => .prop
  | .base (.inl index) => .var index
  | .base (.inr index) => .base index
  | .arr domain codomain => .arr (reifyType domain) (reifyType codomain)

@[simp] theorem schematicType_reifyType (type : Ty Base) :
    HenkinTypeFragment.schematicType (reifyType type) = some type := by
  induction type with
  | prop => rfl
  | base index => cases index <;> rfl
  | arr domain codomain ihd ihc =>
      change (do
        let d ← HenkinTypeFragment.schematicType (reifyType domain)
        let c ← HenkinTypeFragment.schematicType (reifyType codomain)
        pure (Ty.arr d c)) = _
      simp [ihd, ihc]

theorem reifyType_injective : Function.Injective reifyType := by
  intro first second equal
  have := congrArg HenkinTypeFragment.schematicType equal
  simpa using this

theorem reifyType_of_schematicType {type : Tp} {value : Ty Base}
    (interpreted : HenkinTypeFragment.schematicType type = some value) :
    reifyType value = type := by
  induction type generalizing value with
  | var index =>
      simp only [HenkinTypeFragment.schematicType,
        HenkinTypeFragment.instantiate, Option.some.injEq] at interpreted
      subst value; rfl
  | prop =>
      simp only [HenkinTypeFragment.schematicType,
        HenkinTypeFragment.instantiate, Option.some.injEq] at interpreted
      subst value; rfl
  | base index =>
      simp only [HenkinTypeFragment.schematicType,
        HenkinTypeFragment.instantiate, Option.some.injEq] at interpreted
      subst value; rfl
  | all body ih => simp [HenkinTypeFragment.schematicType,
      HenkinTypeFragment.instantiate] at interpreted
  | arr domain codomain ihd ihc =>
      change (do
        let d ← HenkinTypeFragment.schematicType domain
        let c ← HenkinTypeFragment.schematicType codomain
        pure (Ty.arr d c)) = some value at interpreted
      cases hd : HenkinTypeFragment.schematicType domain with
      | none => simp [hd] at interpreted
      | some d =>
        cases hc : HenkinTypeFragment.schematicType codomain with
        | none => simp [hd, hc] at interpreted
        | some c =>
          simp [hd, hc] at interpreted
          subst value
          simp [reifyType, ihd hd, ihc hc]

theorem exists_reifyType_of_plain {depth : Nat} {type : Tp}
    (plain : type.plainWellFormed depth = true) :
    ∃ value : Ty Base, reifyType value = type := by
  obtain ⟨value, interpreted⟩ := Option.isSome_iff_exists.1
    (HenkinTypeFragment.instantiate_isSome_of_plain
      (fun index => .base (.inl index)) Sum.inr type plain)
  exact ⟨value, reifyType_of_schematicType interpreted⟩

/-- Each symbol keeps its source lookup, even if later type instantiation
identifies the interpreted types of two different symbols. -/
inductive Constant (environment : Environment) : Ty Base → Type where
  | named {type : Ty Base} (name : Name) (declaration : TermDecl)
      (lookup : environment.lookupTerm? name = some declaration)
      (typed : declaration.type = reifyType type) : Constant environment type
  | primitive {type : Ty Base} (index : Nat)
      (lookup : environment.primitives[index]? = some (reifyType type)) :
      Constant environment type

def Constant.erase {environment : Environment} {type : Ty Base} :
    Constant environment type → Tm
  | .named name _ _ _ => .named name
  | .primitive index _ => .prim index

def variableIndex {context : Ctx Base} {type : Ty Base} : Var context type → Nat
  | .vz => 0
  | .vs v => variableIndex v + 1

/-- Partial erasure does not assign invented native constructors to the
additional logical constructors of HOL. -/
def erase {environment : Environment} {context : Ctx Base} {type : Ty Base} :
    Term (Constant environment) context type → Option Tm
  | .var v => some (.db (variableIndex v))
  | .const constant => some constant.erase
  | .app function argument => do return .app (← erase function) (← erase argument)
  | .lam (σ := domain) body => do return .lam (reifyType domain) (← erase body)
  | .imp antecedent consequent => do return .imp (← erase antecedent) (← erase consequent)
  | .all (σ := domain) body => do return .all (reifyType domain) (← erase body)
  | .top | .bot | .and _ _ | .or _ _ | .not _ | .eq _ _ | .ex _ => none

/-- Supported constructors are a syntactic condition independent of inference. -/
def supported : Tm → Bool
  | .db _ | .named _ | .prim _ => true
  | .app function argument | .imp function argument => supported function && supported argument
  | .lam _ body | .all _ body => supported body
  | .typeApp _ _ | .typeLam _ | .typeAll _ => false

/-- Formation of the lookup types that raw inference trusts. -/
structure PlainEnvironment (environment : Environment) (depth : Nat) : Prop where
  named : ∀ name declaration, environment.lookupTerm? name = some declaration →
    declaration.type.plainWellFormed depth = true
  primitive : ∀ (index : Nat) (type : Tp), environment.primitives[index]? = some type →
    type.plainWellFormed depth = true

/-- Only the symbols occurring in this native term must have plain lookup
types. Unrelated polymorphic declarations in the environment remain allowed. -/
def PlainLookups (environment : Environment) (depth : Nat) : Tm → Prop
  | .db _ => True
  | .named name => ∀ declaration, environment.lookupTerm? name = some declaration →
      declaration.type.plainWellFormed depth = true
  | .prim index => ∀ type : Tp, environment.primitives[index]? = some type →
      type.plainWellFormed depth = true
  | .app function argument | .imp function argument =>
      PlainLookups environment depth function ∧ PlainLookups environment depth argument
  | .lam _ body | .all _ body => PlainLookups environment depth body
  | .typeApp _ _ | .typeLam _ | .typeAll _ => False

theorem PlainEnvironment.plainLookups {environment : Environment} {depth : Nat}
    (plainEnvironment : PlainEnvironment environment depth) {term : Tm}
    (fragment : supported term = true) : PlainLookups environment depth term := by
  induction term with
  | db _ => trivial
  | named name => exact plainEnvironment.named name
  | prim index => exact plainEnvironment.primitive index
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp only [supported, Bool.and_eq_true] at fragment
      exact ⟨ihf fragment.1, iha fragment.2⟩
  | lam _ _ ih | all _ _ ih => exact ih fragment
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ => simp [supported] at fragment

theorem exists_variable {context : Ctx Base} {index : Nat} {type : Tp}
    (lookup : (context.map reifyType)[index]? = some type) :
    ∃ value : Ty Base, ∃ v : Var context value,
      reifyType value = type ∧ variableIndex v = index := by
  induction context generalizing index with
  | nil => simp at lookup
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at lookup
          exact ⟨head, .vz, lookup, rfl⟩
      | succ index =>
          simp only [List.map_cons, List.getElem?_cons_succ] at lookup
          obtain ⟨value, v, typed, indexed⟩ := ih lookup
          exact ⟨value, .vs v, typed, congrArg Nat.succ indexed⟩

/-- Accepted supported native terms have an intrinsic HOL interpretation whose
erasure is exactly the original term, not just an observationally equal term. -/
theorem interpret_of_plainLookups {environment : Environment} {depth : Nat}
    {context : Ctx Base} {term : Tm} {type : Tp}
    (plainLookups : PlainLookups environment depth term)
    (fragment : supported term = true)
    (accepted : inferTerm environment depth (context.map reifyType) term = some type) :
    ∃ value : Ty Base, ∃ interpreted : Term (Constant environment) context value,
      reifyType value = type ∧ erase interpreted = some term := by
  induction term generalizing context type with
  | db index =>
      obtain ⟨value, v, typed, indexed⟩ := exists_variable accepted
      exact ⟨value, .var v, typed, by simp [erase, indexed]⟩
  | prim index =>
      obtain ⟨value, typed⟩ := exists_reifyType_of_plain
        (plainLookups type accepted)
      exact ⟨value, .const (.primitive index (typed ▸ accepted)), typed, rfl⟩
  | named name =>
      cases lookup : environment.lookupTerm? name with
      | none => simp [inferTerm, lookup] at accepted
      | some declaration =>
          simp only [inferTerm, lookup, Option.map_some, Option.some.injEq] at accepted
          obtain ⟨value, typed⟩ := exists_reifyType_of_plain
            (plainLookups declaration lookup)
          exact ⟨value, .const (.named name declaration lookup typed.symm),
            typed.trans accepted, rfl⟩
  | app function argument ihf iha =>
      simp only [supported, Bool.and_eq_true] at fragment
      cases hf : inferTerm environment depth (context.map reifyType) function with
      | none => simp [inferTerm, hf] at accepted
      | some functionType =>
        cases functionType <;> try simp [inferTerm, hf] at accepted
        case arr domain codomain =>
          cases ha : inferTerm environment depth (context.map reifyType) argument with
          | none => simp [ha] at accepted
          | some argumentType =>
              by_cases same : argumentType = domain
              · subst argumentType
                simp only [ha, Option.bind_some, ite_true,
                  Option.some.injEq] at accepted
                obtain ⟨functionValue, f, ftyped, ferased⟩ := ihf plainLookups.1 fragment.1 hf
                obtain ⟨argumentValue, a, atyped, aerased⟩ := iha plainLookups.2 fragment.2 ha
                cases functionValue with
                | prop => cases ftyped
                | base index => cases index <;> cases ftyped
                | arr d c =>
                    simp only [reifyType, Tp.arr.injEq] at ftyped
                    have equal : argumentValue = d := reifyType_injective
                      (atyped.trans ftyped.1.symm)
                    subst argumentValue
                    exact ⟨c, .app f a, ftyped.2.trans accepted,
                      by simp [erase, ferased, aerased]⟩
              · simp [ha, same] at accepted
  | lam domain body ih =>
      by_cases plain : domain.plainWellFormed depth = true
      · obtain ⟨d, hd⟩ := exists_reifyType_of_plain plain
        cases hb : inferTerm environment depth (domain :: context.map reifyType) body with
        | none => simp [inferTerm, plain, hb] at accepted
        | some codomain =>
            simp [inferTerm, plain, hb] at accepted
            obtain ⟨c, b, hc, eb⟩ := ih plainLookups fragment
              (context := d :: context) (by simpa [hd] using hb)
            exact ⟨.arr d c, .lam b, by simp [reifyType, hd, hc, accepted],
              by simp [erase, hd, eb]⟩
      · simp [inferTerm, plain] at accepted
  | imp antecedent consequent iha ihc =>
      simp only [supported, Bool.and_eq_true] at fragment
      cases ha : inferTerm environment depth (context.map reifyType) antecedent with
      | none => simp [inferTerm, ha] at accepted
      | some a =>
        cases a <;> try simp [inferTerm, ha] at accepted
        case prop =>
          cases hc : inferTerm environment depth (context.map reifyType) consequent with
          | none => simp [hc] at accepted
          | some c =>
            cases c <;> try simp [hc] at accepted
            case prop =>
              obtain ⟨av, antecedentTerm, hat, eat⟩ := iha plainLookups.1 fragment.1 ha
              obtain ⟨cv, ct, hct, ect⟩ := ihc plainLookups.2 fragment.2 hc
              have avp : av = .prop := reifyType_injective hat
              have cvp : cv = .prop := reifyType_injective hct
              subst av; subst cv
              exact ⟨.prop, .imp antecedentTerm ct, accepted, by simp [erase, eat, ect]⟩
  | all domain body ih =>
      by_cases plain : domain.plainWellFormed depth = true
      · obtain ⟨d, hd⟩ := exists_reifyType_of_plain plain
        cases hb : inferTerm environment depth (domain :: context.map reifyType) body with
        | none => simp [inferTerm, plain, hb] at accepted
        | some b =>
          cases b <;> try simp [inferTerm, plain, hb] at accepted
          case prop =>
            obtain ⟨bv, bt, hbt, ebt⟩ := ih plainLookups fragment
              (context := d :: context) (by simpa [hd] using hb)
            have bvp : bv = .prop := reifyType_injective hbt
            subst bv
            exact ⟨.prop, .all bt, accepted, by simp [erase, hd, ebt]⟩
      · simp [inferTerm, plain] at accepted
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ => simp [supported] at fragment

/-- A globally plain environment is a sufficient special case of the local
lookup condition. -/
theorem interpret {environment : Environment} {depth : Nat}
    (plainEnvironment : PlainEnvironment environment depth)
    {context : Ctx Base} {term : Tm} {type : Tp}
    (fragment : supported term = true)
    (accepted : inferTerm environment depth (context.map reifyType) term = some type) :
    ∃ value : Ty Base, ∃ interpreted : Term (Constant environment) context value,
      reifyType value = type ∧ erase interpreted = some term :=
  interpret_of_plainLookups (plainEnvironment.plainLookups fragment) fragment accepted

/-- A native context containing only plain types is exactly representable as
an intrinsic HOL context. -/
theorem exists_reified_context {depth : Nat} (context : List Tp)
    (plain : ∀ type ∈ context, type.plainWellFormed depth = true) :
    ∃ interpreted : Ctx Base, interpreted.map reifyType = context := by
  induction context with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨headType, typed⟩ := exists_reifyType_of_plain (plain head (by simp))
      obtain ⟨context, reified⟩ := ih (by intro type member; exact plain type (by simp [member]))
      exact ⟨headType :: context, by simp [typed, reified]⟩

/-- Interpretation starts from the native context and inference judgment;
the intrinsic context is reconstructed, not supplied as a separate semantic
assumption. -/
theorem interpret_native {environment : Environment} {depth : Nat}
    {context : List Tp} {term : Tm} {type : Tp}
    (plainContext : ∀ type ∈ context, type.plainWellFormed depth = true)
    (plainLookups : PlainLookups environment depth term)
    (fragment : supported term = true)
    (accepted : inferTerm environment depth context term = some type) :
    ∃ interpretedContext : Ctx Base, ∃ value : Ty Base,
      ∃ interpreted : Term (Constant environment) interpretedContext value,
        interpretedContext.map reifyType = context ∧
          reifyType value = type ∧ erase interpreted = some term := by
  obtain ⟨interpretedContext, reified⟩ := exists_reified_context context plainContext
  obtain ⟨value, interpreted, typed, erased⟩ :=
    interpret_of_plainLookups plainLookups fragment (reified ▸ accepted)
  exact ⟨interpretedContext, value, interpreted, reified, typed, erased⟩

/-- Formation of annotations, separate from the inferred type and from lookup
formation. This checks precisely the binder annotations of the supported syntax. -/
def plainAnnotations (depth : Nat) : Tm → Bool
  | .db _ | .named _ | .prim _ => true
  | .app function argument | .imp function argument =>
      plainAnnotations depth function && plainAnnotations depth argument
  | .lam type body | .all type body =>
      type.plainWellFormed depth && plainAnnotations depth body
  | .typeApp _ _ | .typeLam _ | .typeAll _ => false

theorem supported_of_plainAnnotations {depth : Nat} {term : Tm}
    (formed : plainAnnotations depth term = true) : supported term = true := by
  induction term with
  | db _ | named _ | prim _ => rfl
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed
      simp only [supported, Bool.and_eq_true]
      exact ⟨ihf formed.1, iha formed.2⟩
  | lam _ _ ih | all _ _ ih =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed
      exact ih formed.2
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ =>
      simp [plainAnnotations] at formed

theorem lookup_variableIndex {context : Ctx Base} {type : Ty Base}
    (v : Var context type) :
    (context.map reifyType)[variableIndex v]? = some (reifyType type) := by
  induction v with
  | vz => rfl
  | vs v ih => simpa [variableIndex] using ih

/-- Intrinsic typing and exact erasure imply native inference once the native
binder annotations are formed. No environment-wide assumption is needed in this
direction: each intrinsic constant already carries its own lookup proof. -/
theorem infer_of_erase {environment : Environment} {context : Ctx Base}
    {type : Ty Base} (interpreted : Term (Constant environment) context type)
    {depth : Nat} {term : Tm} (erased : erase interpreted = some term)
    (formed : plainAnnotations depth term = true) :
    inferTerm environment depth (context.map reifyType) term = some (reifyType type) := by
  induction interpreted generalizing term with
  | var v =>
      cases erased
      exact lookup_variableIndex v
  | const constant =>
      cases constant with
      | named name declaration lookup typed =>
          cases erased
          change (environment.lookupTerm? name).map TermDecl.type = _
          rw [lookup]
          exact congrArg some typed
      | primitive index lookup =>
          cases erased
          exact lookup
  | app function argument ihf iha =>
      cases hf : erase function with
      | none => simp [erase, hf] at erased
      | some f =>
        cases ha : erase argument with
        | none => simp [erase, hf, ha] at erased
        | some a =>
            simp [erase, hf, ha] at erased
            subst term
            simp only [plainAnnotations, Bool.and_eq_true] at formed
            simp [inferTerm, ihf hf formed.1, iha ha formed.2, reifyType]
  | lam body ih =>
      cases hb : erase body with
      | none => simp [erase, hb] at erased
      | some b =>
          simp [erase, hb] at erased
          subst term
          simp only [plainAnnotations, Bool.and_eq_true] at formed
          have bodyType := ih hb formed.2
          simp only [List.map_cons] at bodyType
          simp [inferTerm, formed.1, reifyType, bodyType]
  | imp antecedent consequent iha ihc =>
      cases ha : erase antecedent with
      | none => simp [erase, ha] at erased
      | some a =>
        cases hc : erase consequent with
        | none => simp [erase, ha, hc] at erased
        | some c =>
            simp [erase, ha, hc] at erased
            subst term
            simp only [plainAnnotations, Bool.and_eq_true] at formed
            simp [inferTerm, iha ha formed.1, ihc hc formed.2, reifyType]
  | all body ih =>
      cases hb : erase body with
      | none => simp [erase, hb] at erased
      | some b =>
          simp [erase, hb] at erased
          subst term
          simp only [plainAnnotations, Bool.and_eq_true] at formed
          have bodyType := ih hb formed.2
          simp only [List.map_cons, reifyType] at bodyType
          simp [inferTerm, formed.1, reifyType, bodyType]
  | top | bot | and _ _ _ _ | or _ _ _ _ | not _ _ | eq _ _ _ _ | ex _ _ =>
      simp [erase] at erased

/-- Exact correspondence for a fixed intrinsic result type. -/
theorem infer_iff_interpretation_of_plainLookups {environment : Environment} {depth : Nat}
    {context : Ctx Base} {type : Ty Base} {term : Tm}
    (plainLookups : PlainLookups environment depth term)
    (formed : plainAnnotations depth term = true) :
    inferTerm environment depth (context.map reifyType) term = some (reifyType type) ↔
      ∃ interpreted : Term (Constant environment) context type, erase interpreted = some term := by
  constructor
  · intro accepted
    obtain ⟨value, interpreted, typed, erased⟩ :=
      interpret_of_plainLookups plainLookups (supported_of_plainAnnotations formed) accepted
    have equal := reifyType_injective typed
    subst value
    exact ⟨interpreted, erased⟩
  · rintro ⟨interpreted, erased⟩
    exact infer_of_erase interpreted erased formed

/-- The global-environment version follows from local lookup exactness. -/
theorem infer_iff_interpretation {environment : Environment} {depth : Nat}
    (plainEnvironment : PlainEnvironment environment depth)
    {context : Ctx Base} {type : Ty Base} {term : Tm}
    (formed : plainAnnotations depth term = true) :
    inferTerm environment depth (context.map reifyType) term = some (reifyType type) ↔
      ∃ interpreted : Term (Constant environment) context type, erase interpreted = some term :=
  infer_iff_interpretation_of_plainLookups
    (plainEnvironment.plainLookups (supported_of_plainAnnotations formed)) formed

/-- Prefix polymorphism cannot be hidden in the partial erasure. -/
theorem supported_of_erase {environment : Environment} {context : Ctx Base}
    {type : Ty Base} (interpreted : Term (Constant environment) context type)
    {term : Tm} (erased : erase interpreted = some term) : supported term = true := by
  induction interpreted generalizing term with
  | var _ => cases erased; rfl
  | const constant => cases constant <;> cases erased <;> rfl
  | app f a ihf iha | imp f a ihf iha =>
      cases hf : erase f with
      | none => simp [erase, hf] at erased
      | some f' =>
        cases ha : erase a with
        | none => simp [erase, hf, ha] at erased
        | some a' =>
            simp [erase, hf, ha] at erased
            subst term
            simp only [supported, Bool.and_eq_true]
            exact ⟨ihf hf, iha ha⟩
  | lam b ih | all b ih =>
      cases hb : erase b with
      | none => simp [erase, hb] at erased
      | some b' =>
          simp [erase, hb] at erased
          subst term
          exact ih (term := b') hb
  | top | bot | and _ _ _ _ | or _ _ _ _ | not _ _ | eq _ _ _ _ | ex _ _ =>
      simp [erase] at erased

theorem no_typeLam_interpretation {environment : Environment} {context : Ctx Base}
    {type : Ty Base} (body : Tm) :
    ¬ ∃ interpreted : Term (Constant environment) context type,
      erase interpreted = some (.typeLam body) := by
  rintro ⟨interpreted, erased⟩
  exact Bool.noConfusion (supported_of_erase interpreted erased)

theorem no_typeAll_interpretation {environment : Environment} {context : Ctx Base}
    {type : Ty Base} (body : Tm) :
    ¬ ∃ interpreted : Term (Constant environment) context type,
      erase interpreted = some (.typeAll body) := by
  rintro ⟨interpreted, erased⟩
  exact Bool.noConfusion (supported_of_erase interpreted erased)

theorem no_typeApp_interpretation {environment : Environment} {context : Ctx Base}
    {type : Ty Base} (body : Tm) (argument : Tp) :
    ¬ ∃ interpreted : Term (Constant environment) context type,
      erase interpreted = some (.typeApp body argument) := by
  rintro ⟨interpreted, erased⟩
  exact Bool.noConfusion (supported_of_erase interpreted erased)

namespace Examples

def environment : Environment where
  primitives := [.arr (.var 0) (.var 0)]
  terms := [⟨"step", .arr (.var 0) (.var 0), none⟩]

theorem environment_plain : PlainEnvironment environment 1 where
  named := by
    intro name declaration lookup
    simp only [environment, Environment.lookupTerm?, lookupTermList?] at lookup
    split at lookup
    · cases lookup
      decide
    · cases lookup
  primitive := by
    intro index type lookup
    cases index with
    | zero => cases lookup; decide
    | succ index => simp [environment] at lookup

def higherOrder : Tm :=
  .lam (.arr (.var 0) (.var 0))
    (.lam (.var 0) (.app (.db 1) (.app (.db 1) (.db 0))))

def higherOrderType : Ty Base :=
  .arr (.arr (.base (.inl 0)) (.base (.inl 0)))
    (.arr (.base (.inl 0)) (.base (.inl 0)))

theorem higherOrder_accepted :
    inferTerm environment 1 [] higherOrder = some (reifyType higherOrderType) := by decide

theorem higherOrder_interpreted :
    ∃ interpreted : Term (Constant environment) [] higherOrderType,
      erase interpreted = some higherOrder :=
  (infer_iff_interpretation environment_plain (by decide)).1 higherOrder_accepted

/-- Equal declared types do not identify a named symbol with a primitive. -/
def namedAndPrimitive : Tm :=
  .lam (.var 0) (.app (.named "step") (.app (.prim 0) (.db 0)))

theorem namedAndPrimitive_interpreted :
    ∃ interpreted : Term (Constant environment) []
        (.arr (.base (.inl 0)) (.base (.inl 0))),
      erase interpreted = some namedAndPrimitive :=
  (infer_iff_interpretation environment_plain (by decide)).1 (by decide)

theorem named_ne_primitive :
    (Constant.named (environment := environment)
      (type := .arr (.base (.inl 0)) (.base (.inl 0)))
      "step" ⟨"step", .arr (.var 0) (.var 0), none⟩ rfl rfl) ≠
      Constant.primitive 0 rfl := by
  intro equal
  have erased := congrArg Constant.erase equal
  cases erased

def predicateRule : Tm :=
  .all (.var 0) (.all (.arr (.var 0) .prop)
    (.imp (.app (.db 0) (.db 1)) (.app (.db 0) (.db 1))))

theorem predicateRule_interpreted :
    ∃ interpreted : ClosedFormula (Constant environment),
      erase interpreted = some predicateRule :=
  (infer_iff_interpretation environment_plain (by decide)).1 (by decide)

/-- A full native environment may contain an unrelated polymorphic declaration. -/
def mixedEnvironment : Environment :=
  { environment with terms :=
      ⟨"poly", .all (.arr (.var 0) (.var 0)), none⟩ :: environment.terms }

theorem mixedEnvironment_not_plain : ¬ PlainEnvironment mixedEnvironment 1 := by
  intro plain
  have invalid := plain.named "poly" ⟨"poly", .all (.arr (.var 0) (.var 0)), none⟩ rfl
  cases invalid

theorem mixedEnvironment_local_plain : PlainLookups mixedEnvironment 1 namedAndPrimitive := by
  simp [PlainLookups, namedAndPrimitive, mixedEnvironment, environment,
    Environment.lookupTerm?, lookupTermList?, Tp.plainWellFormed]

theorem mixedEnvironment_interpreted :
    ∃ interpreted : Term (Constant mixedEnvironment) []
        (.arr (.base (.inl 0)) (.base (.inl 0))),
      erase interpreted = some namedAndPrimitive :=
  (infer_iff_interpretation_of_plainLookups mixedEnvironment_local_plain (by decide)).1 (by decide)

def mismatch : Tm := .app (.named "step") (.lam (.var 0) (.db 0))

theorem mismatch_rejected : inferTerm environment 1 [] mismatch = none := by decide

theorem mismatch_no_interpretation (type : Ty Base) :
    ¬ ∃ interpreted : Term (Constant environment) [] type,
      erase interpreted = some mismatch := by
  rintro ⟨interpreted, erased⟩
  have accepted := infer_of_erase interpreted erased (depth := 1) (by decide)
  simp only [List.map_nil] at accepted
  rw [mismatch_rejected] at accepted
  cases accepted

/-- A genuinely accepted native polymorphic term is outside the monomorphic
constructor interpretation, not an incorrectly rejected native term. -/
theorem prefix_accepted :
    inferTerm environment 0 [] (.typeLam (.lam (.var 0) (.db 0))) =
      some (.all (.arr (.var 0) (.var 0))) := by decide

end Examples

#print axioms interpret_of_plainLookups
#print axioms interpret_native
#print axioms infer_of_erase
#print axioms infer_iff_interpretation_of_plainLookups
#print axioms no_typeLam_interpretation
#print axioms Examples.higherOrder_interpreted
#print axioms Examples.namedAndPrimitive_interpreted
#print axioms Examples.named_ne_primitive
#print axioms Examples.predicateRule_interpreted
#print axioms Examples.mixedEnvironment_interpreted
#print axioms Examples.mismatch_no_interpretation
#print axioms Examples.prefix_accepted

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
