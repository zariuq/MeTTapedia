import Mettapedia.Languages.Agda.Adequacy.StaticObservationNaturality
import Mettapedia.Languages.Agda.Adequacy.StaticForward
import Mettapedia.Languages.Agda.Structural.SpineStatics
import Mettapedia.Languages.Agda.StaticSpecification.Judgments

/-!
# Conditional source interpretation of the six spine constructors

Each witness retains an actual native derivation, successful observations of
its context and syntax, and actual source typing evidence. The constructors
below compose witnessed premises; they do not produce witnesses for arbitrary
native trees. A spine action consumes a typed head. Its nil case provides no
type formation. Input/output conversions and append's intermediate type are
preserved in the source typing construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation

open Mettapedia.OSLF.Binding
open Structural (sig scope)
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)

def context : {n : Nat} → RawContext n → Option (StaticSpecification.RawContext n)
  | _, .nil => some .nil
  | _, .snoc Γ A => do
      let Γ ← context Γ
      let A ← type A
      pure (.snoc Γ A)

@[simp] theorem context_embed {n : Nat} (Γ : StaticSpecification.RawContext n) :
    context (embedContext Γ) = some Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih =>
      change (do
        let Γ ← context (embedContext Γ)
        let A ← type (embedTy A)
        pure (StaticSpecification.RawContext.snoc Γ A)) = _
      rw [ih, type_embed]
      rfl

def typeBody {n : Nat} : TypeBody n → Option (StaticSpecification.TyAbs n)
  | .bind A => (type A.code).map .bind
  | .noBind A => (type A.code).map .noBind

@[simp] theorem typeBody_embed {n : Nat} (b : StaticSpecification.TyAbs n) :
    typeBody (embedTypeBody b) = some b := by
  cases b with
  | bind A =>
      change (type (embedTypeParameter A).code).map StaticSpecification.TyAbs.bind = _
      rw [embedTypeParameter_code, type_embed]
      rfl
  | noBind A =>
      change (type (embedTypeParameter A).code).map StaticSpecification.TyAbs.noBind = _
      rw [embedTypeParameter_code, type_embed]
      rfl

theorem typeParameter_level {n : Nat} (A : TypeParameter n) {a : StaticSpecification.Ty n}
    (supported : type A.code = some a) : a.level = A.level := by
  change (term A.term).bind (fun head => some (StaticSpecification.Ty.el A.level head)) = some a at supported
  obtain ⟨head, _supported, equality⟩ := Option.bind_eq_some_iff.mp supported
  cases Option.some.inj equality
  rfl

theorem typeBody_level {n : Nat} (B : TypeBody n) {b : StaticSpecification.TyAbs n}
    (supported : typeBody B = some b) : b.level = B.level := by
  cases B with
  | bind A =>
      change (type A.code).map StaticSpecification.TyAbs.bind = some b at supported
      obtain ⟨a, observed, rfl⟩ := Option.map_eq_some_iff.mp supported
      exact typeParameter_level A observed
  | noBind A =>
      change (type A.code).map StaticSpecification.TyAbs.noBind = some b at supported
      obtain ⟨a, observed, rfl⟩ := Option.map_eq_some_iff.mp supported
      exact typeParameter_level A observed

theorem piType_observed {n : Nat} (A : TypeParameter n) (B : TypeBody n)
    {a : StaticSpecification.Ty n} {b : StaticSpecification.TyAbs n}
    (domain : type A.code = some a) (body : typeBody B = some b) :
    type (Structural.Statics.piType A B).code = some (StaticSpecification.Ty.pi a b) := by
  have domainLevel := typeParameter_level A domain
  have bodyLevel := typeBody_level B body
  have piObserved : term (B.pi A) = some (.pi a b) := by
    cases B with
    | bind B =>
        change (type B.code).map StaticSpecification.TyAbs.bind = some b at body
        obtain ⟨b, observed, rfl⟩ := Option.map_eq_some_iff.mp body
        change (do
          let a ← type A.code
          let b ← type B.code
          pure (StaticSpecification.Term.pi a (.bind b))) = _
        rw [domain, observed]
        rfl
    | noBind B =>
        change (type B.code).map StaticSpecification.TyAbs.noBind = some b at body
        obtain ⟨b, observed, rfl⟩ := Option.map_eq_some_iff.mp body
        change (do
          let a ← type A.code
          let b ← type B.code
          pure (StaticSpecification.Term.pi a (.noBind b))) = _
        rw [domain, observed]
        rfl
  change (term (B.pi A)).bind (fun head =>
    some (StaticSpecification.Ty.el (max A.level B.level) head)) = _
  rw [piObserved]
  change some (StaticSpecification.Ty.el (max A.level B.level) (.pi a b)) = _
  rw [← domainLevel, ← bodyLevel]
  rfl

theorem single_observes {n : Nat} {argument : RawTm n} {a : StaticSpecification.Term n}
    (supported : term argument = some a) :
    SubObserves (Structural.Statics.single argument) (StaticSpecification.Substitution.single a) := by
  intro index
  refine Fin.cases supported (fun i => ?_) index
  change some (StaticSpecification.Term.var (readVar (embedVar i))) = some (.var i)
  rw [read_embedVar]

theorem typeBody_instantiate {n : Nat} (B : TypeBody n) {b : StaticSpecification.TyAbs n}
    {argument : RawTm n} {a : StaticSpecification.Term n}
    (body : typeBody B = some b) (arg : term argument = some a) :
    type (B.instantiate argument).code = some (b.instantiate a) := by
  cases B with
  | bind B =>
      change (type B.code).map StaticSpecification.TyAbs.bind = some b at body
      obtain ⟨b, observed, rfl⟩ := Option.map_eq_some_iff.mp body
      exact observe_bind_of_some (single_observes arg) observed
  | noBind B =>
      change (type B.code).map StaticSpecification.TyAbs.noBind = some b at body
      obtain ⟨b, observed, rfl⟩ := Option.map_eq_some_iff.mp body
      rw [Structural.Statics.TypeBody.instantiate_noBind, StaticSpecification.TyAbs.instantiate_noBind]
      exact observed

/-- The observations and both actual derivations are retained together. -/
structure TypingWitness {n : Nat} (Γ : RawContext n) (Δ : StaticSpecification.RawContext n)
    (t : RawTm n) (A : RawTy n) (f : StaticSpecification.Term n) (a : StaticSpecification.Ty n) where
  native : Structural.SpineStatics.CoreDerivation (Structural.Statics.typed Γ t A)
  context_eq : context Γ = some Δ
  term_eq : term t = some f
  type_eq : type A = some a
  source : StaticSpecification.Typing Δ f a

structure TypeEqualityWitness {n : Nat} (Γ : RawContext n) (Δ : StaticSpecification.RawContext n)
    (A B : RawTy n) (a b : StaticSpecification.Ty n) where
  native : Structural.SpineStatics.CoreDerivation (Structural.Statics.typeEqual Γ A B)
  context_eq : context Γ = some Δ
  left_eq : type A = some a
  right_eq : type B = some b
  source : StaticSpecification.TypeEq Δ a b

/-- Existing forward adequacy provides witnessed canonical premises. -/
noncomputable def TypingWitness.ofSource {n : Nat} {Γ : StaticSpecification.RawContext n}
    {f : StaticSpecification.Term n} {a : StaticSpecification.Ty n} (source : StaticSpecification.Typing Γ f a) :
    TypingWitness (embedContext Γ) Γ (embedTerm f) (embedTy a) f a where
  native := Structural.SpineStatics.includeCanonical (typingForward source)
  context_eq := context_embed Γ
  term_eq := term_embed f
  type_eq := type_embed a
  source := source

noncomputable def TypeEqualityWitness.ofSource {n : Nat} {Γ : StaticSpecification.RawContext n}
    {a b : StaticSpecification.Ty n} (source : StaticSpecification.TypeEq Γ a b) :
    TypeEqualityWitness (embedContext Γ) Γ (embedTy a) (embedTy b) a b where
  native := Structural.SpineStatics.includeCanonical (typeEqualityForward source)
  context_eq := context_embed Γ
  left_eq := type_embed a
  right_eq := type_embed b
  source := source

/-- A conditional source action returns an actual source typing derivation. -/
abbrev SourceAction {n : Nat} (Δ : StaticSpecification.RawContext n)
    (a : StaticSpecification.Ty n) (es : StaticSpecification.Spine n) (b : StaticSpecification.Ty n) :=
  ∀ {f : StaticSpecification.Term n}, StaticSpecification.Typing Δ f a →
    StaticSpecification.Typing Δ (f.applySpine es) b

structure ActionWitness {n : Nat} (Γ : RawContext n) (Δ : StaticSpecification.RawContext n)
    (A : RawTy n) (es : Structural.Spine (scope n)) (B : RawTy n)
    (a : StaticSpecification.Ty n) (sourceSpine : StaticSpecification.Spine n) (b : StaticSpecification.Ty n) where
  native : Structural.SpineStatics.Action Γ A es B
  context_eq : context Γ = some Δ
  input_eq : type A = some a
  spine_eq : spine es = some sourceSpine
  output_eq : type B = some b
  source : SourceAction Δ a sourceSpine b

namespace ActionWitness

def nil {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A : RawTy n} {a : StaticSpecification.Ty n}
    (observedContext : context Γ = some Δ) (observedType : type A = some a) :
    ActionWitness Γ Δ A Structural.nil A a [] a where
  native := Structural.SpineStatics.Derivation.nil Γ A
  context_eq := observedContext
  input_eq := observedType
  spine_eq := rfl
  output_eq := observedType
  source := fun head => head

def cons {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A : TypeParameter n} {B : TypeBody n} {argument : RawTm n}
    {rest : Structural.Spine (scope n)} {C : RawTy n}
    {a : StaticSpecification.Ty n} {b : StaticSpecification.TyAbs n}
    {u : StaticSpecification.Term n} {es : StaticSpecification.Spine n} {c : StaticSpecification.Ty n}
    (body : typeBody B = some b)
    (arg : TypingWitness Γ Δ argument A.code u a)
    (tail : ActionWitness Γ Δ (B.instantiate argument).code rest C (b.instantiate u) es c) :
    ActionWitness Γ Δ (Structural.Statics.piType A B).code
      (Structural.cons (Structural.apply argument) rest) C (StaticSpecification.Ty.pi a b) (.apply u :: es) c where
  native := Structural.SpineStatics.Derivation.cons arg.native tail.native
  context_eq := arg.context_eq
  input_eq := piType_observed A B arg.type_eq body
  spine_eq := cons_of_some (apply_of_some arg.term_eq) tail.spine_eq
  output_eq := tail.output_eq
  source := fun head => tail.source (.app head arg.source)

def append {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A B C : RawTy n} {first second : Structural.Spine (scope n)}
    {a b c : StaticSpecification.Ty n} {es fs : StaticSpecification.Spine n}
    (left : ActionWitness Γ Δ A first B a es b) (right : ActionWitness Γ Δ B second C b fs c) :
    ActionWitness Γ Δ A (Structural.append first second) C a (es ++ fs) c where
  native := Structural.SpineStatics.Derivation.append left.native right.native
  context_eq := left.context_eq
  input_eq := left.input_eq
  spine_eq := append_of_some left.spine_eq right.spine_eq
  output_eq := right.output_eq
  source := fun {f} head =>
    (congrArg (fun t => StaticSpecification.Typing Δ t c)
      (StaticSpecification.Term.applySpine_append f es fs)).mpr
      (right.source (left.source head))

def inputConversion {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A' A B : RawTy n} {es : Structural.Spine (scope n)}
    {a' a b : StaticSpecification.Ty n} {sourceSpine : StaticSpecification.Spine n}
    (equal : TypeEqualityWitness Γ Δ A' A a' a)
    (action : ActionWitness Γ Δ A es B a sourceSpine b) :
    ActionWitness Γ Δ A' es B a' sourceSpine b where
  native := Structural.SpineStatics.Derivation.inputConversion equal.native action.native
  context_eq := equal.context_eq
  input_eq := equal.left_eq
  spine_eq := action.spine_eq
  output_eq := action.output_eq
  source := fun head => action.source (.conv head equal.source)

def outputConversion {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A B B' : RawTy n} {es : Structural.Spine (scope n)}
    {a b b' : StaticSpecification.Ty n} {sourceSpine : StaticSpecification.Spine n}
    (action : ActionWitness Γ Δ A es B a sourceSpine b)
    (equal : TypeEqualityWitness Γ Δ B B' b b') :
    ActionWitness Γ Δ A es B' a sourceSpine b' where
  native := Structural.SpineStatics.Derivation.outputConversion action.native equal.native
  context_eq := action.context_eq
  input_eq := action.input_eq
  spine_eq := action.spine_eq
  output_eq := equal.right_eq
  source := fun head => .conv (action.source head) equal.source

def elimination {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {head : RawTm n} {A B : RawTy n} {es : Structural.Spine (scope n)}
    {f : StaticSpecification.Term n} {a b : StaticSpecification.Ty n} {sourceSpine : StaticSpecification.Spine n}
    (typed : TypingWitness Γ Δ head A f a) (action : ActionWitness Γ Δ A es B a sourceSpine b) :
    TypingWitness Γ Δ (Structural.eliminate head es) B (f.applySpine sourceSpine) b where
  native := Structural.SpineStatics.Derivation.elimination typed.native action.native
  context_eq := typed.context_eq
  term_eq := eliminate_of_some typed.term_eq action.spine_eq
  type_eq := action.output_eq
  source := action.source typed.source

end ActionWitness

end Mettapedia.Languages.Agda.StaticAdequacy.Observation
