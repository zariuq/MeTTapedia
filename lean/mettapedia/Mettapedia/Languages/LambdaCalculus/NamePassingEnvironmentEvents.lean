import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironment

/-!
# Retained origins of name-passing environment events

`FetchCertificate` and `EventCertificate` retain the selected constructor
derivation in `Type`. Their erased soundness and completeness refer to the
existing `FetchAt` and `Step` relations; they introduce no additional source
transition rule. An origin distinguishes the declaration or beta redex that
fires from the reference occurrence it services. This distinction matters
when two declarations can service the same reference at equal endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

/-- One edge of an independently authored active evaluation context. -/
inductive Position where
  | appFunction
  | definitionBody
  | carrierBody
  deriving DecidableEq, Repr

/-- A proof-relevant selected reference occurrence. Constructor arguments
retain the expression and binder context in which selection was made. -/
inductive FetchCertificate : {Γ : List Srt} → Var Γ nm → Expr nm Γ →
    Expr nm Γ → Expr nm Γ → Type where
  | here {Γ} (name : Var Γ nm) (value : Expr nm Γ) :
      FetchCertificate name value (.var name) value
  | app {Γ} {name : Var Γ nm} {value function function' : Expr nm Γ}
      (argument : Var Γ nm) :
      FetchCertificate name value function function' →
      FetchCertificate name value (.app function argument) (.app function' argument)
  | defn {Γ} {name : Var Γ nm} {value : Expr nm Γ}
      (stored : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      FetchCertificate (.succ name) (NamePassing.weaken value) body body' →
      FetchCertificate name value (.defn stored body) (.defn stored body')
  | carrier {Γ} {name : Var Γ nm} {value body body' : Expr nm Γ}
      (subject : Var Γ nm) (stored : Expr nm Γ) :
      FetchCertificate name value body body' →
      FetchCertificate name value (.carrier subject stored body) (.carrier subject stored body')

namespace FetchCertificate

/-- Erasure checks the certificate against the existing lookup authority. -/
theorem sound : {Γ : List Srt} → {name : Var Γ nm} →
    {value source target : Expr nm Γ} →
    FetchCertificate name value source target → FetchAt name value source target
  | _, _, _, _, _, .here name value => .here name value
  | _, _, _, _, _, .app argument selected => .app argument selected.sound
  | _, _, _, _, _, .defn stored selected => .defn stored selected.sound
  | _, _, _, _, _, .carrier subject stored selected =>
      .carrier subject stored selected.sound

/-- The active reference address is computed from the retained derivation. -/
def address : {Γ : List Srt} → {name : Var Γ nm} →
    {value source target : Expr nm Γ} →
    FetchCertificate name value source target → List Position
  | _, _, _, _, _, .here _ _ => []
  | _, _, _, _, _, .app _ selected => .appFunction :: selected.address
  | _, _, _, _, _, .defn _ selected => .definitionBody :: selected.address
  | _, _, _, _, _, .carrier _ _ selected => .carrierBody :: selected.address

/-- Certificates cover exactly the independently specified reference lookups. -/
theorem nonempty_iff {Γ : List Srt} {name : Var Γ nm}
    {value source target : Expr nm Γ} :
    Nonempty (FetchCertificate name value source target) ↔
      FetchAt name value source target := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.sound
  · intro fetch
    induction fetch with
    | here name value => exact ⟨.here name value⟩
    | app argument selected ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.app argument certificate⟩
    | defn stored selected ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.defn stored certificate⟩
    | carrier subject stored selected ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.carrier subject stored certificate⟩

end FetchCertificate

/-- A retained source firing. Lookup constructors carry their real selected
reference derivation rather than a label attached to an erased step proof. -/
inductive EventCertificate : Action → {Γ : List Srt} →
    Expr nm Γ → Expr nm Γ → Type where
  | beta {Γ} (body : Expr nm (nm :: Γ)) (argument : Var Γ nm) :
      EventCertificate .beta (.app (.lam body) argument)
        (NamePassing.instantiate body argument)
  | carrierFetch {Γ} (name : Var Γ nm) (value : Expr nm Γ)
      {body body' : Expr nm Γ} : FetchCertificate name value body body' →
      EventCertificate .carrierFetch (.carrier name value body) body'
  | environmentFetch {Γ} (value : Expr nm Γ)
      {body body' : Expr nm (nm :: Γ)} :
      FetchCertificate .zero (NamePassing.weaken value) body body' →
      EventCertificate .environmentFetch (.defn value body) (.defn value body')
  | app {Γ kind} {function function' : Expr nm Γ} (argument : Var Γ nm) :
      EventCertificate kind function function' →
      EventCertificate kind (.app function argument) (.app function' argument)
  | defn {Γ kind} (value : Expr nm Γ) {body body' : Expr nm (nm :: Γ)} :
      EventCertificate kind body body' →
      EventCertificate kind (.defn value body) (.defn value body')
  | carrier {Γ kind} (name : Var Γ nm) (value : Expr nm Γ)
      {body body' : Expr nm Γ} :
      EventCertificate kind body body' →
      EventCertificate kind (.carrier name value body) (.carrier name value body')

/-- The firing owner and selected reference have distinct operational roles.
Beta does not perform a reference fetch and has no reference address. -/
structure EventOrigin where
  action : Action
  owner : List Position
  reference : Option (List Position)
  deriving DecidableEq, Repr

namespace EventCertificate

/-- Erasure checks the retained event against the existing step authority. -/
theorem sound : {kind : Action} → {Γ : List Srt} →
    {source target : Expr nm Γ} → EventCertificate kind source target →
    Step kind source target
  | _, _, _, _, .beta body argument => .beta body argument
  | _, _, _, _, .carrierFetch name value selected =>
      .carrierFetch name value selected.sound
  | _, _, _, _, .environmentFetch value selected =>
      .environmentFetch value selected.sound
  | _, _, _, _, .app argument event => .app argument event.sound
  | _, _, _, _, .defn value event => .defn value event.sound
  | _, _, _, _, .carrier name value event => .carrier name value event.sound

def owner : {kind : Action} → {Γ : List Srt} →
    {source target : Expr nm Γ} → EventCertificate kind source target → List Position
  | _, _, _, _, .beta _ _ => []
  | _, _, _, _, .carrierFetch _ _ _ => []
  | _, _, _, _, .environmentFetch _ _ => []
  | _, _, _, _, .app _ event => .appFunction :: event.owner
  | _, _, _, _, .defn _ event => .definitionBody :: event.owner
  | _, _, _, _, .carrier _ _ event => .carrierBody :: event.owner

def reference : {kind : Action} → {Γ : List Srt} →
    {source target : Expr nm Γ} → EventCertificate kind source target →
    Option (List Position)
  | _, _, _, _, .beta _ _ => none
  | _, _, _, _, .carrierFetch _ _ selected => some (.carrierBody :: selected.address)
  | _, _, _, _, .environmentFetch _ selected => some (.definitionBody :: selected.address)
  | _, _, _, _, .app _ event => event.reference.map (.appFunction :: ·)
  | _, _, _, _, .defn _ event => event.reference.map (.definitionBody :: ·)
  | _, _, _, _, .carrier _ _ event => event.reference.map (.carrierBody :: ·)

/-- Readout derives the rule and addresses from the actual constructor tree. -/
def origin {kind : Action} {Γ : List Srt} {source target : Expr nm Γ}
    (event : EventCertificate kind source target) : EventOrigin :=
  ⟨kind, event.owner, event.reference⟩

/-- Retained events cover exactly the independently authored communication
relation; keeping their derivation neither adds nor drops source steps. -/
theorem nonempty_iff {kind : Action} {Γ : List Srt}
    {source target : Expr nm Γ} :
    Nonempty (EventCertificate kind source target) ↔ Step kind source target := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.sound
  · intro step
    induction step with
    | beta body argument => exact ⟨.beta body argument⟩
    | carrierFetch name value fetch =>
        obtain ⟨certificate⟩ := FetchCertificate.nonempty_iff.mpr fetch
        exact ⟨.carrierFetch name value certificate⟩
    | environmentFetch value fetch =>
        obtain ⟨certificate⟩ := FetchCertificate.nonempty_iff.mpr fetch
        exact ⟨.environmentFetch value certificate⟩
    | app argument step ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.app argument certificate⟩
    | defn value step ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.defn value certificate⟩
    | carrier name value step ih =>
        obtain ⟨certificate⟩ := ih
        exact ⟨.carrier name value certificate⟩

end EventCertificate

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment
