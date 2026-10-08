import Mettapedia.OSLF.Framework.InstrumentObservations

/-!
# Enlarging a labelled instrument kit refines its observations

The same labelled response is retained exactly whenever its constructor is
already admitted by the smaller kit. This reflection, rather than inclusion
of unlabelled rewrite relations, earns bisimulation monotonicity. Transport
of receipts retains the supplied origin, constructor, argument bundle and
selected position. Erasure of the independently computed views composes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentObservations

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

def Label.constructor : Label Symbols arity → Symbols
  | .ask constructor => constructor
  | .get constructor _ => constructor
  | .build constructor => constructor

namespace Event

variable {smaller larger last : Policy Symbols}
  {source target : State Symbols arity} {label : Label Symbols arity}

theorem permission (event : Event larger source label target) : larger label.constructor := by
  cases event <;> assumption

def weaken (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (event : Event smaller source label target) : Event larger source label target := by
  cases event with
  | ask constructor arguments allowed => exact .ask constructor arguments (inclusion _ allowed)
  | get constructor arguments allowed position =>
      exact .get constructor arguments (inclusion _ allowed) position
  | build constructor arguments allowed => exact .build constructor arguments (inclusion _ allowed)

def restrict (allowed : smaller label.constructor)
    (event : Event larger source label target) : Event smaller source label target := by
  cases event with
  | ask constructor arguments _ => exact .ask constructor arguments allowed
  | get constructor arguments _ position => exact .get constructor arguments allowed position
  | build constructor arguments _ => exact .build constructor arguments allowed

theorem weaken_identity (event : Event smaller source label target) :
    weaken (fun _ allowed => allowed) event = event := by
  cases event <;> rfl

theorem weaken_composition
    (first : ∀ constructor, smaller constructor → larger constructor)
    (second : ∀ constructor, larger constructor → last constructor)
    (event : Event smaller source label target) :
    weaken second (weaken first event) =
      weaken (fun constructor allowed => second constructor (first constructor allowed)) event := by
  cases event <;> rfl

theorem restrict_weaken
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (event : Event smaller source label target) :
    restrict (permission event) (weaken inclusion event) = event := by
  cases event <;> rfl

end Event

theorem response_permission {opened : Policy Symbols}
    {source target : State Symbols arity} {label : Label Symbols arity}
    (response : Response opened source label target) : opened label.constructor := by
  obtain ⟨event⟩ := response
  exact event.permission

theorem response_mono {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {source target : State Symbols arity} {label : Label Symbols arity}
    (response : Response smaller source label target) : Response larger source label target := by
  obtain ⟨event⟩ := response
  exact ⟨event.weaken inclusion⟩

theorem old_label_responses_iff {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {source target : State Symbols arity} {label : Label Symbols arity}
    (allowed : smaller label.constructor) :
    Response larger source label target ↔ Response smaller source label target := by
  constructor
  · rintro ⟨event⟩
    exact ⟨event.restrict allowed⟩
  · exact response_mono inclusion

theorem IsBisimulation.smaller {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {relation : State Symbols arity → State Symbols arity → Prop}
    (bisimulation : IsBisimulation larger relation) : IsBisimulation smaller relation where
  tags := bisimulation.tags
  forward := by
    intro source other related label target response
    have allowed := response_permission response
    obtain ⟨matched, responds, paired⟩ :=
      bisimulation.forward related (response_mono inclusion response)
    exact ⟨matched, (old_label_responses_iff inclusion allowed).1 responds, paired⟩
  backward := by
    intro source other related label target response
    have allowed := response_permission response
    obtain ⟨matched, responds, paired⟩ :=
      bisimulation.backward related (response_mono inclusion response)
    exact ⟨matched, (old_label_responses_iff inclusion allowed).1 responds, paired⟩

theorem bisimilar_mono {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {source other : State Symbols arity} (related : Bisimilar larger source other) :
    Bisimilar smaller source other := by
  obtain ⟨relation, bisimulation, paired⟩ := related
  exact ⟨relation, bisimulation.smaller inclusion, paired⟩

namespace Receipt

variable {Origins : Type u} {smaller larger last : Policy Symbols}
  {source target : State Symbols arity} {label : Label Symbols arity}

def weaken (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (receipt : Receipt Origins smaller source label target) :
    Receipt Origins larger source label target :=
  ⟨receipt.origin, receipt.event.weaken inclusion⟩

theorem weaken_origin (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (receipt : Receipt Origins smaller source label target) :
    (receipt.weaken inclusion).origin = receipt.origin := rfl

theorem weaken_identity (receipt : Receipt Origins smaller source label target) :
    receipt.weaken (fun _ allowed => allowed) = receipt := by
  cases receipt with
  | mk origin event => cases event <;> rfl

theorem weaken_composition
    (first : ∀ constructor, smaller constructor → larger constructor)
    (second : ∀ constructor, larger constructor → last constructor)
    (receipt : Receipt Origins smaller source label target) :
    (receipt.weaken first).weaken second =
      receipt.weaken (fun constructor allowed => second constructor (first constructor allowed)) := by
  cases receipt with
  | mk origin event => cases event <;> rfl

end Receipt

def eraseView (smaller : Policy Symbols) : View Symbols arity → View Symbols arity
  | .opaque => .opaque
  | .visible constructor arguments => by
      classical
      exact if smaller constructor then
        .visible constructor (fun position => eraseView smaller (arguments position))
      else .opaque

theorem erase_view {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (tree : Tree Symbols arity) : eraseView smaller (view larger tree) = view smaller tree := by
  classical
  induction tree with
  | node constructor arguments inductionHypothesis =>
    by_cases allowed : smaller constructor
    · simp only [view, if_pos allowed, if_pos (inclusion _ allowed), eraseView]
      congr 1
      funext position
      exact inductionHypothesis position
    · by_cases wasAllowed : larger constructor
      · simp only [view, if_pos wasAllowed, if_neg allowed, eraseView]
      · simp only [view, if_neg wasAllowed, if_neg allowed, eraseView]

theorem erase_composition {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    (observed : View Symbols arity) :
    eraseView smaller (eraseView larger observed) = eraseView smaller observed := by
  classical
  induction observed with
  | «opaque» => rfl
  | visible constructor arguments inductionHypothesis =>
    by_cases allowed : smaller constructor
    · simp only [eraseView, if_pos allowed, if_pos (inclusion _ allowed)]
      congr 1
      funext position
      exact inductionHypothesis position
    · by_cases wasAllowed : larger constructor
      · simp only [eraseView, if_pos wasAllowed, if_neg allowed]
      · simp only [eraseView, if_neg wasAllowed, if_neg allowed]

theorem view_mono {smaller larger : Policy Symbols}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {source other : Tree Symbols arity} (same : view larger source = view larger other) :
    view smaller source = view smaller other := by
  rw [← erase_view inclusion source, ← erase_view inclusion other, same]

end Mettapedia.OSLF.Framework.InstrumentObservations
