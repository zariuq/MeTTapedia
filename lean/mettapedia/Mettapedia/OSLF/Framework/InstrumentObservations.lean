import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Retained labelled observations of a finite-arity instrument kit

The carrier is the independent closed first-order constructor algebra.
An opening returns its actual argument bundle; projection reads a supplied
position; rebuilding returns the same constructed term. Event evidence is
kept separately from the existential response relation. Bisimulation is
defined by labelled response matching and bundle tags, before its comparison
with the independently computed partial structural view.

An unopened node is opaque. Opening an ancestor is required before any of
its descendants can be inspected. These results do not authorize stepping
under a binder or identify labelled kit observations with arbitrary
unlabelled reductions of an extended presentation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentObservations

universe u

variable (Symbols : Type u) (arity : Symbols → Nat)

inductive Tree where
  | node (constructor : Symbols) (arguments : Fin (arity constructor) → Tree)

inductive View where
  | opaque
  | visible (constructor : Symbols) (arguments : Fin (arity constructor) → View)

inductive State where
  | term (value : Tree Symbols arity)
  | bundle (value : Tree Symbols arity)

inductive Label where
  | ask (constructor : Symbols)
  | get (constructor : Symbols) (position : Fin (arity constructor))
  | build (constructor : Symbols)

variable {Symbols arity}

abbrev Policy (Symbols : Type u) := Symbols → Prop

def view (opened : Policy Symbols) : Tree Symbols arity → View Symbols arity
  | .node constructor arguments => by
      classical
      exact if opened constructor then
        .visible constructor (fun position => view opened (arguments position))
      else .opaque

inductive Readout where
  | term (value : View Symbols arity)
  | bundle (constructor : Symbols) (value : Option (View Symbols arity))

def readout (opened : Policy Symbols) : State Symbols arity → @Readout Symbols arity
  | .term value => .term (view opened value)
  | .bundle (.node constructor arguments) => by
      classical
      exact .bundle constructor
        (if opened constructor then some (view opened (.node constructor arguments)) else none)

def tag : State Symbols arity → Option Symbols
  | .term _ => none
  | .bundle (.node constructor _) => some constructor

def Readout.tag : @Readout Symbols arity → Option Symbols
  | .term _ => none
  | .bundle constructor _ => some constructor

theorem readout_tag (opened : Policy Symbols) (state : State Symbols arity) :
    (readout opened state).tag = tag state := by
  cases state with
  | term value => rfl
  | bundle value => cases value; rfl

inductive Event (opened : Policy Symbols) :
    State Symbols arity → Label Symbols arity → State Symbols arity → Type u where
  | ask (constructor : Symbols) (arguments : Fin (arity constructor) → Tree Symbols arity)
      (permission : opened constructor) :
      Event opened (.term (.node constructor arguments)) (.ask constructor)
        (.bundle (.node constructor arguments))
  | get (constructor : Symbols) (arguments : Fin (arity constructor) → Tree Symbols arity)
      (permission : opened constructor) (position : Fin (arity constructor)) :
      Event opened (.bundle (.node constructor arguments)) (.get constructor position)
        (.term (arguments position))
  | build (constructor : Symbols) (arguments : Fin (arity constructor) → Tree Symbols arity)
      (permission : opened constructor) :
      Event opened (.bundle (.node constructor arguments)) (.build constructor)
        (.term (.node constructor arguments))

abbrev Response (opened : Policy Symbols) (source : State Symbols arity)
    (label : Label Symbols arity) (target : State Symbols arity) : Prop :=
  Nonempty (Event opened source label target)

structure Receipt (Origins : Type u) (opened : Policy Symbols)
    (source : State Symbols arity) (label : Label Symbols arity)
    (target : State Symbols arity) where
  origin : Origins
  event : Event opened source label target

theorem receipt_support_iff (Origins : Type u) [Nonempty Origins]
    (opened : Policy Symbols) (source : State Symbols arity)
    (label : Label Symbols arity) (target : State Symbols arity) :
    Nonempty (Receipt Origins opened source label target) ↔
      Response opened source label target := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.event⟩
  · rintro ⟨event⟩
    exact ⟨⟨Classical.choice inferInstance, event⟩⟩

structure IsBisimulation (opened : Policy Symbols)
    (relation : State Symbols arity → State Symbols arity → Prop) : Prop where
  tags : ∀ {source other}, relation source other → tag source = tag other
  forward : ∀ {source other}, relation source other → ∀ {label target},
    Response opened source label target →
      ∃ matched, Response opened other label matched ∧ relation target matched
  backward : ∀ {source other}, relation source other → ∀ {label target},
    Response opened other label target →
      ∃ matched, Response opened source label matched ∧ relation matched target

def Bisimilar (opened : Policy Symbols) (source other : State Symbols arity) : Prop :=
  ∃ relation, IsBisimulation opened relation ∧ relation source other

theorem related_visible_term (opened : Policy Symbols)
    {constructor : Symbols} {arguments : Fin (arity constructor) → Tree Symbols arity}
    {other : State Symbols arity} (permission : opened constructor)
    (same : readout opened (.term (.node constructor arguments)) = readout opened other) :
    ∃ compared : Fin (arity constructor) → Tree Symbols arity,
      other = .term (.node constructor compared) ∧
        ∀ position, view opened (arguments position) = view opened (compared position) := by
  classical
  cases other with
  | bundle value => cases value; cases same
  | term value =>
    cases value with
    | node second compared =>
      by_cases secondPermission : opened second
      · simp only [readout, view, if_pos permission, if_pos secondPermission,
          Readout.term.injEq] at same
        obtain ⟨sameConstructor, sameArguments⟩ := View.visible.inj same
        subst second
        exact ⟨compared, rfl, fun position => congrFun (eq_of_heq sameArguments) position⟩
      · simp only [readout, view, if_pos permission, if_neg secondPermission,
          Readout.term.injEq] at same
        cases same

theorem related_visible_bundle (opened : Policy Symbols)
    {constructor : Symbols} {arguments : Fin (arity constructor) → Tree Symbols arity}
    {other : State Symbols arity} (permission : opened constructor)
    (same : readout opened (.bundle (.node constructor arguments)) = readout opened other) :
    ∃ compared : Fin (arity constructor) → Tree Symbols arity,
      other = .bundle (.node constructor compared) ∧
        ∀ position, view opened (arguments position) = view opened (compared position) := by
  classical
  cases other with
  | term value => cases same
  | bundle value =>
    cases value with
    | node second compared =>
      have sameTag := congrArg Readout.tag same
      change some constructor = some second at sameTag
      have sameConstructor := Option.some.inj sameTag
      subst second
      simp only [readout, view, if_pos permission,
        Readout.bundle.injEq, true_and, Option.some.injEq] at same
      obtain ⟨_, sameArguments⟩ := View.visible.inj same
      exact ⟨compared, rfl, fun position => congrFun (eq_of_heq sameArguments) position⟩

theorem kernel_forward (opened : Policy Symbols)
    {source other : State Symbols arity}
    (same : readout opened source = readout opened other)
    {label : Label Symbols arity} {target : State Symbols arity}
    (response : Response opened source label target) :
    ∃ matched, Response opened other label matched ∧
      readout opened target = readout opened matched := by
  classical
  obtain ⟨event⟩ := response
  cases event with
  | ask constructor arguments permission =>
      obtain ⟨compared, rfl, children⟩ := related_visible_term opened permission same
      refine ⟨.bundle (.node constructor compared), ⟨.ask constructor compared permission⟩, ?_⟩
      simp only [readout, view, if_pos permission]
      exact congrArg (fun values => Readout.bundle constructor
        (some (View.visible constructor values))) (funext children)
  | get constructor arguments permission position =>
      obtain ⟨compared, rfl, children⟩ := related_visible_bundle opened permission same
      exact ⟨.term (compared position), ⟨.get constructor compared permission position⟩,
        congrArg Readout.term (children position)⟩
  | build constructor arguments permission =>
      obtain ⟨compared, rfl, children⟩ := related_visible_bundle opened permission same
      refine ⟨.term (.node constructor compared), ⟨.build constructor compared permission⟩, ?_⟩
      simp only [readout, view, if_pos permission]
      exact congrArg (fun values => Readout.term (View.visible constructor values))
        (funext children)

theorem kernel_bisimulation (opened : Policy Symbols) :
    IsBisimulation opened (fun source other : State Symbols arity =>
      readout opened source = readout opened other) where
  tags same := by
    have result := congrArg Readout.tag same
    simpa only [readout_tag] using result
  forward := by
    intro source other same label target response
    exact kernel_forward opened same response
  backward := by
    intro source other same label target response
    obtain ⟨matched, responds, result⟩ := kernel_forward opened same.symm response
    exact ⟨matched, responds, result.symm⟩

theorem bisimilar_of_same_readout (opened : Policy Symbols)
    {source other : State Symbols arity}
    (same : readout opened source = readout opened other) : Bisimilar opened source other :=
  ⟨_, kernel_bisimulation opened, same⟩

theorem term_views_of_bisimulation (opened : Policy Symbols)
    {relation : State Symbols arity → State Symbols arity → Prop}
    (bisimulation : IsBisimulation opened relation) :
    ∀ left right : Tree Symbols arity,
      relation (.term left) (.term right) → view opened left = view opened right := by
  classical
  intro left
  induction left with
  | node constructor arguments inductionHypothesis =>
      intro right related
      cases right with
      | node second compared =>
        by_cases permission : opened constructor
        · obtain ⟨matched, ⟨event⟩, bundles⟩ :=
            bisimulation.forward related ⟨Event.ask constructor arguments permission⟩
          cases event
          simp only [view, if_pos permission]
          congr 1
          funext position
          obtain ⟨matched, ⟨projection⟩, children⟩ :=
            bisimulation.forward bundles ⟨Event.get constructor arguments permission position⟩
          cases projection
          exact inductionHypothesis position _ children
        · by_cases secondPermission : opened second
          · obtain ⟨matched, ⟨event⟩, _⟩ :=
              bisimulation.backward related ⟨Event.ask second compared secondPermission⟩
            cases event
            exact False.elim (permission secondPermission)
          · simp only [view, if_neg permission, if_neg secondPermission]

theorem term_bisimilar_iff_view (opened : Policy Symbols) (left right : Tree Symbols arity) :
    Bisimilar opened (.term left) (.term right) ↔ view opened left = view opened right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact term_views_of_bisimulation opened bisimulation left right related
  · intro same
    exact bisimilar_of_same_readout opened (congrArg Readout.term same)

end Mettapedia.OSLF.Framework.InstrumentObservations
