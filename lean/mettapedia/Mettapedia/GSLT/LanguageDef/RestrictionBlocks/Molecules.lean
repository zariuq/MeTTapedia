import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Form

/-!
# Molecules of a block

A block of restrictions over a bag of components splits into **molecules**: the components connected through the
block's own restrictions, each with the restrictions it uses. Two components are in one molecule when a chain of
components links them, each consecutive pair sharing a restricted name. A component that uses no restriction of the
block is a molecule on its own.

- `groups`: the molecules of a block, as the restrictions each uses and its components, by merging a component
  into every earlier group it shares a restricted name with;
- `Prenex.molecule`: a group read as a block of its own, its restrictions renumbered from `0` in the block's order,
  the names outside the block shifted past them.

Replication splits along molecules (`!(νx)(P | Q)` gives each copy its own `x`), and a block is its molecules side
by side.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The restrictions of a block of `count` that a component uses. -/
def usedRestrictions (count : Nat) (component : Pattern) : List Nat :=
  (List.range count).filter fun index => mentions index component

/-- A group of a block: the restrictions it uses and its components. -/
structure Group where
  restrictions : List Nat
  components : List Pattern
deriving DecidableEq, Repr

/-- Whether two lists of restrictions share one. -/
def shares (first second : List Nat) : Bool := first.any fun index => second.contains index

/-- **Merge a component into the groups**, the component using the restrictions `used`: every group sharing one
with it joins it, with the merged restrictions in increasing order. -/
def insertUsing (count : Nat) (used : List Nat) (component : Pattern) (groups : List Group) : List Group :=
  let joined := groups.filter fun group => shares used group.restrictions
  let apart := groups.filter fun group => !shares used group.restrictions
  let restrictions := (List.range count).filter fun index =>
    used.contains index || joined.any fun group => group.restrictions.contains index
  apart ++ [⟨restrictions, joined.flatMap Group.components ++ [component]⟩]

/-- **Merge a component into the groups** by the restrictions of the block it uses. -/
def insertComponent (count : Nat) (component : Pattern) (groups : List Group) : List Group :=
  insertUsing count (usedRestrictions count component) component groups

/-- **The molecules of a block**: its components merged in order. -/
def groups (form : Prenex) : List Group :=
  form.components.foldl (fun groups component => insertComponent form.count component groups) []

/-- The groups of components linked through the allowed restrictions only. -/
def groupsThrough (allowed : List Nat) (count : Nat) (components : List Pattern) : List Group :=
  components.foldl (fun groups component =>
    insertUsing count ((usedRestrictions count component).filter allowed.contains) component groups) []

namespace Prenex

/-- The renumbering of a group's variables: a restriction of the group becomes its position among the group's
restrictions, a name outside the block moves past the group's restrictions. -/
def groupIndex (count : Nat) (restrictions : List Nat) (index : Nat) : Nat :=
  if index < count then restrictions.idxOf index else index - count + restrictions.length

/-- **A group as a block of its own.** -/
def molecule (count : Nat) (group : Group) : Prenex :=
  ⟨group.restrictions.length, group.components.map (rename (groupIndex count group.restrictions))⟩

end Prenex

/-! ## Controls -/

section Controls

private def a : Pattern := .fvar "a"
private def b : Pattern := .fvar "b"
private def out (channel : Pattern) : Pattern := .apply "Out" [channel]

/-- Two components on one restricted name form one molecule; a component on a free name is a molecule alone. -/
example : (groups ⟨1, [out (.bvar 0), out a, out (.bvar 0)]⟩).length = 2 := by decide +kernel

/-- Components on two restricted names, linked by a third component using both, form one molecule. -/
example : (groups ⟨2, [out (.bvar 0), out (.bvar 1), .apply "Both" [.bvar 0, .bvar 1]]⟩).length = 1 := by
  decide +kernel

/-- Without the linking component, they are two molecules. -/
example : (groups ⟨2, [out (.bvar 0), out (.bvar 1)]⟩).length = 2 := by decide +kernel

/-- A molecule renumbers its own restriction from `0` and moves an outside name past it. -/
example : Prenex.molecule 2 ⟨[1], [.apply "Both" [.bvar 1, .bvar 2]]⟩ = ⟨1, [.apply "Both" [.bvar 0, .bvar 1]]⟩ := by
  decide +kernel


end Controls

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
