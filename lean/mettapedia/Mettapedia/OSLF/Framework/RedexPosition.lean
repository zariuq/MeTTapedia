import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Redex positions, one-hole contexts, and rely variables

The type-system generator reads a rewrite rule *together with a choice of redex
position*.  Choosing a subterm occurrence `t_j` of a left-hand side `L`
determines a one-hole context `K_j[-]` with `K_j[t_j] = L`, and splits the
rule's variables in two:

* `V_j = FV(K_j) \ FV(t_j)` — the **rely parameters** of the modality generated
  at that position; and
* `W_j = FV(t_j) \ FV(K_j)` — the variables the chosen subterm keeps to itself.

This module supplies that input layer, and nothing above it: positions into a
`Pattern`, the one-hole context a position names, the plug operation, and the
two variable sets.  Everything is a function of the authored rule, so no slot
family downstream is written by hand.

A one-hole context is represented by its host pattern together with a position,
rather than by a separate inductive with a hole constructor.  The two readings
agree through `plug`: `plug L pos t` rebuilds `L` with the subterm at `pos`
replaced by `t`, and `plug_subtermAt` states `K_j[t_j] = L`.
-/

namespace Mettapedia.OSLF.Framework.RedexPosition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Positions -/

/-- A position is a path from the root; each step selects a child by index. -/
abbrev Position := List Nat

/-- The immediate children of a pattern, in the order positions index them. -/
def children : Pattern → List Pattern
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ args => args
  | .lambda _ body => [body]
  | .multiLambda _ _ body => [body]
  | .subst body replacement => [body, replacement]
  | .collection _ elements _ => elements

/-- The child at one index, if there is one. -/
def childAt (p : Pattern) (i : Nat) : Option Pattern :=
  (children p)[i]?

/-- Rebuild a pattern with one child replaced.  The shape and every other
child are retained; an out-of-range index has no rebuild. -/
def withChildAt : Pattern → Nat → Pattern → Option Pattern
  | .apply f args, i, c =>
      if i < args.length then some (.apply f (args.set i c)) else none
  | .lambda b _, 0, c => some (.lambda b c)
  | .multiLambda n xs _, 0, c => some (.multiLambda n xs c)
  | .subst _ r, 0, c => some (.subst c r)
  | .subst b _, 1, c => some (.subst b c)
  | .collection t elements rest, i, c =>
      if i < elements.length then some (.collection t (elements.set i c) rest)
      else none
  | _, _, _ => none

/-- Every child of a pattern is smaller than it.  This is what makes the
position enumeration below terminate. -/
theorem sizeOf_children_lt {p c : Pattern} (mem : c ∈ children p) :
    sizeOf c < sizeOf p := by
  cases p with
  | bvar _ => simp [children] at mem
  | fvar _ => simp [children] at mem
  | apply f args =>
      have hc : sizeOf c < sizeOf args := List.sizeOf_lt_of_mem (by simpa [children] using mem)
      have : sizeOf args < sizeOf (Pattern.apply f args) := by
        simp +arith [Pattern.apply.sizeOf_spec]
      omega
  | lambda b body =>
      have : c = body := by simpa [children] using mem
      subst this
      simp +arith [Pattern.lambda.sizeOf_spec]
  | multiLambda n xs body =>
      have : c = body := by simpa [children] using mem
      subst this
      simp +arith [Pattern.multiLambda.sizeOf_spec]
  | subst body replacement =>
      have hmem : c = body ∨ c = replacement := by simpa [children] using mem
      rcases hmem with h | h <;> subst h <;>
        simp +arith [Pattern.subst.sizeOf_spec]
  | collection t elements rest =>
      have hc : sizeOf c < sizeOf elements :=
        List.sizeOf_lt_of_mem (by simpa [children] using mem)
      have : sizeOf elements < sizeOf (Pattern.collection t elements rest) := by
        simp +arith [Pattern.collection.sizeOf_spec]
      omega

/-- The subterm at a position, if the path is valid. -/
def subtermAt : Pattern → Position → Option Pattern
  | p, [] => some p
  | p, i :: rest => (childAt p i).bind fun c => subtermAt c rest

/-- Plug a pattern into the hole a position names: rebuild the host with the
subterm at that position replaced. -/
def plug : Pattern → Position → Pattern → Option Pattern
  | _, [], t => some t
  | p, i :: rest, t =>
      (childAt p i).bind fun c =>
        (plug c rest t).bind fun c' => withChildAt p i c'

mutual

/-- All positions of a pattern, root first.  Written by structural recursion on
the constructor fields so that the enumeration reduces in the kernel. -/
def positions : Pattern → List Position
  | .bvar _ => [[]]
  | .fvar _ => [[]]
  | .apply _ args => [] :: positionsList args 0
  | .lambda _ body => [] :: (positions body).map (fun pos => 0 :: pos)
  | .multiLambda _ _ body => [] :: (positions body).map (fun pos => 0 :: pos)
  | .subst body replacement =>
      [] :: (((positions body).map (fun pos => 0 :: pos)) ++
             ((positions replacement).map (fun pos => 1 :: pos)))
  | .collection _ elements _ => [] :: positionsList elements 0

/-- Positions of a list of children, offset by the index of the first. -/
def positionsList : List Pattern → Nat → List Position
  | [], _ => []
  | c :: cs, i =>
      ((positions c).map (fun pos => i :: pos)) ++ positionsList cs (i + 1)

end

/-! ## Contexts and their variables

The variable notion is `freeFvarNames`, the one the presentation validator
uses: collection rest names are metavariable positions and count as free.  A
node's own variable positions are those not carried by any child — the name of
an `fvar` leaf, and the rest name of a collection — so walking a path collects,
at each step, the node's local variables together with every sibling's free
variables. -/

/-- The variable positions a node owns directly rather than through a child. -/
def localVars : Pattern → List String
  | .fvar name => [name]
  | .collection _ _ rest => rest.toList
  | _ => []

/-! `Pattern.freeFvarNames` is the presentation validator's notion of a free
metavariable position, and it is the one used here — but it is compiled by
well-founded recursion over the nested `List Pattern`, so it does not reduce
definitionally and no statement about it can be closed in the kernel.  The
mutually structural implementation below does reduce, and `fvarNames_eq`
proves the two agree, so the generated slot families can be checked by
computation without introducing a second convention. -/

mutual

/-- Free metavariable positions of a pattern, by structural recursion. -/
def fvarNames : Pattern → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .apply _ args => fvarNamesList args
  | .lambda _ body => fvarNames body
  | .multiLambda _ _ body => fvarNames body
  | .subst body replacement => fvarNames body ++ fvarNames replacement
  | .collection _ elements rest => fvarNamesList elements ++ rest.toList

/-- Free metavariable positions of a list of patterns. -/
def fvarNamesList : List Pattern → List String
  | [] => []
  | p :: ps => fvarNames p ++ fvarNamesList ps

end

mutual

/-- The structural implementation agrees with the validator's notion. -/
theorem fvarNames_eq : (p : Pattern) → fvarNames p = p.freeFvarNames
  | .bvar _ => by simp [fvarNames, Pattern.freeFvarNames]
  | .fvar _ => by simp [fvarNames, Pattern.freeFvarNames]
  | .apply _ args => by
      simp [fvarNames, Pattern.freeFvarNames, fvarNamesList_eq args]
  | .lambda _ body => by
      simp [fvarNames, Pattern.freeFvarNames, fvarNames_eq body]
  | .multiLambda _ _ body => by
      simp [fvarNames, Pattern.freeFvarNames, fvarNames_eq body]
  | .subst body replacement => by
      simp [fvarNames, Pattern.freeFvarNames, fvarNames_eq body,
        fvarNames_eq replacement]
  | .collection _ elements _ => by
      simp [fvarNames, Pattern.freeFvarNames, fvarNamesList_eq elements]

/-- The list form agrees with flattening the validator's notion. -/
theorem fvarNamesList_eq :
    (ps : List Pattern) → fvarNamesList ps = ps.flatMap Pattern.freeFvarNames
  | [] => by simp [fvarNamesList]
  | p :: ps => by
      simp [fvarNamesList, fvarNames_eq p, fvarNamesList_eq ps]

end

/-- At the empty binder context the validator's free-variable notion is the
structural one, so a statement about it reduces in the kernel. -/
theorem patternFvarNames_nil (p : Pattern) :
    Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternFvarNames [] p = fvarNames p := by
  simp [Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternFvarNames, ← fvarNames_eq]

/-- The list form, which is the shape a validator's scan of a premise's
arguments takes. -/
theorem flatMap_patternFvarNames_nil (ps : List Pattern) :
    ps.flatMap (Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternFvarNames [])
      = fvarNamesList ps := by
  induction ps with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [fvarNamesList, patternFvarNames_nil, inductionHypothesis]

/-! `LanguageDef.patternBinderNames` is the presentation validator's notion of
the binder names a rule introduces, and it is the one the validation gate uses —
but it recurses through `List.attach`, so it does not reduce definitionally and
no statement about it can be closed in the kernel either.  The mutually
structural implementation below does reduce, and `binderNames_eq` proves the two
agree, so a presentation's validation can be checked by computation without
introducing a second convention. -/

mutual

/-- Binder names a pattern introduces, by structural recursion. -/
def binderNames : Pattern → List String
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ arguments => binderNamesList arguments
  | .lambda binder body =>
      (match binder with | some name => [name] | none => []) ++ binderNames body
  | .multiLambda _ binders body => binders ++ binderNames body
  | .subst body replacement => binderNames body ++ binderNames replacement
  | .collection _ elements _ => binderNamesList elements

/-- Binder names of a list of patterns. -/
def binderNamesList : List Pattern → List String
  | [] => []
  | pattern :: patterns => binderNames pattern ++ binderNamesList patterns

end

mutual

/-- The structural implementation agrees with the validator's notion. -/
theorem binderNames_eq :
    (p : Pattern) → binderNames p = Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames p
  | .bvar _ => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames]
  | .fvar _ => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames]
  | .apply _ arguments => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames,
        binderNamesList_eq arguments]
  | .lambda binder body => by
      cases binder <;>
        simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames,
          binderNames_eq body]
  | .multiLambda _ _ body => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames,
        binderNames_eq body]
  | .subst body replacement => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames,
        binderNames_eq body, binderNames_eq replacement]
  | .collection _ elements _ => by
      simp [binderNames, Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames,
        binderNamesList_eq elements]

/-- The list form agrees with flattening the validator's notion. -/
theorem binderNamesList_eq :
    (ps : List Pattern) →
      binderNamesList ps
        = ps.flatMap Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.patternBinderNames
  | [] => by simp [binderNamesList]
  | pattern :: patterns => by
      simp [binderNamesList, binderNames_eq pattern, binderNamesList_eq patterns]

end

/-- The free variables of the one-hole context `K_j[-]`: the free variables of
the host that survive removing the subterm at the given position. -/
def contextFreeVars : Pattern → Position → List String
  | _, [] => []
  | p, i :: rest =>
      let siblingVars :=
        (children p).zipIdx.flatMap fun ci =>
          if ci.2 = i then [] else fvarNames ci.1
      let deeper :=
        match childAt p i with
        | some c => contextFreeVars c rest
        | none => []
      localVars p ++ siblingVars ++ deeper

/-- The free variables of the chosen subterm `t_j`, or none if the path is
invalid. -/
def focusFreeVars (host : Pattern) (pos : Position) : List String :=
  match subtermAt host pos with
  | some t => fvarNames t
  | none => []

/-- The rely parameters `V_j = FV(K_j) \ FV(t_j)` of the modality generated at
a redex position: free in the context, not in the chosen subterm. -/
def relyVars (host : Pattern) (pos : Position) : List String :=
  let inner := focusFreeVars host pos
  (contextFreeVars host pos).filter (fun x => !inner.contains x) |>.eraseDups

/-- The variables `W_j = FV(t_j) \ FV(K_j)` the chosen subterm hides from its
own context. -/
def hiddenVars (host : Pattern) (pos : Position) : List String :=
  let outer := contextFreeVars host pos
  (focusFreeVars host pos).filter (fun x => !outer.contains x) |>.eraseDups

/-- The number of sort slots the modality at a redex position carries: one per
rely parameter, and one for the output. -/
def slotCount (host : Pattern) (pos : Position) : Nat :=
  (relyVars host pos).length + 1

/-! ## The context laws -/

/-- Rebuilding a child in place is the identity. -/
theorem withChildAt_childAt {p c : Pattern} {i : Nat}
    (h : childAt p i = some c) : withChildAt p i c = some p := by
  cases p with
  | bvar _ => simp [childAt, children] at h
  | fvar _ => simp [childAt, children] at h
  | apply f args =>
      have hlt : i < args.length := by
        by_contra hge
        simp [childAt, children, List.getElem?_eq_none (by omega : args.length ≤ i)] at h
      have hget : args[i]'hlt = c := by
        simpa [childAt, children, List.getElem?_eq_getElem hlt] using h
      simp [withChildAt, hlt, ← hget]
  | lambda b body =>
      match i with
      | 0 =>
          have : body = c := by simpa [childAt, children] using h
          simp [withChildAt, this]
      | (n + 1) => simp [childAt, children] at h
  | multiLambda n xs body =>
      match i with
      | 0 =>
          have : body = c := by simpa [childAt, children] using h
          simp [withChildAt, this]
      | (m + 1) => simp [childAt, children] at h
  | subst body replacement =>
      match i with
      | 0 =>
          have : body = c := by simpa [childAt, children] using h
          simp [withChildAt, this]
      | 1 =>
          have : replacement = c := by simpa [childAt, children] using h
          simp [withChildAt, this]
      | (n + 2) => simp [childAt, children] at h
  | collection t elements rest =>
      have hlt : i < elements.length := by
        by_contra hge
        simp [childAt, children,
          List.getElem?_eq_none (by omega : elements.length ≤ i)] at h
      have hget : elements[i]'hlt = c := by
        simpa [childAt, children, List.getElem?_eq_getElem hlt] using h
      simp [withChildAt, hlt, ← hget]

/-- `K_j[t_j] = L`: plugging a position's own subterm back in returns the host.
This is the law that makes the (host, position) pair a genuine one-hole
context for that subterm. -/
theorem plug_subtermAt {host t : Pattern} {pos : Position}
    (h : subtermAt host pos = some t) : plug host pos t = some host := by
  induction pos generalizing host with
  | nil => simpa [plug] using (by simpa [subtermAt] using h.symm)
  | cons i rest ih =>
      rcases hc : childAt host i with _ | c
      · simp [subtermAt, hc] at h
      · have hrest : subtermAt c rest = some t := by
          simpa [subtermAt, hc] using h
        simp [plug, hc, ih hrest, withChildAt_childAt hc]

end Mettapedia.OSLF.Framework.RedexPosition
