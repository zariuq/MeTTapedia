import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Replication
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Molecules
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Narrow

/-!
# The canonical form with replication

A replicated process stands for unboundedly many copies, so its canonical form is a block whose replicated components
are a set and whose other components are a multiset. The canonical block is computed constructor by constructor
(`canonP`), so that the canonical form of a term depends on a part only through the part's canonical form:

- inaction is the empty block, a restriction closes its body's canonical block, a bag joins its members' canonical
  blocks, and `!P` unfolds into one replicated component per molecule of `P`'s canonical block (`replicatedOf`), a
  molecule that is itself replicated staying one (`!!P = !P`), inaction giving none (`!0 = 0`);
- each such block is normalized (`normal`): a group of other components, linked through the restrictions a
  replicated component does not use, whose block is that component's argument, is a copy of it and is dropped with
  its restrictions (`absorb`, `!P | P = !P`); the restrictions are ordered so that the components, their parts read
  canonically under that order, are least; one of each replicated component is kept (`{!P, !P} = !P`).

Normalizing a block reads only smaller blocks, so three times the size settles it.

The controls at the end separate `!(νx)P` from `(νx)!P` and finitely many copies from a replication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The canonical form with replication -/

/-- Whether a component is replicated. -/
def isReplicated (block : ReplicationBlock) : Pattern → Bool
  | .apply label [_] => label == block.replicate
  | _ => false

/-- The argument of a replicated component. -/
def replicatedArgument (block : ReplicationBlock) : Pattern → Option Pattern
  | .apply label [argument] => if label = block.replicate then some argument else none
  | _ => none

/-- The argument of a replication, any other term as it is. -/
def argumentOf? : Pattern → Pattern
  | .apply _ [argument] => argument
  | other => other

/-- **One absorption**: for some replicated component `!X`, a group of the other components, linked through the
restrictions `!X` does not use, whose block is `X`, is a copy of it and is dropped; the copy's block is not itself a
replication, every replication in the copy has a smaller canonical argument than `X`, and the copy mentions every
restriction `!X` mentions. The block keeps its restrictions, those only the copy used among them, and its numbering. -/
def absorbOnce (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) : Option Prenex :=
  (List.range form.components.length).findSome? fun position =>
    match (form.components[position]? : Option Pattern) with
    | some (.apply label [argument]) =>
        if label = block.replicate then
          let others := form.components.eraseIdx position
          let allowed := (List.range form.count).filter fun index =>
            !mentions index (.apply label [argument])
          let candidates := groupsThrough allowed form.count others
          (candidates.find? fun group =>
              (canonical (copyOf block.toBlock form.count group) ==
                canonical (rename (Prenex.groupIndex form.count (outsideOf form.count group.restrictions))
                  argument)) && !isReplicated block (canonical (copyOf block.toBlock form.count group)) &&
                group.components.all (fun component =>
                  !isReplicated block component ||
                    decide (size (canonical (argumentOf? component)) < size (canonical argument))) &&
                (List.range form.count).all (fun index =>
                  !mentions index (.apply label [argument]) || group.components.any (mentions index))).map
            fun group =>
            ⟨form.count, (candidates.erase group).flatMap Group.components ++ [.apply label [argument]]⟩
        else none
    | _ => none

/-- Absorption repeated while a copy is found, at most `rounds` times. -/
def absorbRounds (block : ReplicationBlock) (canonical : Pattern → Pattern) : Nat → Prenex → Prenex
  | 0, form => form
  | rounds + 1, form =>
      match absorbOnce block canonical form with
      | none => form
      | some next => absorbRounds block canonical rounds next

/-- **Drop the restrictions no component uses**, renumbering the others in their order. -/
def Prenex.prune (form : Prenex) : Prenex :=
  let used := (List.range form.count).filter fun index => form.components.any (mentions index)
  ⟨used.length, form.components.map (rename (Prenex.groupIndex form.count used))⟩

/-- **Absorption**: every copy of a replicated component's argument dropped, `!P | P = !P`, then the restrictions
no component uses any more. Each absorption drops at least one component, so as many rounds as components suffice. -/
def absorb (block : ReplicationBlock) (canonical : Pattern → Pattern) (form : Prenex) : Prenex :=
  (absorbRounds block canonical form.components.length form).prune

/-- Keep one of each replicated component, in order: `{!P, !P} = !P`. Finite components keep their multiplicity. -/
def dedupReplicated (block : ReplicationBlock) : List Pattern → List Pattern
  | [] => []
  | component :: rest =>
      if isReplicated block component && rest.contains component then dedupReplicated block rest
      else component :: dedupReplicated block rest

/-- **The replicated components of a replicated block**: one per molecule, its block canonical; a molecule that is a
lone replicated component stays one, since `!!P = !P`; the unit gives none, since `!0 = 0`. -/
def replicatedOf (block : ReplicationBlock) (canonical : Pattern → Pattern) (inner : Prenex) : List Pattern :=
  (groups inner).map fun group =>
    let form := Prenex.molecule inner.count group
    match form.count, form.components with
    | 0, [.apply label [argument]] =>
        if label = block.replicate then .apply label [canonical argument]
        else .apply block.replicate [canonical (Prenex.toPattern block.toBlock form)]
    | _, _ => .apply block.replicate [canonical (Prenex.toPattern block.toBlock form)]

/-! ## The orders a block is read under -/

/-- **The profile of a component** in a block of `count` restrictions: how many of the restrictions it mentions, and
whether it is a replication. -/
def profileCode (block : ReplicationBlock) (count : Nat) (component : Pattern) : Nat :=
  2 * ((List.range count).filter fun index => mentions index component).length +
    if isReplicated block component then 1 else 0

/-- **The signature of a restriction**: the profiles of the components that mention it, each counted once, as a set
of bits. Renaming the restrictions, reading components alike and repeating a component keep it. -/
def signatureOf (block : ReplicationBlock) (form : Prenex) (index : Nat) : Nat :=
  ((((form.components.filter (mentions index)).map (profileCode block form.count)).dedup).map (2 ^ ·)).sum

/-- **The arrangements of a list whose keys never decrease**: each begins with an element of least key. -/
def keyedArrangements (key : Nat → Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | fuel + 1, first :: rest =>
      ((first :: rest).filter fun element => key element = rest.foldr (fun other low => min (key other) low) (key first)).flatMap
        fun chosen => (keyedArrangements key fuel ((first :: rest).erase chosen)).map (chosen :: ·)

/-- **The orders a block is read under**: every order of its restrictions; or, for a refined block, the orders that
sort the restrictions by their signatures, those of one signature in every order among themselves. -/
def readingOrders (block : ReplicationBlock) (form : Prenex) : List (List Nat) :=
  if block.refined then
    (keyedArrangements (signatureOf block form) form.count (List.range form.count)).map (inverse form.count)
  else orders (List.range form.count)

mutual
  /-- **The canonical form of a block whose components have canonical parts**, within a fuel: its copies absorbed,
  its restrictions in the order, among its reading orders (`readingOrders`), that makes its components least once
  their parts are read again under that order, one of each replicated component. A copy is recognized by the canonical forms of its block and of the replicated
  argument, each a smaller block. -/
  def normalizeWith (block : ReplicationBlock) : Nat → Prenex → Prenex
    | 0, form => form
    | fuel + 1, form =>
        let absorbed := absorb block (fun pattern =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern))) form
        ⟨absorbed.count, least ((readingOrders block absorbed).map fun order =>
          dedupReplicated block (sortComponents (absorbed.components.map fun component =>
            recanonWith block fuel (rename (Prenex.permute absorbed.count order) component))))⟩

  /-- **A component's parts read canonically again**, within a fuel, as after a renaming: the block of every
  argument normalized, a named multiset's argument read back as a multiset. The restriction applied to anything but a
  binder is no restriction, and is left as it is written. -/
  def recanonWith (block : ReplicationBlock) : Nat → Pattern → Pattern
    | 0, component => component
    | fuel + 1, .apply constructor arguments =>
        if constructor = block.restrict then .apply constructor arguments
        else if constructor ∈ block.multisets then .apply constructor (arguments.map (recanonMultisetWith block fuel))
        else .apply constructor (arguments.map (canonArgument fun argument =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock argument))))
    | fuel + 1, .lambda binder body =>
        .lambda binder (Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock body)))
    | fuel + 1, .multiLambda arity binders body =>
        .multiLambda arity binders
          (Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock body)))
    | fuel + 1, .collection kind elements rest =>
        .collection kind (elements.map fun element =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock element))) rest
    | _ + 1, component => component

  /-- A named multiset's argument read canonically again, within a fuel: an open collection keeps its members'
  order and its rest, an explicit substitution stays, any other argument is read as the multiset of its block. -/
  def recanonMultisetWith (block : ReplicationBlock) : Nat → Pattern → Pattern
    | 0, argument => argument
    | fuel + 1, .collection kind elements (some rest) =>
        .collection kind (elements.map fun element =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock element))) (some rest)
    | _ + 1, .subst body replacement => .subst body replacement
    | fuel + 1, argument => multisetOf block.toBlock (normalizeWith block fuel (decompose block.toBlock argument))
end

/-- **The canonical form of a block with canonical parts**, with fuel that settles it. -/
def normal (block : ReplicationBlock) (form : Prenex) : Prenex :=
  normalizeWith block (3 * size (Prenex.toPattern block.toBlock form) + 3) form

/-- The canonical form of a pattern whose parts are canonical, read as a block. -/
def canonicalOf (block : ReplicationBlock) (pattern : Pattern) : Pattern :=
  Prenex.toPattern block.toBlock (normal block (decompose block.toBlock pattern))

/-- An argument of a constructor with canonical parts, from the canonical block of the argument: a named
multiset's argument as a multiset (an open collection and an explicit substitution as they are), any other
argument as its block's pattern. -/
def argumentOf (block : ReplicationBlock) (label : String) (argument : Pattern) (form : Prenex) : Pattern :=
  if label ∈ block.multisets then
    match argument with
    | .collection _ _ (some _) => Prenex.toPattern block.toBlock form
    | .subst _ _ => Prenex.toPattern block.toBlock form
    | _ => multisetOf block.toBlock form
  else Prenex.toPattern block.toBlock form

mutual
  /-- **The canonical block of a pattern with replication**, constructor by constructor: inaction is the empty
  block; a restriction closes the canonical block of its body; `!P` is the block of the replicated molecules of
  `P`'s canonical block; a bag joins its members' canonical blocks; each of these is normalized. Any other term is
  one component with canonical parts. -/
  def canonP (block : ReplicationBlock) : Pattern → Prenex
    | .apply label [] => if label = block.unit then Prenex.nil else Prenex.atom (.apply label [])
    | .apply label [.lambda binder body] =>
        if label = block.restrict then normal block (canonP block body).close
        else Prenex.atom (.apply label [argumentOf block label (.lambda binder body)
          (Prenex.atom (.lambda binder (Prenex.toPattern block.toBlock (canonP block body))))])
    | .apply label [argument] =>
        if label = block.replicate then
          normal block ⟨0, replicatedOf block (canonicalOf block) (canonP block argument)⟩
        else if label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil then Prenex.nil
        else Prenex.atom (.apply label [argumentOf block label argument (canonP block argument)])
    | .apply label arguments =>
        Prenex.atom (.apply label (List.zipWith (argumentOf block label) arguments (canonsP block arguments)))
    | .collection .hashBag elements none => normal block ((canonsP block elements).foldr Prenex.par Prenex.nil)
    | .collection kind elements rest =>
        Prenex.atom (.collection kind ((canonsP block elements).map (Prenex.toPattern block.toBlock)) rest)
    | .lambda binder body => Prenex.atom (.lambda binder (Prenex.toPattern block.toBlock (canonP block body)))
    | .multiLambda arity binders body =>
        Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block body)))
    | other => Prenex.atom other

  /-- The canonical blocks of a list of patterns. -/
  def canonsP (block : ReplicationBlock) : List Pattern → List Prenex
    | [] => []
    | pattern :: patterns => canonP block pattern :: canonsP block patterns
end

/-- **The canonical form of a process with replication.** -/
def canonR (block : ReplicationBlock) (process : Pattern) : Pattern :=
  Prenex.toPattern block.toBlock (canonP block process)

/-! ## Controls -/

section Controls

private def a : Pattern := .fvar "a"
private def b : Pattern := .fvar "b"

/-! ### The canonical form with replication -/

private def rep : ReplicationBlock := ⟨⟨"Nil", "Nu", "Proc", "Name", [], []⟩, "Rep", false⟩
private def bang (process : Pattern) : Pattern := .apply "Rep" [process]
private def par (processes : List Pattern) : Pattern := .collection .hashBag processes none
private def nu (body : Pattern) : Pattern := .apply "Nu" [.lambda none body]
private def nil : Pattern := .apply "Nil" []
private def act (channel : Pattern) : Pattern := .apply "Act" [channel, nil]

/-- `!a.0 | a.0 = !a.0`: a copy is absorbed. -/
example : canonR rep (par [bang (act a), act a]) = canonR rep (bang (act a)) := by decide +kernel

/-- `!!a.0 = !a.0` and `!0 = 0`. -/
example : canonR rep (bang (bang (act a))) = canonR rep (bang (act a)) := by decide +kernel
example : canonR rep (bang nil) = canonR rep nil := by decide +kernel

/-- `!(a.0 | b.0) = !a.0 | !b.0`, and `!a.0 | !a.0 = !a.0`. -/
example : canonR rep (bang (par [act a, act b])) = canonR rep (par [bang (act b), bang (act a)]) := by decide +kernel
example : canonR rep (par [bang (act a), bang (act a)]) = canonR rep (bang (act a)) := by decide +kernel

/-- `(νx)(!x.0 | x.0) = (νx)!x.0`: absorption under a shared restricted name. -/
example : canonR rep (nu (par [bang (act (.bvar 0)), act (.bvar 0)])) = canonR rep (nu (bang (act (.bvar 0)))) := by
  decide +kernel

/-- `(νy)a.y | !(νy)a.y = !(νy)a.y`: a copy with its own restriction is absorbed. -/
example : canonR rep (par [nu (act (.bvar 0)), bang (nu (act (.bvar 0)))]) = canonR rep (bang (nu (act (.bvar 0)))) := by
  decide +kernel

/-- Every copy is absorbed: `!a.0 | a.0 | a.0 = !a.0`. -/
example : canonR rep (par [bang (act a), act a, act a]) = canonR rep (bang (act a)) := by decide +kernel

/-- A copy holding its own replicated component is absorbed: with `M = (νx)(a⟨x⟩ | !b⟨x⟩)`, `!M | M = !M`. -/
example : canonR rep (par [bang (nu (par [.apply "Out" [a, .bvar 0], bang (.apply "Out" [b, .bvar 0])])),
    nu (par [.apply "Out" [a, .bvar 0], bang (.apply "Out" [b, .bvar 0])])]) =
    canonR rep (bang (nu (par [.apply "Out" [a, .bvar 0], bang (.apply "Out" [b, .bvar 0])]))) := by
  decide +kernel

/-- **Negatives.** `!(νx)x.0` and `(νx)!x.0` stay apart: every copy has its own name in the first. -/
example : canonR rep (bang (nu (act (.bvar 0)))) ≠ canonR rep (nu (bang (act (.bvar 0)))) := by decide +kernel

/-- A replicated process is not one copy: `!a.0 ≠ a.0`. -/
example : canonR rep (bang (act a)) ≠ canonR rep (act a) := by decide +kernel

/-- `(νx)(!x.0 | b.0)`: a finite component on another name is kept. -/
example : canonR rep (nu (par [bang (act (.bvar 0)), act b])) ≠ canonR rep (nu (bang (act (.bvar 0)))) := by
  decide +kernel

/-- Two finite copies of a molecule with a shared name are not one replicated one: `(νx)(x.0 | x.0) ≠ (νx)!x.0`. -/
example : canonR rep (nu (par [act (.bvar 0), act (.bvar 0)])) ≠ canonR rep (nu (bang (act (.bvar 0)))) := by
  decide +kernel


/-! ### Replication with a named multiset of guards -/

private def repSum : ReplicationBlock := ⟨⟨"Nil", "Nu", "Proc", "Name", ["Sum"], ["Sum"]⟩, "Rep", false⟩
private def guard (channel : Pattern) : Pattern := .apply "G" [channel, nil]
private def sum (guards : List Pattern) : Pattern := .apply "Sum" [.collection .hashBag guards none]

/-- A sum of one guard keeps its collection: a summand is not a parallel component. -/
example : canonR repSum (sum [guard a]) = sum [guard a] := by decide +kernel

/-- Summands stand in no order, also under replication. -/
example : canonR repSum (sum [guard a, guard b]) = canonR repSum (sum [guard b, guard a]) := by decide +kernel
example : canonR repSum (bang (sum [guard a, guard b])) = canonR repSum (bang (sum [guard b, guard a])) := by
  decide +kernel

/-- A replicated sum absorbs a copy of itself with its summands in another order. -/
example : canonR repSum (par [bang (sum [guard a, guard b]), sum [guard b, guard a]]) =
    canonR repSum (bang (sum [guard a, guard b])) := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
