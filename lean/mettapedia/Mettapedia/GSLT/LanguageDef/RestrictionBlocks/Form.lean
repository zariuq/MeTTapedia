import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.PatternLexOrder

/-!
# Restriction blocks

A calculus with restriction composes processes in parallel in a bag with a unit, and restricts names by a binder over
a process. Modulo restriction of inaction, exchange of restrictions and scope extrusion, besides the bag's laws, a
process is a block of restrictions over a bag of components, each of which is neither the unit, nor a bag, nor a
restriction (`Prenex`). The constructors are named by the calculus (`Block`): π's `PiNil` and `PiNu`, CCS's, the
ambients', any calculus's.

- `decompose` reads the block off a process without looking inside its components; a restriction no component uses is
  dropped where it is read (`Prenex.close`).
- `canonWith` reorders the block's restrictions to make the sorted canonical components least, with canonical parts
  inside every component; `canon` gives it fuel enough.
- A named multiset (CCS's sum) is a component; its argument is read as a block too, and read back as a multiset
  (`canonMultisetWith`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

/-- **The signature of a calculus's blocks**: the unit of its parallel bag and its restriction, the sort of its
processes and the sort of the names a restriction binds; its named multiset operators, whose one argument is a bag
of terms of another sort, reordered but never merged into the parallel bag; and those of them whose empty instance is
the unit, as CCS's empty sum is inaction. -/
structure Block where
  unit : String
  restrict : String
  proc : String
  name : String
  multisets : List String
  emptyUnits : List String
  deriving DecidableEq, Repr

/-- `count` restrictions over the bag of `components`; inside the block the innermost restriction is the bound
variable `0`. -/
structure Prenex where
  count : Nat
  components : List Pattern
deriving DecidableEq, Repr

namespace Prenex

/-- Inaction: no restriction over no component. -/
def nil : Prenex := ⟨0, []⟩

/-- One component, unrestricted. -/
def atom (component : Pattern) : Prenex := ⟨0, [component]⟩

/-- One more restriction, outside the block. -/
def restrict (form : Prenex) : Prenex := ⟨form.count + 1, form.components⟩

/-- **Two blocks side by side**, the first one's restrictions outermost: the first block's components are read
under the second's restrictions, and the second's ambient names skip the first's restrictions. -/
def par (first second : Prenex) : Prenex :=
  ⟨first.count + second.count,
    first.components.map (liftBVars 0 second.count) ++
      second.components.map (liftBVars second.count first.count)⟩

/-- The bag of the components: the unit when empty, the component itself when single. -/
def body (block : Block) : List Pattern → Pattern
  | [] => .apply block.unit []
  | [component] => component
  | components => .collection .hashBag components none

/-- `count` restrictions, outermost first. -/
def restricts (block : Block) : Nat → Pattern → Pattern
  | 0, process => process
  | count + 1, process => .apply block.restrict [.lambda none (restricts block count process)]

/-- **Read the block back** as a process. -/
def toPattern (block : Block) (form : Prenex) : Pattern := restricts block form.count (body block form.components)

@[simp] theorem nil_count : nil.count = 0 := rfl
@[simp] theorem nil_components : nil.components = [] := rfl
@[simp] theorem restrict_count (form : Prenex) : form.restrict.count = form.count + 1 := rfl
@[simp] theorem par_count (first second : Prenex) : (first.par second).count = first.count + second.count := rfl

theorem restricts_succ (block : Block) (count : Nat) (process : Pattern) :
    restricts block (count + 1) process = .apply block.restrict [.lambda none (restricts block count process)] := rfl

/-- Inaction on the left of a block changes nothing. -/
theorem nil_par (form : Prenex) : nil.par form = form := by
  cases form with
  | mk count components =>
      simp only [par, nil, Nat.zero_add, List.map_nil, List.nil_append, mk.injEq, true_and]
      conv_rhs => rw [← List.map_id components]
      apply List.map_congr_left
      intro component _
      exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

end Prenex

open Prenex

/-! ## Garbage -/

mutual
  /-- Whether a pattern mentions the bound variable `index`. -/
  def mentions (index : Nat) : Pattern → Bool
    | .bvar other => other == index
    | .fvar _ => false
    | .apply _ arguments => mentionsList index arguments
    | .lambda _ body => mentions (index + 1) body
    | .multiLambda arity _ body => mentions (index + arity) body
    | .subst body replacement => mentions (index + 1) body || mentions index replacement
    | .collection _ elements _ => mentionsList index elements

  def mentionsList (index : Nat) : List Pattern → Bool
    | [] => false
    | pattern :: patterns => mentions index pattern || mentionsList index patterns
end

/-- Rename the free bound variables. -/
def rename (relabel : Nat → Nat) (pattern : Pattern) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (fun index => .bvar (relabel index)) pattern

/-- Remove the bound variable `cutoff`: those below it stay, those above it move down one. -/
def dropIndex (cutoff index : Nat) : Nat := if index < cutoff then index else index - 1

namespace Prenex

/-- **One more restriction outside the block**, dropped when no component uses it: the components see it as the
variable just past the block's own restrictions. -/
def close (form : Prenex) : Prenex :=
  if form.components.any (mentions form.count) then form.restrict
  else ⟨form.count, form.components.map (rename (dropIndex form.count))⟩

/-- Reorder the block's restrictions: restriction `index` becomes `order[index]`. -/
def permute (count : Nat) (order : List Nat) (index : Nat) : Nat :=
  if index < count then order.getD index index else index

end Prenex

/-! ## Blocks -/

mutual
  /-- **The block of a process**, read without looking inside its components; a restriction no component uses is
  dropped where it is read. A binder's display name is not read. A named multiset whose empty instance is the unit
  is inaction when its argument is. -/
  def decompose (block : Block) : Pattern → Prenex
    | .apply label [] => if label = block.unit then nil else atom (.apply label [])
    | .apply label [.lambda binder body] =>
        if label = block.restrict then (decompose block body).close else atom (.apply label [.lambda binder body])
    | .apply label [argument] =>
        if label ∈ block.emptyUnits ∧ decompose block argument = nil then nil else atom (.apply label [argument])
    | .collection .hashBag elements none => decomposeList block elements
    | other => atom other

  /-- The blocks of the members of a bag, side by side. -/
  def decomposeList (block : Block) : List Pattern → Prenex
    | [] => nil
    | element :: elements => (decompose block element).par (decomposeList block elements)
end

theorem decompose_unit (block : Block) : decompose block (.apply block.unit []) = nil := by simp [decompose]

theorem decompose_restrict (block : Block) (binder : Option String) (body : Pattern) :
    decompose block (.apply block.restrict [.lambda binder body]) = (decompose block body).close := by
  simp [decompose]

theorem decompose_bag (block : Block) (elements : List Pattern) :
    decompose block (.collection .hashBag elements none) = decomposeList block elements := by simp [decompose]

/-- **A multiset whose empty instance is the unit is inaction when its argument is**, and otherwise its own block. -/
theorem decompose_multiset {block : Block} {label : String} {argument : Pattern}
    (notRestriction : ∀ binder body, Pattern.apply label [argument] ≠ .apply block.restrict [.lambda binder body]) :
    decompose block (.apply label [argument]) =
      if label ∈ block.emptyUnits ∧ decompose block argument = nil then nil
      else atom (.apply label [argument]) := by
  cases argument with
  | lambda binder body =>
      have different : label ≠ block.restrict := fun same => notRestriction binder body (by rw [same])
      have notNil : decompose block (.lambda binder body) ≠ nil := by simp [decompose, atom, nil]
      rw [if_neg (fun empty => notNil empty.2)]
      simp [decompose, different]
  | _ => simp only [decompose]

/-- **A multiset that is not inaction is its own block.** -/
theorem decompose_multiset_atom {block : Block} {label : String} {argument : Pattern}
    (notRestriction : ∀ binder body, Pattern.apply label [argument] ≠ .apply block.restrict [.lambda binder body])
    (notEmpty : ¬ (label ∈ block.emptyUnits ∧ decompose block argument = nil)) :
    decompose block (.apply label [argument]) = atom (.apply label [argument]) := by
  rw [decompose_multiset notRestriction, if_neg notEmpty]

/-- **Anything else is its own block.** -/
theorem decompose_atom {block : Block} {process : Pattern} (notUnit : process ≠ .apply block.unit [])
    (notRestriction : ∀ binder body, process ≠ .apply block.restrict [.lambda binder body])
    (notBag : ∀ elements, process ≠ .collection .hashBag elements none)
    (notEmpty : ∀ label argument, process = .apply label [argument] → label ∉ block.emptyUnits) :
    decompose block process = atom process := by
  match process, notUnit, notRestriction, notBag, notEmpty with
  | .apply label [], notUnit, _, _, _ =>
      have different : label ≠ block.unit := fun same => notUnit (by rw [same])
      simp [decompose, different]
  | .apply label [.lambda binder body], _, notRestriction, _, _ =>
      have different : label ≠ block.restrict := fun same => notRestriction binder body (by rw [same])
      simp [decompose, different]
  | .apply label [.bvar index], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .apply label [.fvar name], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .apply label [.apply constructor arguments], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .apply label [.multiLambda arity binders body], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .apply label [.subst body replacement], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .apply label [.collection kind elements rest], _, _, _, notEmpty =>
      simp [decompose, notEmpty label _ rfl]
  | .collection .hashBag elements none, _, _, notBag, _ => exact absurd rfl (notBag elements)
  | .bvar _, _, _, _, _ => simp [decompose]
  | .fvar _, _, _, _, _ => simp [decompose]
  | .apply _ (_ :: _ :: _), _, _, _, _ => simp [decompose]
  | .lambda _ _, _, _, _, _ => simp [decompose]
  | .multiLambda _ _ _, _, _, _, _ => simp [decompose]
  | .subst _ _, _, _, _, _ => simp [decompose]
  | .collection .hashBag _ (some _), _, _, _, _ => simp [decompose]
  | .collection .hashSet _ _, _, _, _, _ => simp [decompose]
  | .collection .vec _ _, _, _, _, _ => simp [decompose]

open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (PatternLe serList)

/-- Sort components by the lexicographic order of their serializations, by insertion, so that the kernel computes it
in time linear in their size. -/
def sortComponents (components : List Pattern) : List Pattern :=
  components.insertionSort PatternLe

/-- A list with one element put in every place. -/
def insertions {α : Type} (element : α) : List α → List (List α)
  | [] => [[element]]
  | first :: rest => (element :: first :: rest) :: (insertions element rest).map (first :: ·)

/-- All orders of a list, by structural recursion, so that the kernel computes them. -/
def orders {α : Type} : List α → List (List α)
  | [] => [[]]
  | first :: rest => (orders rest).flatMap (insertions first)

/-- The least of a list of component lists, compared by their serializations. -/
def least : List (List Pattern) → List Pattern
  | [] => []
  | first :: rest => rest.foldl (fun best next => if serList next < serList best then next else best) first

/-- A constructor argument with canonical parts: the body of an abstraction, or the argument itself; variables
and explicit substitutions stay as they are. -/
def canonArgument (canonical : Pattern → Pattern) : Pattern → Pattern
  | .lambda binder body => .lambda binder (canonical body)
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .subst body replacement => .subst body replacement
  | argument => canonical argument

/-- **A multiset read back from a block**: the components, when there are no restrictions; otherwise the block as
the one member. -/
def multisetOf (block : Block) (form : Prenex) : Pattern :=
  if form.count = 0 then .collection .hashBag form.components none
  else .collection .hashBag [Prenex.toPattern block form] none

mutual
  /-- **The canonical form**, computed within a fuel: the block, its restrictions in the order that makes the sorted
  canonical components least, and canonical parts inside every component. -/
  def canonWith (block : Block) : Nat → Pattern → Pattern
    | 0, process => process
    | fuel + 1, process =>
        let form := decompose block process
        let candidates := (orders (List.range form.count)).map fun order =>
          sortComponents (form.components.map fun component =>
            canonComponentWith block fuel (rename (Prenex.permute form.count order) component))
        Prenex.toPattern block ⟨form.count, least candidates⟩

  /-- **The canonical argument of a named multiset**, computed within a fuel: the same reading as the canonical
  form's, read back as a multiset, so that a bag of members of another sort keeps its members. An open collection
  keeps its members' order and its rest; an explicit substitution stays as it is. -/
  def canonMultisetWith (block : Block) : Nat → Pattern → Pattern
    | 0, argument => argument
    | fuel + 1, .collection kind elements (some rest) =>
        .collection kind (elements.map (canonWith block fuel)) (some rest)
    | _ + 1, .subst body replacement => .subst body replacement
    | fuel + 1, argument =>
        let form := decompose block argument
        let candidates := (orders (List.range form.count)).map fun order =>
          sortComponents (form.components.map fun component =>
            canonComponentWith block fuel (rename (Prenex.permute form.count order) component))
        multisetOf block ⟨form.count, least candidates⟩

  /-- A component with canonical parts, at every node but explicit substitutions: the arguments of a constructor,
  the body of a binder, the members of a collection. The arguments of a named multiset are canonical multisets. -/
  def canonComponentWith (block : Block) : Nat → Pattern → Pattern
    | 0, component => component
    | fuel + 1, .apply constructor arguments =>
        if constructor ∈ block.multisets then .apply constructor (arguments.map (canonMultisetWith block fuel))
        else .apply constructor (arguments.map (canonArgument (canonWith block fuel)))
    | fuel + 1, .lambda binder body => .lambda binder (canonWith block fuel body)
    | fuel + 1, .multiLambda arity binders body => .multiLambda arity binders (canonWith block fuel body)
    | fuel + 1, .collection kind elements rest => .collection kind (elements.map (canonWith block fuel)) rest
    | _ + 1, component => component
end

mutual
  /-- The number of nodes of a pattern. -/
  def size : Pattern → Nat
    | .bvar _ => 1
    | .fvar _ => 1
    | .apply _ arguments => sizeList arguments + 1
    | .lambda _ body => size body + 1
    | .multiLambda _ _ body => size body + 1
    | .subst body replacement => size body + size replacement + 1
    | .collection _ elements _ => sizeList elements + 1

  def sizeList : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => size pattern + sizeList patterns
end

/-- **The canonical form of a process.** -/
def canon (block : Block) (process : Pattern) : Pattern := canonWith block (2 * size process + 2) process

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
