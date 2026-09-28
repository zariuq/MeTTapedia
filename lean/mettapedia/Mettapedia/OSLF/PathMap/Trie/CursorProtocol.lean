import Mettapedia.OSLF.PathMap.Trie.HuetZipper
import Mettapedia.Machines.Cursor.Transfer

/-!
# Trie navigation as a cursor protocol

The same protocol supports a subtree representation and the existing Huet
zipper. A `peek` request returns an optional value; a `down` request returns
whether the edge exists and moves only on success. Missing edges and nodes
with no value remain distinct. The subtree implementation searches directly;
the zipper implementation retains its existing parent contexts.

The local refinement implies agreement for every adaptive bounded client.
This adapter covers read/down capabilities, not writes or ascent. It connects
the finite PathMap model to the cursor algebra, not the Rust implementation
or its ownership and allocation costs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.PathMap.Trie.CursorProtocol

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor

inductive Request where
  | peek
  | down (byte : UInt8)

def protocol (Value : Type) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request
  Position request := match request with
    | .peek => Option Value
    | .down _ => Bool
  next _ _ := ()

variable {Value : Type}

/-- A direct search without constructing parent contexts. -/
def findChild (byte : UInt8) : List (UInt8 × FTrie Value) → Option (FTrie Value)
  | [] => none
  | (key, child) :: rest =>
      if key == byte then some child else findChild byte rest

theorem findChild_split (byte : UInt8) (children : List (UInt8 × FTrie Value)) :
    findChild byte children = (splitAtByte byte children).map (fun found => found.2.1) := by
  induction children with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, child⟩
      by_cases equal : (key == byte) = true
      · simp [findChild, splitAtByte, equal]
      · simp only [findChild, splitAtByte, equal]
        rw [ih]
        cases splitAtByte byte rest <;> rfl

def descend (tree : FTrie Value) (byte : UInt8) : Option (FTrie Value) :=
  match tree with
  | .empty => none
  | .node _ children => findChild byte children

theorem descend_focus (zipper : HuetTrieZipper Value) (byte : UInt8) :
    (zipper.descendByte byte).map HuetTrieZipper.focus = descend zipper.focus byte := by
  rcases zipper with ⟨tree, crumbs⟩
  cases tree with
  | empty => rfl
  | node value children =>
      simp only [HuetTrieZipper.descendByte, descend, findChild_split]
      cases splitAtByte byte children <;> rfl

def subtrees (Value : Type) : Provider (protocol Value) where
  State _ _ := FTrie Value
  step tree request := match request with
    | .peek => ⟨tree.lookup [], tree⟩
    | .down byte => match descend tree byte with
      | none => ⟨false, tree⟩
      | some child => ⟨true, child⟩

def zippers (Value : Type) : Provider (protocol Value) where
  State _ _ := HuetTrieZipper Value
  step zipper request := match request with
    | .peek => ⟨zipper.focus.lookup [], zipper⟩
    | .down byte => match zipper.descendByte byte with
      | none => ⟨false, zipper⟩
      | some child => ⟨true, child⟩

def focusHom (Value : Type) : Hom (zippers Value) (subtrees Value) where
  map := HuetTrieZipper.focus
  step zipper request := by
    cases request with
    | peek => rfl
    | down byte =>
        have law := descend_focus zipper byte
        cases found : zipper.descendByte byte with
        | none =>
            simp only [found, Option.map_none] at law
            simp [zippers, subtrees, found, ← law]
        | some child =>
            simp only [found, Option.map_some] at law
            simp [zippers, subtrees, found, ← law]

/-- A repeated, reply-dependent navigation client observes the same replies
and current subtree through either representation. -/
theorem zipper_advance {Return : Unit → Unit → Type}
    (C : Client (P := protocol Value) (Return := Return))
    (zipperCost : Charge (zippers Value)) (subtreeCost : Charge (subtrees Value))
    (budget : Nat) (packet : Packet (zippers Value) C ()) :
    (focusHom Value).outcome C (advance _ C zipperCost budget packet).2 =
      (advance (subtrees Value) C subtreeCost budget ((focusHom Value).packet C packet)).2 :=
  Hom.advance C (focusHom Value) zipperCost subtreeCost budget packet

example : (subtrees Nat).step (base := ()) (index := ())
    (.node none [(7, .node (some 42) [])]) (.down 7) =
    ⟨true, .node (some 42) []⟩ := rfl

example : (subtrees Nat).step (base := ()) (index := ())
    (.node none [(7, .empty)]) (.down 7) =
    ⟨true, .empty⟩ := rfl

example : (subtrees Nat).step (base := ()) (index := ())
    (.node none [(7, .empty)]) (.down 8) =
    ⟨false, .node none [(7, .empty)]⟩ := rfl

end Mettapedia.OSLF.PathMap.Trie.CursorProtocol
