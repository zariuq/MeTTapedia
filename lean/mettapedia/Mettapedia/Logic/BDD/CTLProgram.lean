import Mettapedia.Logic.BDD.NestedCTL
import Mettapedia.Logic.BDD.Canonical

/-!
# Shared topological CTL programs

Instructions name previously produced formula results. The reference decoder
unfolds those references into formulas; the worker uses cached diagrams and
executes each instruction once. Missing references and repeated destinations
refuse the plan, rather than becoming false or choosing an overwrite policy.

The operation count here is the number of instruction visits, not constant
time per BDD operation or associative-list lookup. Source function effects,
round counters, native hash tables and physical lifetimes require adapters.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.CTLProgram

open StatePredicates StateTransducer CTLFormula

inductive Node (Label : Type)
  | atom (label : Label)
  | truth
  | neg (body : String)
  | conj (left right : String)
  | disj (left right : String)
  | ex (body : String)
  | eu (holds goal : String)
  | eg (body : String)
  deriving DecidableEq, Repr

structure Instruction (Label : Type) where
  destination : String
  node : Node Label
  deriving DecidableEq, Repr

abbrev Table (Value : Type) := List (String × Value)

def lookup {Value : Type} (name : String) : Table Value → Option Value
  | [] => none
  | (key, value) :: rest => if key = name then some value else lookup name rest

def mapTable {A B : Type} (f : A → B) (table : Table A) : Table B :=
  table.map fun entry => (entry.1, f entry.2)

theorem lookup_map {A B : Type} (f : A → B) (name : String) (table : Table A) :
    lookup name (mapTable f table) = (lookup name table).map f := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      change (if key = name then some (f value) else lookup name (mapTable f rest)) =
        (if key = name then some value else lookup name rest).map f
      split_ifs <;> simp_all

def decodeNode {Label : Type} (table : Table (Formula Label)) : Node Label → Option (Formula Label)
  | .atom label => some (.atom label)
  | .truth => some .truth
  | .neg body => .neg <$> lookup body table
  | .conj left right => return .conj (← lookup left table) (← lookup right table)
  | .disj left right => return .disj (← lookup left table) (← lookup right table)
  | .ex body => .ex <$> lookup body table
  | .eu holds goal => return .eu (← lookup holds table) (← lookup goal table)
  | .eg body => .eg <$> lookup body table

def evalNode {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n) (table : Table (Diagram n)) :
    Node Label → Option (Diagram n)
  | .atom label => some (within domain (atoms label))
  | .truth => some domain
  | .neg body => complement domain <$> lookup body table
  | .conj left right => return StatePredicates.conj (← lookup left table) (← lookup right table)
  | .disj left right => return StatePredicates.disj (← lookup left table) (← lookup right table)
  | .ex body => pre domain program.rules <$> lookup body table
  | .eu holds goal => do
      let held ← lookup holds table
      let reached ← lookup goal table
      return BoundedFixedPoints.least (SymbolicCTL.untilOp program held reached)
  | .eg body => return BoundedFixedPoints.greatest (SymbolicCTL.globallyOp program (← lookup body table))

theorem node_refines {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (table : Table (Formula Label)) (node : Node Label) :
    evalNode program atoms (mapTable (NestedCTL.compile program atoms) table) node =
      (decodeNode table node).map (NestedCTL.compile program atoms) := by
  cases node with
  | atom label | truth => rfl
  | neg body | ex body | eg body =>
      cases value : lookup body table <;>
        simp [evalNode, decodeNode, lookup_map, value, NestedCTL.compile]
  | conj left right | disj left right | eu left right =>
      cases first : lookup left table <;> cases second : lookup right table <;>
        simp [evalNode, decodeNode, lookup_map, first, second, NestedCTL.compile]

def decodeFrom {Label : Type} : List (Instruction Label) → Table (Formula Label) → Option (Table (Formula Label))
  | [], table => some table
  | instruction :: rest, table => do
      if (lookup instruction.destination table).isSome then none else
        let formula ← decodeNode table instruction.node
        decodeFrom rest ((instruction.destination, formula) :: table)

def executeFrom {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n) :
    List (Instruction Label) → Table (Diagram n) → Option (Table (Diagram n))
  | [], table => some table
  | instruction :: rest, table => do
      if (lookup instruction.destination table).isSome then none else
        let result ← evalNode program atoms table instruction.node
        executeFrom program atoms rest ((instruction.destination, result) :: table)

theorem program_refines {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (instructions : List (Instruction Label)) (table : Table (Formula Label)) :
    executeFrom program atoms instructions (mapTable (NestedCTL.compile program atoms) table) =
      (decodeFrom instructions table).map (mapTable (NestedCTL.compile program atoms)) := by
  induction instructions generalizing table with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [executeFrom, decodeFrom, lookup_map, Option.isSome_map]
      split
      · rfl
      · rw [node_refines]
        cases decoded : decodeNode table instruction.node with
        | none => simp
        | some formula =>
            simpa [mapTable] using ih ((instruction.destination, formula) :: table)

def root {Label : Type} {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (atoms : Label → Diagram n) (instructions : List (Instruction Label)) (name : String) : Option (Diagram n) :=
  (executeFrom program atoms instructions []).bind (lookup name)

theorem root_refines {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n) (instructions : List (Instruction Label)) (name : String) :
    root program atoms instructions name =
      ((decodeFrom instructions []).bind (lookup name)).map (NestedCTL.compile program atoms) := by
  unfold root
  rw [show ([] : Table (Diagram n)) = mapTable (NestedCTL.compile program atoms) [] from rfl, program_refines]
  cases decoded : decodeFrom instructions [] with
  | none => simp
  | some table => simp [lookup_map]

theorem root_path_exact {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n) (instructions : List (Instruction Label))
    (name : String) (formula : Formula Label)
    (decoded : ((decodeFrom instructions []).bind (lookup name)) = some formula) :
    (root program atoms instructions name).map denote =
      some (meaning (denote domain) (Relation domain program.rules) (fun label => denote (atoms label)) formula) := by
  rw [root_refines, decoded]
  simp [NestedCTL.compile_exact]

theorem executeFrom_append {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (first later : List (Instruction Label)) (table : Table (Diagram n)) :
    executeFrom program atoms (first ++ later) table =
      (executeFrom program atoms first table).bind (executeFrom program atoms later) := by
  induction first generalizing table with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, executeFrom]
      split
      · rfl
      · cases computed : evalNode program atoms table instruction.node <;> simp [ih]

theorem old_binding_retained {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (instructions : List (Instruction Label)) (before after : Table (Diagram n))
    (executed : executeFrom program atoms instructions before = some after)
    (name : String) (value : Diagram n) (present : lookup name before = some value) :
    lookup name after = some value := by
  induction instructions generalizing before with
  | nil => cases executed; exact present
  | cons instruction rest ih =>
      simp only [executeFrom] at executed
      split at executed
      · cases executed
      next fresh =>
        have distinct : instruction.destination ≠ name := by
          intro same
          simp [same, present] at fresh
        cases computed : evalNode program atoms before instruction.node with
        | none => simp [computed] at executed
        | some result =>
            apply ih ((instruction.destination, result) :: before)
              (by simpa [computed] using executed)
            simp [lookup, distinct, present]

def executeCounted {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n) :
    List (Instruction Label) → Table (Diagram n) → Nat × Option (Table (Diagram n))
  | [], table => (0, some table)
  | instruction :: rest, table =>
      if (lookup instruction.destination table).isSome then (1, none) else
        match evalNode program atoms table instruction.node with
        | none => (1, none)
        | some result =>
            let later := executeCounted program atoms rest ((instruction.destination, result) :: table)
            (later.1 + 1, later.2)

theorem counted_erases {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (instructions : List (Instruction Label)) (table : Table (Diagram n)) :
    (executeCounted program atoms instructions table).2 = executeFrom program atoms instructions table := by
  induction instructions generalizing table with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [executeCounted, executeFrom]
      split
      · rfl
      · cases evalNode program atoms table instruction.node <;> simp [ih]

theorem successful_visits {Label : Type} {n : Nat} {domain : Diagram n}
    (program : Certified n domain) (atoms : Label → Diagram n)
    (instructions : List (Instruction Label)) (table result : Table (Diagram n))
    (completed : executeFrom program atoms instructions table = some result) :
    (executeCounted program atoms instructions table).1 = instructions.length := by
  induction instructions generalizing table with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [executeFrom] at completed
      rw [executeCounted]
      split at completed
      · cases completed
      next fresh =>
        rw [if_neg fresh]
        cases computed : evalNode program atoms table instruction.node with
        | none => simp [computed] at completed
        | some value =>
            simp only [ih _ (by simpa [computed] using completed), List.length_cons]

end Mettapedia.Logic.BDDCore.CTLProgram
