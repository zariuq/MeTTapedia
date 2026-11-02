import Mettapedia.Logic.HOL.ConstructorPositionPrograms

/-!
# Finite constructor-program rows

The table stores each ordered field telescope, its guard, its result-index
program and its child-position graph as syntax. Tabulation evaluates every
original constructor occurrence. Reconstruction provides the existing
function-field interfaces without retaining their source semantic registry.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards

open FiniteConstructorEncoding CurriedPredicates
universe u v

inductive ProgramRows {Base : Type u} (Const : Ty Base → Type v) (Γ : Ctx Base)
    (number index : Ty Base) : List (List (Ty Base)) → Type (max u v) where
  | nil : ProgramRows Const Γ number index []
  | cons (arity : List (Ty Base)) {rest : List (List (Ty Base))}
      (allowed : Term Const Γ (handlerType arity))
      (result : Term Const Γ (FunctionType arity index))
      (graph : Term Const Γ (number ⇒ index ⇒ handlerType arity))
      (tail : ProgramRows Const Γ number index rest) :
      ProgramRows Const Γ number index (arity :: rest)

namespace ProgramRows

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {number index : Ty Base}

def ofFunctions : (fields : List (List (Ty Base))) →
    ((occurrence : Fin fields.length) → Term Const Γ (handlerType (fields.get occurrence))) →
    ((occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index)) →
    ((occurrence : Fin fields.length) → Term Const Γ (number ⇒ index ⇒ handlerType (fields.get occurrence))) →
    ProgramRows Const Γ number index fields
  | [], _, _, _ => .nil
  | arity :: rest, allowed, result, graph =>
      .cons arity (allowed ⟨0, by simp⟩) (result ⟨0, by simp⟩) (graph ⟨0, by simp⟩)
        (ofFunctions rest (fun i => allowed i.succ) (fun i => result i.succ) (fun i => graph i.succ))

def allowed : {fields : List (List (Ty Base))} → ProgramRows Const Γ number index fields →
    (occurrence : Fin fields.length) → Term Const Γ (handlerType (fields.get occurrence))
  | [], .nil, occurrence => Fin.elim0 occurrence
  | _ :: _, .cons _ first _ _ rest, occurrence => Fin.cases first (fun i => allowed rest i) occurrence

def result : {fields : List (List (Ty Base))} → ProgramRows Const Γ number index fields →
    (occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index)
  | [], .nil, occurrence => Fin.elim0 occurrence
  | _ :: _, .cons _ _ first _ rest, occurrence => Fin.cases first (fun i => result rest i) occurrence

def graph : {fields : List (List (Ty Base))} → ProgramRows Const Γ number index fields →
    (occurrence : Fin fields.length) → Term Const Γ (number ⇒ index ⇒ handlerType (fields.get occurrence))
  | [], .nil, occurrence => Fin.elim0 occurrence
  | _ :: _, .cons _ _ _ first rest, occurrence => Fin.cases first (fun i => graph rest i) occurrence

theorem allowed_ofFunctions : ∀ (fields : List (List (Ty Base)))
    (guards : (occurrence : Fin fields.length) → Term Const Γ (handlerType (fields.get occurrence)))
    (results : (occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index))
    (graphs : (occurrence : Fin fields.length) → Term Const Γ (number ⇒ index ⇒ handlerType (fields.get occurrence)))
    (occurrence : Fin fields.length),
    (ofFunctions fields guards results graphs).allowed occurrence = guards occurrence := by
  intro fields
  induction fields with
  | nil => intro guards results graphs occurrence; exact Fin.elim0 occurrence
  | cons arity rest ih =>
      intro guards results graphs occurrence
      refine Fin.cases ?_ (fun i => ?_) occurrence
      · rfl
      · exact ih _ _ _ i

theorem result_ofFunctions : ∀ (fields : List (List (Ty Base)))
    (guards : (occurrence : Fin fields.length) → Term Const Γ (handlerType (fields.get occurrence)))
    (results : (occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index))
    (graphs : (occurrence : Fin fields.length) → Term Const Γ (number ⇒ index ⇒ handlerType (fields.get occurrence)))
    (occurrence : Fin fields.length),
    (ofFunctions fields guards results graphs).result occurrence = results occurrence := by
  intro fields
  induction fields with
  | nil => intro guards results graphs occurrence; exact Fin.elim0 occurrence
  | cons arity rest ih =>
      intro guards results graphs occurrence
      refine Fin.cases ?_ (fun i => ?_) occurrence
      · rfl
      · exact ih _ _ _ i

theorem graph_ofFunctions : ∀ (fields : List (List (Ty Base)))
    (guards : (occurrence : Fin fields.length) → Term Const Γ (handlerType (fields.get occurrence)))
    (results : (occurrence : Fin fields.length) → Term Const Γ (FunctionType (fields.get occurrence) index))
    (graphs : (occurrence : Fin fields.length) → Term Const Γ (number ⇒ index ⇒ handlerType (fields.get occurrence)))
    (occurrence : Fin fields.length),
    (ofFunctions fields guards results graphs).graph occurrence = graphs occurrence := by
  intro fields
  induction fields with
  | nil => intro guards results graphs occurrence; exact Fin.elim0 occurrence
  | cons arity rest ih =>
      intro guards results graphs occurrence
      refine Fin.cases ?_ (fun i => ?_) occurrence
      · rfl
      · exact ih _ _ _ i

def constructors {fields : List (List (Ty Base))} (rows : ProgramRows Const Γ number index fields)
    (numeral : Nat → Term Const Γ number) : ConstructorPrograms Const Γ where
  fields := fields
  number := number
  index := index
  numeral := numeral
  allowed := rows.allowed
  result := rows.result

theorem ofFunctions_recovered {fields : List (List (Ty Base))}
    (data : ProgramRows Const Γ number index fields) :
    ofFunctions fields data.allowed data.result data.graph = data := by
  induction data with
  | nil => rfl
  | cons arity allowed result graph tail ih =>
      change ProgramRows.cons arity allowed result graph
        (ofFunctions _ tail.allowed tail.result tail.graph) =
        ProgramRows.cons arity allowed result graph tail
      exact congrArg (fun rest => ProgramRows.cons arity allowed result graph rest) ih

def positions {fields : List (List (Ty Base))} (rows : ProgramRows Const Γ number index fields)
    (numeral : Nat → Term Const Γ number) : PositionPrograms (rows.constructors numeral) where
  graph := rows.graph

def ofPrograms (inventory : ConstructorPrograms Const Γ) (positions : PositionPrograms inventory) :
    ProgramRows Const Γ inventory.number inventory.index inventory.fields :=
  ofFunctions inventory.fields inventory.allowed inventory.result positions.graph

theorem ofPrograms_constructed {fields : List (List (Ty Base))}
    (data : ProgramRows Const Γ number index fields) (numeral : Nat → Term Const Γ number) :
    ofPrograms (data.constructors numeral) (data.positions numeral) = data :=
  ofFunctions_recovered data

theorem constructors_ofPrograms (inventory : ConstructorPrograms Const Γ) (positions : PositionPrograms inventory) :
    (ofPrograms inventory positions).constructors inventory.numeral = inventory := by
  cases inventory with
  | mk fields number index numeral guards results =>
      have allowedSame : (ofFunctions fields guards results positions.graph).allowed = guards :=
        funext (allowed_ofFunctions fields guards results positions.graph)
      have resultSame : (ofFunctions fields guards results positions.graph).result = results :=
        funext (result_ofFunctions fields guards results positions.graph)
      simp only [ofPrograms, constructors, allowedSame, resultSame]

private theorem positions_ext_heq {first second : ConstructorPrograms Const Γ}
    (same : first = second) (a : PositionPrograms first) (b : PositionPrograms second)
    (graphs : HEq a.graph b.graph) : HEq a b := by
  cases same
  cases a
  cases b
  cases graphs
  rfl

theorem positions_ofPrograms (inventory : ConstructorPrograms Const Γ) (positions : PositionPrograms inventory) :
    HEq ((ofPrograms inventory positions).positions inventory.numeral) positions := by
  apply positions_ext_heq (constructors_ofPrograms inventory positions)
  exact heq_of_eq (funext (graph_ofFunctions inventory.fields inventory.allowed inventory.result positions.graph))

#print axioms allowed_ofFunctions
#print axioms ofPrograms_constructed
#print axioms constructors_ofPrograms
#print axioms positions_ofPrograms

end ProgramRows
end Mettapedia.Logic.HOL.IndexedConstructorGuards
