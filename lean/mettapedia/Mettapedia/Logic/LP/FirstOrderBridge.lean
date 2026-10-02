import Mettapedia.Logic.LP.Semantics
import Mathlib.ModelTheory.Semantics

/-!
# Logic-programming syntax as a first-order language

The translation retains a constant and a nullary function as different symbols.
It preserves each function and predicate arity, substitution, and the existing
Herbrand grounding semantics. Terms are translated structurally in both
directions; no quotient or binding convention is introduced.
-/

namespace Mettapedia.Logic.LP.FirstOrderBridge

variable {σ : LPSignature}

/-- Constants and functions occupy separate tags, including at arity zero. -/
inductive FunctionSymbol (σ : LPSignature) : Nat → Type _ where
  | constant (symbol : σ.constants) : FunctionSymbol σ 0
  | function (symbol : σ.functionSymbols) : FunctionSymbol σ (σ.functionArity symbol)

/-- A predicate keeps its authored arity. -/
inductive RelationSymbol (σ : LPSignature) : Nat → Type _ where
  | relation (symbol : σ.relationSymbols) : RelationSymbol σ (σ.relationArity symbol)

def language (σ : LPSignature) : FirstOrder.Language where
  Functions := FunctionSymbol σ
  Relations := RelationSymbol σ

/-- Structural translation into mathlib's first-order terms. -/
def encodeTerm : Term σ → (language σ).Term σ.vars
  | .var name => .var name
  | .const symbol => .func (.constant symbol) Fin.elim0
  | .app symbol arguments =>
    .func (.function symbol) (fun position => encodeTerm (arguments position))

private def decodeFunction : {arity : Nat} → FunctionSymbol σ arity →
    (Fin arity → Term σ) → Term σ
  | _, .constant symbol, _ => .const symbol
  | _, .function symbol, arguments => .app symbol arguments

/-- Structural translation back; all first-order symbols are authored LP symbols. -/
def decodeTerm : (language σ).Term σ.vars → Term σ
  | .var name => .var name
  | .func symbol arguments =>
    decodeFunction symbol (fun position => decodeTerm (arguments position))

@[simp] theorem decodeTerm_var (name : σ.vars) :
    decodeTerm (FirstOrder.Language.Term.var name) = (Term.var name : Term σ) := rfl

@[simp] theorem decodeTerm_constant (symbol : σ.constants)
    (arguments : Fin 0 → (language σ).Term σ.vars) :
    decodeTerm (FirstOrder.Language.Term.func (FunctionSymbol.constant symbol) arguments) =
      Term.const symbol := rfl

@[simp] theorem decodeTerm_function (symbol : σ.functionSymbols)
    (arguments : Fin (σ.functionArity symbol) → (language σ).Term σ.vars) :
    decodeTerm (FirstOrder.Language.Term.func (FunctionSymbol.function symbol) arguments) =
      Term.app symbol (fun position => decodeTerm (arguments position)) := rfl

@[simp] theorem decodeTerm_encodeTerm (term : Term σ) :
    decodeTerm (encodeTerm term) = term := by
  induction term with
  | var => rfl
  | const => rfl
  | app symbol arguments ih => simp only [encodeTerm, decodeTerm, decodeFunction, ih]

@[simp] theorem encodeTerm_decodeTerm (term : (language σ).Term σ.vars) :
    encodeTerm (decodeTerm term) = term := by
  induction term with
  | var => rfl
  | func symbol arguments ih =>
    cases symbol with
    | constant symbol =>
      simp only [decodeTerm, decodeFunction, encodeTerm]
      congr 1
      funext position
      exact Fin.elim0 position
    | function symbol => simp only [decodeTerm, decodeFunction, encodeTerm, ih]

def termEquiv : Term σ ≃ (language σ).Term σ.vars where
  toFun := encodeTerm
  invFun := decodeTerm
  left_inv := decodeTerm_encodeTerm
  right_inv := encodeTerm_decodeTerm

theorem encodeTerm_injective : Function.Injective (encodeTerm (σ := σ)) :=
  termEquiv.injective

@[simp] theorem encodeTerm_applyTerm (substitution : Subst σ) (term : Term σ) :
    encodeTerm (substitution.applyTerm term) =
      (encodeTerm term).subst (fun name => encodeTerm (substitution name)) := by
  induction term with
  | var => rfl
  | const =>
    simp only [Subst.applyTerm, encodeTerm, FirstOrder.Language.Term.subst]
    congr 1
    funext position
    exact Fin.elim0 position
  | app symbol arguments ih =>
    simp only [Subst.applyTerm, encodeTerm, FirstOrder.Language.Term.subst, ih]

@[simp] theorem decodeTerm_subst (substitution : σ.vars → (language σ).Term σ.vars)
    (term : (language σ).Term σ.vars) :
    decodeTerm (term.subst substitution) =
      Subst.applyTerm (fun name => decodeTerm (substitution name)) (decodeTerm term) := by
  induction term with
  | var => rfl
  | func symbol arguments ih =>
    cases symbol with
    | constant => rfl
    | function =>
      simp only [FirstOrder.Language.Term.subst, decodeTerm, decodeFunction, Subst.applyTerm, ih]

theorem encodeSubst_comp (later earlier : Subst σ) (name : σ.vars) :
    encodeTerm ((later ∘ₛ earlier) name) =
      (encodeTerm (earlier name)).subst (fun name => encodeTerm (later name)) :=
  encodeTerm_applyTerm later (earlier name)

variable {Model : Type*} [(language σ).Structure Model]

/-- Evaluation directly on LP syntax, using the structure's tagged symbols. -/
def realizeTerm (assignment : σ.vars → Model) : Term σ → Model
  | .var name => assignment name
  | .const symbol => FirstOrder.Language.Structure.funMap (L := language σ) (.constant symbol) Fin.elim0
  | .app symbol arguments =>
    FirstOrder.Language.Structure.funMap (L := language σ) (.function symbol)
      (fun position => realizeTerm assignment (arguments position))

@[simp] theorem encodeTerm_realize (assignment : σ.vars → Model) (term : Term σ) :
    (encodeTerm term).realize assignment = realizeTerm assignment term := by
  induction term with
  | var => rfl
  | const symbol =>
    change FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.constant symbol)
      (fun position => (Fin.elim0 position : (language σ).Term σ.vars).realize assignment) =
      FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.constant symbol) Fin.elim0
    congr 1
    funext position
    exact Fin.elim0 position
  | app symbol arguments ih =>
    change FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.function symbol)
      (fun position => (encodeTerm (arguments position)).realize assignment) =
      FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.function symbol)
        (fun position => realizeTerm assignment (arguments position))
    exact congrArg (FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.function symbol)) (funext ih)

theorem realizeTerm_applyTerm (assignment : σ.vars → Model)
    (substitution : Subst σ) (term : Term σ) :
    realizeTerm assignment (substitution.applyTerm term) =
      realizeTerm (fun name => realizeTerm assignment (substitution name)) term := by
  rw [← encodeTerm_realize, encodeTerm_applyTerm, FirstOrder.Language.Term.realize_subst]
  simp only [encodeTerm_realize]

/-- Predicate evaluation on LP atoms, without changing argument positions. -/
def realizeAtom (assignment : σ.vars → Model) (atom : Atom σ) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := language σ) (.relation atom.symbol)
    (fun position => realizeTerm assignment (atom.args position))

def encodeAtom (atom : Atom σ) : (language σ).Formula σ.vars :=
  FirstOrder.Language.Relations.formula (.relation atom.symbol)
    (fun position => encodeTerm (atom.args position))

@[simp] theorem encodeAtom_realize (assignment : σ.vars → Model) (atom : Atom σ) :
    (encodeAtom atom).Realize assignment ↔ realizeAtom assignment atom := by
  exact (FirstOrder.Language.Formula.realize_rel (L := language σ) (M := Model)
    (R := RelationSymbol.relation atom.symbol)
    (ts := fun position => encodeTerm (atom.args position)) (v := assignment)).trans
      (by simp only [encodeTerm_realize, realizeAtom])

theorem realizeAtom_applyAtom (assignment : σ.vars → Model)
    (substitution : Subst σ) (atom : Atom σ) :
    realizeAtom assignment (substitution.applyAtom atom) ↔
      realizeAtom (fun name => realizeTerm assignment (substitution name)) atom := by
  simp only [realizeAtom, Subst.applyAtom, realizeTerm_applyTerm]

def encodeBody : List (Atom σ) → (language σ).Formula σ.vars
  | [] => ⊤
  | atom :: rest => encodeAtom atom ⊓ encodeBody rest

theorem encodeBody_realize (assignment : σ.vars → Model) (body : List (Atom σ)) :
    (encodeBody body).Realize assignment ↔ ∀ atom ∈ body, realizeAtom assignment atom := by
  induction body with
  | nil => simp only [encodeBody, FirstOrder.Language.Formula.realize_top, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | cons atom rest ih =>
    change (encodeAtom atom ⊓ encodeBody rest).Realize assignment ↔ _
    rw [FirstOrder.Language.Formula.realize_inf, encodeAtom_realize, ih]
    constructor
    · rintro ⟨first, later⟩ a member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact later a member
    · intro valid
      exact ⟨valid atom List.mem_cons_self,
        fun a member => valid a (List.mem_cons_of_mem _ member)⟩

/-- The clause remains an implication from its complete ordered body. Truth
does not retain a derivation's proof occurrences or search order. -/
def encodeClause (clause : Clause σ) : (language σ).Formula σ.vars :=
  (encodeBody clause.body).imp (encodeAtom clause.head)

theorem encodeClause_realize (assignment : σ.vars → Model) (clause : Clause σ) :
    (encodeClause clause).Realize assignment ↔
      (∀ atom ∈ clause.body, realizeAtom assignment atom) → realizeAtom assignment clause.head := by
  exact (FirstOrder.Language.Formula.realize_imp (L := language σ) (M := Model)
    (φ := encodeBody clause.body) (ψ := encodeAtom clause.head) (v := assignment)).trans
      (imp_congr (encodeBody_realize assignment clause.body) (encodeAtom_realize assignment clause.head))

/-- The structure underlying the existing Herbrand interpretation: functions
build ground terms and relations test membership in the authored atom set. -/
@[instance_reducible] def herbrandStructure (interpretation : Interpretation σ) :
    (language σ).Structure (GroundTerm σ) where
  funMap
    | .constant symbol, _ => .const symbol
    | .function symbol, arguments => .app symbol arguments
  RelMap
    | .relation symbol, arguments => (⟨symbol, arguments⟩ : GroundAtom σ) ∈ interpretation

theorem realizeTerm_herbrand (interpretation : Interpretation σ)
    (grounding : Grounding σ) (term : Term σ) :
    @realizeTerm σ (GroundTerm σ) (herbrandStructure interpretation) grounding term =
      grounding.groundTerm term := by
  let _ := herbrandStructure interpretation
  induction term with
  | var => rfl
  | const => rfl
  | app symbol arguments ih =>
    change GroundTerm.app symbol (fun position => realizeTerm grounding (arguments position)) = _
    simp only [Grounding.groundTerm, ih]

theorem encodeTerm_realize_herbrand (interpretation : Interpretation σ)
    (grounding : Grounding σ) (term : Term σ) :
    let := herbrandStructure interpretation
    (encodeTerm term).realize grounding = grounding.groundTerm term := by
  let := herbrandStructure interpretation
  exact (encodeTerm_realize grounding term).trans (realizeTerm_herbrand _ _ _)

theorem encodeAtom_realize_herbrand (interpretation : Interpretation σ)
    (grounding : Grounding σ) (atom : Atom σ) :
    let := herbrandStructure interpretation
    (encodeAtom atom).Realize grounding ↔ grounding.groundAtom atom ∈ interpretation := by
  dsimp only
  change σ.vars → GroundTerm σ at grounding
  let _ := herbrandStructure interpretation
  refine (encodeAtom_realize grounding atom).trans ?_
  change (⟨atom.symbol, fun position => realizeTerm grounding (atom.args position)⟩ : GroundAtom σ)
      ∈ interpretation ↔ _
  have arguments : (fun position => realizeTerm grounding (atom.args position)) =
      (fun position => Grounding.groundTerm grounding (atom.args position)) :=
    funext fun position => realizeTerm_herbrand interpretation grounding (atom.args position)
  rw [arguments]
  rfl

theorem realizeAtom_herbrand (interpretation : Interpretation σ)
    (grounding : Grounding σ) (atom : Atom σ) :
    @realizeAtom σ (GroundTerm σ) (herbrandStructure interpretation) grounding atom ↔
      grounding.groundAtom atom ∈ interpretation := by
  let _ := herbrandStructure interpretation
  exact (encodeAtom_realize grounding atom).symm.trans
    (encodeAtom_realize_herbrand interpretation grounding atom)

theorem encodeClause_realize_herbrand (interpretation : Interpretation σ)
    (grounding : Grounding σ) (clause : Clause σ) :
    let := herbrandStructure interpretation
    (encodeClause clause).Realize grounding ↔
      (∀ atom ∈ clause.body, grounding.groundAtom atom ∈ interpretation) →
        grounding.groundAtom clause.head ∈ interpretation := by
  dsimp only
  let _ := herbrandStructure interpretation
  refine (encodeClause_realize grounding clause).trans ?_
  exact imp_congr (forall_congr' fun atom => forall_congr' fun _ =>
    realizeAtom_herbrand interpretation grounding atom)
      (realizeAtom_herbrand interpretation grounding clause.head)

/-- The original immediate-consequence model condition is precisely the
first-order truth of all grounded clauses, together with the database facts. -/
theorem isModel_iff_firstOrder (kb : KnowledgeBase σ) (interpretation : Interpretation σ) :
    isModel kb interpretation ↔
      kb.db ⊆ interpretation ∧
        (let := herbrandStructure interpretation
         ∀ clause ∈ kb.prog, ∀ grounding : Grounding σ,
           (encodeClause clause).Realize grounding) := by
  rw [isModel, T_P_LP_le_iff]
  constructor
  · rintro ⟨database, closed⟩
    exact ⟨database, fun clause member grounding =>
      (encodeClause_realize_herbrand interpretation grounding clause).mpr
        (closed clause grounding member)⟩
  · rintro ⟨database, valid⟩
    exact ⟨database, fun clause grounding member =>
      (encodeClause_realize_herbrand interpretation grounding clause).mp
        (valid clause member grounding)⟩

end Mettapedia.Logic.LP.FirstOrderBridge
