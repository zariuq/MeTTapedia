import Mettapedia.GSLT.LanguageDef.Collections.TypedCertificates

/-!
# PeTTa's type relation, with multiplicity

`get-type` is a relation: a value may have several types, and a typed call
continues once for every answer that meets its formal. This module gives the
relation as CeTTa reads it, exactly in multiplicity.

**Declarations** have symbol subjects (`Decls`): each symbol has a list of
declared types, its rows. A type is a term over symbols and type variables
(`Ty`); the variables of a row are local to that row.

**Derivations.** A derivation of a value's type chooses one row at every node
of the value and records the type it gives and the equations its rows impose
(`Deriv`). A row's variables are renamed apart by the address of the node
that uses it (`DVar`), so the derivations of distinct nodes share no
variable. The rules follow PeTTa's clauses:
* a number, a string or a truth value has its class `Number`, `String` or
  `Bool`, and a variable value has every type without binding it;
* a symbol has the type of each of its rows;
* an application `(f a₁ … aₖ)` has, for each arrow row `(-> A₁ … Aₖ R)` of `f`,
  the result `R`, with each argument whose parameter is not `%Undefined%` or
  `_` typed at its parameter (`funTrees`);
* an expression with no such derivation has its **tuple type**, the list of
  its elements' types (`tupleTrees`);
* a value with no derivation has the type `%Undefined%` where another value
  needs one (`eff`).

Equations are solved over finite terms (`Sat`): a derivation is an answer when
its equations, the request and the equations already in force (a store) have
a common solution. The relation is a compositional judgment in the sense of
`TypedCertificates.Judgment` (`typeRelation`), so recorded judgments,
revision tokens and the dependence on the declarations of the symbols in a
term (`TypedCertificates.Judgment.check_eq`, `check_scoped`, `full_congr`)
hold for it.

**The guard** of a typed call is `get-type(V, T) *-> true ; get-metatype(V, T)`
(`guard`): one continuation for each answer of the type relation at the
formal, and only when there is none, the metatype of the value.

**Functional declarations.** When every symbol has at most one row, every
value has exactly one effective derivation (`card_eff`), so the relation has
at most one answer at every request and every guard succeeds at most once
(`card_getType_le_one`, `card_guard_le_one`); at a type variable that nothing
else names, the relation and the guard have exactly one answer
(`card_getType_fresh`, `card_guard_fresh`).

**Closed requests.** At a type without variables the store does not matter
(`card_getType_closed`), and the number of answers is `count`. A number, a
string or a truth value is typed at its class and nothing else, whatever the
declarations (`count_class`), and a variable value at every type once
(`count_var`).

**Rows.** A symbol's rows are read as a bag (`info_agree`), and CeTTa's index
keeps the first of each class of alpha-equivalent rows (`Decls.idemAlpha`), so
a repeated row changes no observation (`idemAlpha_addRow`).

The reading differs from SWI-PeTTa in two choices, both CeTTa's: terms are
finite (SWI-Prolog unifies without the occurs check), and repeated identical
rows are one declaration (`TypedCalls.Protocol`), where SWI's `get-type`
counts every row.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Type terms -/

/-- Type terms: variables over `V`, symbols, and applications. -/
inductive Ty (V : Type) where
  | var : V → Ty V
  | sym : String → Ty V
  | app : List (Ty V) → Ty V
  deriving Repr

namespace Ty

variable {V W X : Type}

mutual
/-- Decidable equality of type terms. -/
def decEq [DecidableEq V] : (a b : Ty V) → Decidable (a = b)
  | .var x, .var y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (Ty.var.inj e)
  | .sym s, .sym t =>
      if h : s = t then isTrue (h ▸ rfl) else isFalse fun e => h (Ty.sym.inj e)
  | .app xs, .app ys =>
      match decEqList xs ys with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (Ty.app.inj e)
  | .var _, .sym _ => isFalse fun e => by cases e
  | .var _, .app _ => isFalse fun e => by cases e
  | .sym _, .var _ => isFalse fun e => by cases e
  | .sym _, .app _ => isFalse fun e => by cases e
  | .app _, .var _ => isFalse fun e => by cases e
  | .app _, .sym _ => isFalse fun e => by cases e

/-- Decidable equality of lists of type terms. -/
def decEqList [DecidableEq V] : (xs ys : List (Ty V)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => by cases e
  | _ :: _, [] => isFalse fun e => by cases e
  | x :: xs, y :: ys =>
      match decEq x y, decEqList xs ys with
      | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
      | _, isFalse h' => isFalse fun e => h' (List.cons.inj e).2
end

instance [DecidableEq V] : DecidableEq (Ty V) := decEq

instance : Inhabited (Ty V) := ⟨.sym ""⟩

mutual
/-- Substitution. -/
def bind (f : V → Ty W) : Ty V → Ty W
  | .var v => f v
  | .sym s => .sym s
  | .app ts => .app (bindList f ts)

/-- Substitution in a list. -/
def bindList (f : V → Ty W) : List (Ty V) → List (Ty W)
  | [] => []
  | t :: ts => bind f t :: bindList f ts
end

mutual
/-- The variables of a type term, with repetitions. -/
def vars : Ty V → List V
  | .var v => [v]
  | .sym _ => []
  | .app ts => varsList ts

/-- The variables of a list of type terms. -/
def varsList : List (Ty V) → List V
  | [] => []
  | t :: ts => vars t ++ varsList ts
end

theorem bindList_eq_map (f : V → Ty W) (ts : List (Ty V)) :
    bindList f ts = ts.map (bind f) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [bindList, ih, List.map_cons]

@[simp] theorem bind_var' (f : V → Ty W) (v : V) : (Ty.var v).bind f = f v := rfl

@[simp] theorem bind_sym (f : V → Ty W) (s : String) : (Ty.sym s : Ty V).bind f = .sym s := rfl

@[simp] theorem bind_app (f : V → Ty W) (ts : List (Ty V)) :
    (Ty.app ts).bind f = .app (ts.map (bind f)) := by
  rw [bind, bindList_eq_map]

theorem varsList_eq (ts : List (Ty V)) : varsList ts = ts.flatMap vars := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [varsList, ih, List.flatMap_cons]

@[simp] theorem vars_var (v : V) : (Ty.var v).vars = [v] := rfl

@[simp] theorem vars_sym (s : String) : (Ty.sym s : Ty V).vars = [] := rfl

@[simp] theorem vars_app (ts : List (Ty V)) : (Ty.app ts).vars = ts.flatMap vars := by
  rw [vars, varsList_eq]

/-- A term's substitution depends only on its variables. -/
theorem bind_congr {f g : V → Ty W} : ∀ (t : Ty V), (∀ v ∈ t.vars, f v = g v) →
    t.bind f = t.bind g
  | .var v, h => h v (by simp)
  | .sym _, _ => rfl
  | .app ts, h => by
      rw [bind_app, bind_app]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact bind_congr t fun v hv => h v (by simp only [vars_app, List.mem_flatMap]; exact ⟨t, ht, hv⟩)

/-- Substituting twice is substituting once with the composite. -/
theorem bind_bind (f : V → Ty W) (g : W → Ty X) :
    ∀ (t : Ty V), (t.bind f).bind g = t.bind fun v => (f v).bind g
  | .var _ => rfl
  | .sym _ => rfl
  | .app ts => by
      rw [bind_app, bind_app, bind_app, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      exact bind_bind f g t

@[simp] theorem bind_var_id : ∀ (t : Ty V), t.bind Ty.var = t
  | .var _ => rfl
  | .sym _ => rfl
  | .app ts => by
      rw [bind_app]
      congr 1
      conv_rhs => rw [← List.map_id ts]
      apply List.map_congr_left
      intro t _
      exact bind_var_id t

/-- Renaming the variables. -/
def map (g : V → W) (t : Ty V) : Ty W := t.bind fun v => .var (g v)

@[simp] theorem map_var (g : V → W) (v : V) : (Ty.var v).map g = .var (g v) := rfl

@[simp] theorem map_sym (g : V → W) (s : String) : (Ty.sym s : Ty V).map g = .sym s := rfl

@[simp] theorem map_app (g : V → W) (ts : List (Ty V)) :
    (Ty.app ts).map g = .app (ts.map (map g)) := by
  simp only [map, bind_app]
  rfl

theorem bind_map (g : V → W) (f : W → Ty X) (t : Ty V) :
    (t.map g).bind f = t.bind (f ∘ g) := by
  rw [map, bind_bind]
  rfl

theorem vars_bind (f : V → Ty W) : ∀ (t : Ty V), (t.bind f).vars = t.vars.flatMap fun v => (f v).vars
  | .var v => by simp
  | .sym _ => rfl
  | .app ts => by
      rw [bind_app, vars_app, vars_app, List.flatMap_assoc, List.flatMap_map]
      apply List.flatMap_congr
      intro t _
      exact vars_bind f t

theorem vars_map (g : V → W) (t : Ty V) : (t.map g).vars = t.vars.map g := by
  rw [map, vars_bind]
  generalize t.vars = vs
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [List.flatMap_cons, vars_var, List.singleton_append, ih, List.map_cons]

/-- A ground type as a type over any variables. -/
def lift (t : Ty Empty) : Ty V := t.map Empty.elim

@[simp] theorem vars_lift (t : Ty Empty) : (t.lift : Ty V).vars = [] := by
  rw [lift, vars_map]
  cases h : t.vars with
  | nil => rfl
  | cons v _ => exact v.elim

theorem bind_lift (f : V → Ty W) (t : Ty Empty) : (t.lift : Ty V).bind f = t.lift := by
  rw [lift, lift, bind_map, map]
  exact bind_congr t fun v => v.elim

theorem lift_bind_ground (σ : V → Ty Empty) (t : Ty Empty) : (t.lift : Ty V).bind σ = t := by
  rw [bind_lift, lift, map]
  conv_rhs => rw [← bind_var_id t]
  exact bind_congr t fun v => v.elim

theorem map_map (g : V → W) (h : W → X) (t : Ty V) : (t.map g).map h = t.map (h ∘ g) := by
  rw [map, bind_map]
  rfl

end Ty

/-! ## Equations over finite terms -/

/-- An equation between type terms. -/
abbrev Eqn (V : Type) := Ty V × Ty V

namespace Eqn

variable {V W : Type}

/-- Renaming the variables of an equation. -/
def map (g : V → W) (e : Eqn V) : Eqn W := (e.1.map g, e.2.map g)

/-- The variables of an equation. -/
def vars (e : Eqn V) : List V := e.1.vars ++ e.2.vars

end Eqn

/-- The variables of a list of equations. -/
def eqnVars {V : Type} (E : List (Eqn V)) : List V := E.flatMap Eqn.vars

/-- A ground assignment solves a list of equations. -/
def Solves {V : Type} (σ : V → Ty Empty) (E : List (Eqn V)) : Prop :=
  ∀ e ∈ E, e.1.bind σ = e.2.bind σ

/-- A list of equations is satisfiable over finite ground terms. A unifiable
system has a ground solution, sending the variables a unifier leaves to a
symbol, so this is unifiability with the occurs check. -/
def Sat {V : Type} (E : List (Eqn V)) : Prop := ∃ σ : V → Ty Empty, Solves σ E

section Equations

variable {U V W : Type}

@[simp] theorem solves_nil (σ : V → Ty Empty) : Solves σ [] := fun _ h => absurd h List.not_mem_nil

theorem solves_append (σ : V → Ty Empty) (E F : List (Eqn V)) :
    Solves σ (E ++ F) ↔ Solves σ E ∧ Solves σ F := by
  simp only [Solves, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem solves_cons (σ : V → Ty Empty) (e : Eqn V) (E : List (Eqn V)) :
    Solves σ (e :: E) ↔ e.1.bind σ = e.2.bind σ ∧ Solves σ E := by
  simp only [Solves, List.mem_cons, forall_eq_or_imp]

theorem solves_singleton (σ : V → Ty Empty) (e : Eqn V) :
    Solves σ [e] ↔ e.1.bind σ = e.2.bind σ := by
  rw [solves_cons]
  simp

theorem sat_nil : Sat ([] : List (Eqn V)) := ⟨fun _ => default, solves_nil _⟩

theorem Sat.left {E F : List (Eqn V)} (h : Sat (E ++ F)) : Sat E := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, ((solves_append σ E F).mp hσ).1⟩

theorem Sat.right {E F : List (Eqn V)} (h : Sat (E ++ F)) : Sat F := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, ((solves_append σ E F).mp hσ).2⟩

theorem solves_map (σ : W → Ty Empty) (g : V → W) (E : List (Eqn V)) :
    Solves σ (E.map (Eqn.map g)) ↔ Solves (σ ∘ g) E := by
  simp only [Solves, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Eqn.map, Ty.bind_map]

theorem mem_eqnVars {E : List (Eqn V)} {v : V} :
    v ∈ eqnVars E ↔ ∃ e ∈ E, v ∈ e.1.vars ∨ v ∈ e.2.vars := by
  simp [eqnVars, Eqn.vars]

/-- A solution depends only on the variables of the equations. -/
theorem solves_congr {σ τ : V → Ty Empty} {E : List (Eqn V)}
    (same : ∀ v ∈ eqnVars E, σ v = τ v) : Solves σ E ↔ Solves τ E := by
  have side : ∀ e ∈ E, e.1.bind σ = e.1.bind τ ∧ e.2.bind σ = e.2.bind τ := fun e he =>
    ⟨Ty.bind_congr _ fun v hv => same v (mem_eqnVars.mpr ⟨e, he, .inl hv⟩),
      Ty.bind_congr _ fun v hv => same v (mem_eqnVars.mpr ⟨e, he, .inr hv⟩)⟩
  constructor
  · intro h e he
    rw [← (side e he).1, ← (side e he).2]
    exact h e he
  · intro h e he
    rw [(side e he).1, (side e he).2]
    exact h e he

theorem eqnVars_append (E F : List (Eqn V)) : eqnVars (E ++ F) = eqnVars E ++ eqnVars F := by
  simp [eqnVars]

theorem eqnVars_cons (e : Eqn V) (E : List (Eqn V)) : eqnVars (e :: E) = e.vars ++ eqnVars E := by
  simp [eqnVars]

theorem eqnVars_map (g : V → W) (E : List (Eqn V)) :
    eqnVars (E.map (Eqn.map g)) = (eqnVars E).map g := by
  simp only [eqnVars, Eqn.vars, Eqn.map, Ty.vars_map, List.flatMap_map, List.map_flatMap,
    List.map_append]

open Classical in
/-- **Systems over disjoint variables are solved separately.** -/
theorem sat_append_of_disjoint {E F : List (Eqn V)} (hE : Sat E) (hF : Sat F)
    (disjoint : ∀ v ∈ eqnVars E, v ∉ eqnVars F) : Sat (E ++ F) := by
  obtain ⟨σ, hσ⟩ := hE
  obtain ⟨τ, hτ⟩ := hF
  refine ⟨fun v => if v ∈ eqnVars F then τ v else σ v, (solves_append _ _ _).mpr ⟨?_, ?_⟩⟩
  · refine (solves_congr fun v hv => ?_).mpr hσ
    simp [disjoint v hv]
  · refine (solves_congr fun v hv => ?_).mpr hτ
    simp [hv]

open Classical in
/-- **A renamed block of fresh variables is solved separately**: equations whose
variables enter by an injective map that misses the variables of `S`. -/
theorem sat_append_map_iff {S : List (Eqn U)} {E : List (Eqn V)} (e : V → U)
    (injective : Function.Injective e) (fresh : ∀ v, e v ∉ eqnVars S) :
    Sat (S ++ E.map (Eqn.map e)) ↔ Sat S ∧ Sat E := by
  constructor
  · intro h
    refine ⟨h.left, ?_⟩
    obtain ⟨σ, hσ⟩ := h.right
    exact ⟨σ ∘ e, (solves_map σ e E).mp hσ⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨fun u => if h : ∃ v, e v = u then τ h.choose else σ u,
      (solves_append _ _ _).mpr ⟨?_, ?_⟩⟩
    · refine (solves_congr fun u hu => ?_).mpr hσ
      have : ¬ ∃ v, e v = u := fun ⟨v, hv⟩ => fresh v (hv ▸ hu)
      simp [this]
    · rw [solves_map]
      refine (solves_congr fun v _ => ?_).mpr hτ
      have h : ∃ w, e w = e v := ⟨v, rfl⟩
      simp only [Function.comp, dif_pos h]
      rw [injective h.choose_spec]

end Equations

/-! ## Derivations -/

/-- The variables of a derivation: the path from the value's root to the node
whose row introduced the variable, and the row variable's name; `none` names
the type of a variable leaf. -/
abbrev DVar := List ℕ × Option String

/-- A variable of the child at position `i`, seen from its parent. -/
def DVar.push (i : ℕ) (v : DVar) : DVar := (i :: v.1, v.2)

theorem DVar.push_injective (i : ℕ) : Function.Injective (DVar.push i) := by
  rintro ⟨p, x⟩ ⟨q, y⟩ h
  simp only [DVar.push, Prod.mk.injEq, List.cons.injEq, true_and] at h
  rw [h.1, h.2]

/-- A row variable of the node itself. -/
def DVar.own (x : String) : DVar := ([], some x)

theorem DVar.own_injective : Function.Injective DVar.own := by
  intro x y h
  simpa [DVar.own] using h

/-- A derivation: the type it gives and the equations its rows impose. -/
structure Deriv where
  ty : Ty DVar
  eqs : List (Eqn DVar)

/-- A child's derivation, seen from its parent. -/
def Deriv.push (i : ℕ) (d : Deriv) : Deriv :=
  ⟨d.ty.map (DVar.push i), d.eqs.map (Eqn.map (DVar.push i))⟩

/-- `%Undefined%`. -/
def undefinedTy {V : Type} : Ty V := .sym "%Undefined%"

/-- The derivation of a value that has none, where another value needs its
type: `%Undefined%`. -/
def undefinedDeriv : Deriv := ⟨undefinedTy, []⟩

/-- The derivation of a value class: `Number`, `String` or `Bool`. -/
def classDeriv (c : String) : Deriv := ⟨.sym c, []⟩

/-- What the relation records of a value: its rows, when it is a symbol, and
its derivations. -/
structure Info where
  rows : List (Ty String)
  cands : Multiset Deriv

/-- The derivations a value contributes where another value needs its type:
its own, or `%Undefined%` when it has none. -/
def eff (j : Info) : Multiset Deriv :=
  if Multiset.card j.cands = 0 then {undefinedDeriv} else j.cands

/-- An arrow row `(-> A₁ … Aₖ R)`: its parameters and its result. -/
def arrowSplit {V : Type} : Ty V → Option (List (Ty V) × Ty V)
  | .app (.sym s :: ts) => if s = "->" then ts.getLast?.map fun r => (ts.dropLast, r) else none
  | _ => none

/-- A parameter PeTTa does not check: `%Undefined%` or `_`. -/
def Unchecked {V : Type} : Ty V → Prop
  | .sym s => s = "%Undefined%" ∨ s = "_"
  | _ => False

instance {V : Type} (t : Ty V) : Decidable (Unchecked t) := by
  cases t <;> unfold Unchecked <;> infer_instance

/-- The equations of the checked arguments of a call through an arrow row, one
alternative for each choice of the arguments' derivations. Position `i` is the
argument's place in the expression. -/
def argEqs : ℕ → List (Ty String) → List Info → Multiset (List (Eqn DVar))
  | _, [], [] => {[]}
  | i, A :: As, j :: js =>
      if Unchecked A then argEqs (i + 1) As js
      else (eff j).bind fun d =>
        (argEqs (i + 1) As js).map fun E =>
          ((A.map DVar.own, (d.push i).ty) :: (d.push i).eqs) ++ E
  | _, [], _ :: _ => 0
  | _, _ :: _, [] => 0

open Classical in
/-- The derivations of an application through the arrow rows of its head. -/
noncomputable def funTrees (head : Info) (args : List Info) : Multiset Deriv :=
  (head.rows : Multiset (Ty String)).bind fun τ =>
    match arrowSplit τ with
    | some (As, R) =>
        if As.length = args.length then
          ((argEqs 1 As args).map fun E => (⟨R.map DVar.own, E⟩ : Deriv)).filter fun d => Sat d.eqs
        else 0
    | none => 0

/-- The parts of the tuple derivations of an expression: a type for each
element, from position `i` on. -/
def tupleParts : ℕ → List Info → Multiset (List (Ty DVar) × List (Eqn DVar))
  | _, [] => {([], [])}
  | i, j :: js => (eff j).bind fun d =>
      (tupleParts (i + 1) js).map fun p => ((d.push i).ty :: p.1, (d.push i).eqs ++ p.2)

/-- The tuple derivations of an expression: the list of its elements' types. -/
def tupleTrees (js : List Info) : Multiset Deriv :=
  (tupleParts 0 js).map fun p => ⟨.app p.1, p.2⟩

open Classical in
/-- An expression's derivations: through its head's arrow rows, or, when it has
none, its tuple type. -/
noncomputable def nodeInfo : List Info → Info
  | [] => ⟨[], tupleTrees []⟩
  | j :: js => ⟨[], if Multiset.card (funTrees j js) = 0 then tupleTrees (j :: js) else funTrees j js⟩

/-- Declarations with symbol subjects: the rows of each symbol, in written order. -/
abbrev Decls := String → List (Ty String)

/-- The derivations of the values that are not expressions. -/
def leafInfo (Γ : Decls) : Atom → Info
  | .symbol s => ⟨Γ s, (((Γ s).map fun τ => (⟨τ.map DVar.own, []⟩ : Deriv)) : Multiset Deriv)⟩
  | .var _ => ⟨[], {⟨.var ([], none), []⟩}⟩
  | .grounded (.int _) => ⟨[], {classDeriv "Number"}⟩
  | .grounded (.string _) => ⟨[], {classDeriv "String"}⟩
  | .grounded (.bool _) => ⟨[], {classDeriv "Bool"}⟩
  | .grounded (.custom _ _) => ⟨[], 0⟩
  | .expression _ => ⟨[], 0⟩

/-- **PeTTa's type relation is a compositional judgment**: the declarations
enter at the leaves, and an expression's derivations are one rule applied to
its elements'. -/
noncomputable def typeRelation : TypedCertificates.Judgment Decls Info where
  leaf := leafInfo
  node := nodeInfo

/-- The relation's record of a value. -/
noncomputable def info (Γ : Decls) (v : Atom) : Info := TypedCertificates.Judgment.full typeRelation Γ v

theorem info_expression (Γ : Decls) (xs : List Atom) :
    info Γ (.expression xs) = nodeInfo (xs.map (info Γ)) :=
  TypedCertificates.Judgment.full_expression typeRelation Γ xs

theorem info_symbol (Γ : Decls) (s : String) :
    info Γ (.symbol s) = ⟨Γ s, (((Γ s).map fun τ => (⟨τ.map DVar.own, []⟩ : Deriv)) : Multiset Deriv)⟩ :=
  rfl

theorem info_int (Γ : Decls) (n : ℤ) : info Γ (.grounded (.int n)) = ⟨[], {classDeriv "Number"}⟩ := rfl

theorem info_string (Γ : Decls) (s : String) :
    info Γ (.grounded (.string s)) = ⟨[], {classDeriv "String"}⟩ := rfl

theorem info_bool (Γ : Decls) (b : Bool) : info Γ (.grounded (.bool b)) = ⟨[], {classDeriv "Bool"}⟩ :=
  rfl

theorem info_var (Γ : Decls) (x : String) : info Γ (.var x) = ⟨[], {⟨.var ([], none), []⟩}⟩ := rfl

/-! ## Requests and the guard -/

open Classical in
/-- The answers of `get-type` for a value recorded as `j`, requested at `T`
under the store `S`: the store extended by each effective derivation, whose
variables enter by `e`, when the extension is satisfiable. -/
noncomputable def getType {U : Type} (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info) :
    Multiset (List (Eqn U)) :=
  ((eff j).map fun d => S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]).filter Sat

/-- PeTTa's `get-metatype`. `grounded` holds of the symbols that name a
registered function or a space, which PeTTa classes as `Grounded`. -/
def metatype (grounded : String → Bool) : Atom → String
  | .var _ => "Variable"
  | .grounded _ => "Grounded"
  | .expression _ => "Expression"
  | .symbol s => if grounded s then "Grounded" else "Symbol"

open Classical in
/-- **The guard of a typed call**, `get-type(V, T) *-> true ; get-metatype(V, T)`:
one continuation for each answer of the type relation, and the metatype only
when there is none. -/
noncomputable def guard {U : Type} (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info)
    (kind : String) : Multiset (List (Eqn U)) :=
  if Multiset.card (getType e S T j) = 0 then
    (({S ++ [(.sym kind, T)]} : Multiset (List (Eqn U)))).filter Sat
  else getType e S T j

open Classical in
/-- The number of answers of the type relation at a closed request. -/
noncomputable def count (j : Info) (T : Ty Empty) : ℕ :=
  Multiset.card ((eff j).filter fun d => Sat (d.eqs ++ [(d.ty, T.lift)]))

/-! ## Every derivation is satisfiable -/

section Invariants

theorem sat_push (i : ℕ) {E : List (Eqn DVar)} (h : Sat E) :
    Sat (E.map (Eqn.map (DVar.push i))) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun w => σ (w.1.tail, w.2), (solves_map _ _ _).mpr ?_⟩
  have same : ((fun w : DVar => σ (w.1.tail, w.2)) ∘ DVar.push i) = σ := by
    funext v
    rfl
  rw [same]
  exact hσ

theorem eqnVars_push (i : ℕ) (E : List (Eqn DVar)) :
    ∀ v ∈ eqnVars (E.map (Eqn.map (DVar.push i))), v.1.head? = some i := by
  intro v hv
  rw [eqnVars_map, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  rfl

theorem tupleParts_vars : ∀ (i : ℕ) (js : List Info), ∀ p ∈ tupleParts i js,
    ∀ v ∈ eqnVars p.2, ∃ k, i ≤ k ∧ v.1.head? = some k
  | _, [], p, hp, v, hv => by
      simp only [tupleParts, Multiset.mem_singleton] at hp
      subst hp
      simp [eqnVars] at hv
  | i, j :: js, p, hp, v, hv => by
      simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hp
      obtain ⟨d, -, p', hp', rfl⟩ := hp
      rw [eqnVars_append, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ⟨i, le_rfl, eqnVars_push i d.eqs v hv⟩
      · obtain ⟨k, hk, hv'⟩ := tupleParts_vars (i + 1) js p' hp' v hv
        exact ⟨k, by omega, hv'⟩

theorem tupleParts_sat : ∀ (i : ℕ) (js : List Info), (∀ j ∈ js, ∀ d ∈ eff j, Sat d.eqs) →
    ∀ p ∈ tupleParts i js, Sat p.2
  | _, [], _, p, hp => by
      simp only [tupleParts, Multiset.mem_singleton] at hp
      subst hp
      exact sat_nil
  | i, j :: js, h, p, hp => by
      simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hp
      obtain ⟨d, hd, p', hp', rfl⟩ := hp
      refine sat_append_of_disjoint (sat_push i (h j (by simp) d hd))
        (tupleParts_sat (i + 1) js (fun j' hj' => h j' (by simp [hj'])) p' hp') ?_
      intro v hv hv'
      obtain ⟨k, hk, hk'⟩ := tupleParts_vars (i + 1) js p' hp' v hv'
      rw [eqnVars_push i d.eqs v hv] at hk'
      cases hk'
      omega

theorem eff_sat {j : Info} (h : ∀ d ∈ j.cands, Sat d.eqs) : ∀ d ∈ eff j, Sat d.eqs := by
  intro d hd
  unfold eff at hd
  split_ifs at hd
  · rw [Multiset.mem_singleton] at hd
    subst hd
    exact sat_nil
  · exact h d hd

open Classical in
theorem nodeInfo_sat (js : List Info) (h : ∀ j ∈ js, ∀ d ∈ eff j, Sat d.eqs) :
    ∀ d ∈ (nodeInfo js).cands, Sat d.eqs := by
  have tuple : ∀ d ∈ tupleTrees js, Sat d.eqs := by
    intro d hd
    simp only [tupleTrees, Multiset.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact tupleParts_sat 0 js h p hp
  match js, h, tuple with
  | [], _, tuple => exact tuple
  | j :: js, _, tuple =>
      intro d hd
      simp only [nodeInfo] at hd
      split_ifs at hd
      · exact tuple d hd
      · simp only [funTrees, Multiset.mem_bind] at hd
        obtain ⟨τ, -, hd⟩ := hd
        split at hd
        · split_ifs at hd
          · exact (Multiset.mem_filter.mp hd).2
          · simp at hd
        · simp at hd

variable (Γ : Decls)

mutual
/-- **Every derivation the relation records is satisfiable.** -/
theorem cands_sat : ∀ v : Atom, ∀ d ∈ (info Γ v).cands, Sat d.eqs
  | .symbol s, d, hd => by
      rw [info_symbol] at hd
      simp only [Multiset.mem_coe, List.mem_map] at hd
      obtain ⟨τ, -, rfl⟩ := hd
      exact sat_nil
  | .var x, d, hd => by
      rw [info_var, Multiset.mem_singleton] at hd
      subst hd
      exact sat_nil
  | .grounded (.int n), d, hd => by
      rw [info_int, Multiset.mem_singleton] at hd
      subst hd
      exact sat_nil
  | .grounded (.string t), d, hd => by
      rw [info_string, Multiset.mem_singleton] at hd
      subst hd
      exact sat_nil
  | .grounded (.bool b), d, hd => by
      rw [info_bool, Multiset.mem_singleton] at hd
      subst hd
      exact sat_nil
  | .grounded (.custom _ _), d, hd => absurd hd (Multiset.notMem_zero d)
  | .expression xs, d, hd => by
      rw [info_expression] at hd
      exact nodeInfo_sat _ (effAll_sat xs) d hd

/-- The list version. -/
theorem effAll_sat : ∀ xs : List Atom, ∀ j ∈ xs.map (info Γ), ∀ d ∈ eff j, Sat d.eqs
  | [], j, hj => absurd hj List.not_mem_nil
  | x :: xs, j, hj => by
      rw [List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact eff_sat (cands_sat x)
      · exact effAll_sat xs j hj
end

end Invariants

/-! ## Functional declarations -/

/-- Every symbol has at most one row: the precondition of the trusted versions
(`space_type_annotations_functional`). -/
def Functional (Γ : Decls) : Prop := ∀ s, (Γ s).length ≤ 1

section Functional

theorem card_eff_of_le_one {j : Info} (h : Multiset.card j.cands ≤ 1) : Multiset.card (eff j) = 1 := by
  unfold eff
  split_ifs with h0
  · rfl
  · omega

theorem card_argEqs : ∀ (i : ℕ) (As : List (Ty String)) (js : List Info),
    (∀ j ∈ js, Multiset.card (eff j) = 1) → Multiset.card (argEqs i As js) ≤ 1
  | _, [], [], _ => by simp [argEqs]
  | i, A :: As, j :: js, h => by
      have rest := card_argEqs (i + 1) As js fun j' hj' => h j' (by simp [hj'])
      unfold argEqs
      split_ifs
      · exact rest
      · obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp (h j (by simp))
        rw [hd, Multiset.singleton_bind, Multiset.card_map]
        exact rest
  | _, [], _ :: _, _ => by simp [argEqs]
  | _, _ :: _, [], _ => by simp [argEqs]

theorem card_tupleParts : ∀ (i : ℕ) (js : List Info),
    (∀ j ∈ js, Multiset.card (eff j) = 1) → Multiset.card (tupleParts i js) = 1
  | _, [], _ => rfl
  | i, j :: js, h => by
      obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp (h j (by simp))
      simp only [tupleParts, hd, Multiset.singleton_bind, Multiset.card_map]
      exact card_tupleParts (i + 1) js fun j' hj' => h j' (by simp [hj'])

open Classical in
theorem card_funTrees_le_one (head : Info) (args : List Info) (rows : head.rows.length ≤ 1)
    (h : ∀ j ∈ args, Multiset.card (eff j) = 1) : Multiset.card (funTrees head args) ≤ 1 := by
  have each : ∀ τ ∈ head.rows, Multiset.card (match arrowSplit τ with
      | some (As, R) =>
          if As.length = args.length then
            ((argEqs 1 As args).map fun E => (⟨R.map DVar.own, E⟩ : Deriv)).filter fun d => Sat d.eqs
          else 0
      | none => 0) ≤ 1 := by
    intro τ _
    split
    · split_ifs
      · exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans
          ((Multiset.card_map _ _).le.trans (card_argEqs 1 _ args h))
      · simp
    · simp
  unfold funTrees
  match hr : head.rows, rows, each with
  | [], _, _ => simp
  | [τ], _, each => simpa using each τ (by simp)

variable {Γ : Decls}

theorem rows_length_le_one (hΓ : Functional Γ) : ∀ v : Atom, (info Γ v).rows.length ≤ 1
  | .symbol s => hΓ s
  | .var _ => by simp [info_var]
  | .grounded (.int _) => by simp [info_int]
  | .grounded (.string _) => by simp [info_string]
  | .grounded (.bool _) => by simp [info_bool]
  | .grounded (.custom _ _) => by simp [info, TypedCertificates.Judgment.full, typeRelation, leafInfo]
  | .expression xs => by
      rw [info_expression]
      cases xs <;> simp [nodeInfo]

mutual
/-- **Under functional declarations a value has at most one derivation.** -/
theorem card_cands_le_one (hΓ : Functional Γ) : ∀ v : Atom, Multiset.card (info Γ v).cands ≤ 1
  | .symbol s => by
      rw [info_symbol]
      simpa using hΓ s
  | .var _ => by simp [info_var]
  | .grounded (.int _) => by simp [info_int]
  | .grounded (.string _) => by simp [info_string]
  | .grounded (.bool _) => by simp [info_bool]
  | .grounded (.custom _ _) => by simp [info, TypedCertificates.Judgment.full, typeRelation, leafInfo]
  | .expression [] => by
      rw [info_expression]
      simp [nodeInfo, tupleTrees, tupleParts]
  | .expression (x :: xs) => by
      rw [info_expression, List.map_cons]
      have all := card_effAll hΓ (x :: xs)
      simp only [nodeInfo]
      split_ifs
      · rw [tupleTrees, Multiset.card_map, card_tupleParts 0 _ (by simpa using all)]
      · exact card_funTrees_le_one _ _ (rows_length_le_one hΓ x)
          fun j hj => all j (by simp [hj])

/-- The list version: every element contributes exactly one derivation. -/
theorem card_effAll (hΓ : Functional Γ) :
    ∀ xs : List Atom, ∀ j ∈ xs.map (info Γ), Multiset.card (eff j) = 1
  | [], j, hj => absurd hj List.not_mem_nil
  | x :: xs, j, hj => by
      rw [List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact card_eff_of_le_one (card_cands_le_one hΓ x)
      · exact card_effAll hΓ xs j hj
end

/-- **Under functional declarations a value contributes exactly one derivation.** -/
theorem card_eff (hΓ : Functional Γ) (v : Atom) : Multiset.card (eff (info Γ v)) = 1 :=
  card_eff_of_le_one (card_cands_le_one hΓ v)

end Functional

/-! ## Requests -/

section Requests

variable {U : Type}

open Classical in
theorem card_getType_le (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info) :
    Multiset.card (getType e S T j) ≤ Multiset.card (eff j) := by
  unfold getType
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (Multiset.card_map _ _).le

/-- **Under functional declarations `get-type` has at most one answer**, at every
request and under every store. -/
theorem card_getType_le_one {Γ : Decls} (hΓ : Functional Γ) (e : DVar → U) (S : List (Eqn U))
    (T : Ty U) (v : Atom) : Multiset.card (getType e S T (info Γ v)) ≤ 1 :=
  (card_getType_le e S T _).trans (card_eff hΓ v).le

open Classical in
/-- **The guard succeeds at most once** under functional declarations. -/
theorem card_guard_le_one {Γ : Decls} (hΓ : Functional Γ) (e : DVar → U) (S : List (Eqn U))
    (T : Ty U) (v : Atom) (kind : String) : Multiset.card (guard e S T (info Γ v) kind) ≤ 1 := by
  unfold guard
  split_ifs
  · exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by simp)
  · exact card_getType_le_one hΓ e S T v

theorem lift_map (g : DVar → U) (T : Ty Empty) : (T.lift : Ty DVar).map g = T.lift := by
  rw [Ty.map, Ty.bind_lift]

/-- At a closed request, a derivation's extension of a store is the store
followed by the renamed derivation with the request. -/
theorem extend_closed (e : DVar → U) (S : List (Eqn U)) (T : Ty Empty) (d : Deriv) :
    S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T.lift)] =
      S ++ (d.eqs ++ [(d.ty, T.lift)]).map (Eqn.map e) := by
  simp only [List.map_append, List.map_cons, List.map_nil, Eqn.map, lift_map, List.append_assoc]

open Classical in
/-- **At a closed request the store does not matter**: the answers are counted
by `count`, when the derivation's variables enter fresh. -/
theorem card_getType_closed (e : DVar → U) (injective : Function.Injective e) (S : List (Eqn U))
    (fresh : ∀ v, e v ∉ eqnVars S) (hS : Sat S) (T : Ty Empty) (j : Info) :
    Multiset.card (getType e S T.lift j) = count j T := by
  unfold getType count
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d _
  change Sat (S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T.lift)]) ↔ _
  rw [extend_closed, sat_append_map_iff e injective fresh]
  exact ⟨fun h => h.2, fun h => ⟨hS, h⟩⟩

theorem count_le (j : Info) (T : Ty Empty) : count j T ≤ Multiset.card (eff j) := by
  classical
  unfold count
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem count_le_one {Γ : Decls} (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) :
    count (info Γ v) T ≤ 1 :=
  (count_le _ T).trans (card_eff hΓ v).le

open Classical in
/-- **At a type variable that nothing else names, every derivation is an
answer.** -/
theorem card_getType_fresh (e : DVar → U) (injective : Function.Injective e) (S : List (Eqn U))
    (fresh : ∀ v, e v ∉ eqnVars S) (hS : Sat S) (t : U) (tFresh : t ∉ eqnVars S)
    (tNew : ∀ v, e v ≠ t) (j : Info) (hj : ∀ d ∈ eff j, Sat d.eqs) :
    Multiset.card (getType e S (.var t) j) = Multiset.card (eff j) := by
  unfold getType
  rw [Multiset.filter_eq_self.mpr, Multiset.card_map]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨σ, hσ⟩ := (sat_append_map_iff e injective fresh).mpr ⟨hS, hj d hd⟩
  have tOut : t ∉ eqnVars (S ++ d.eqs.map (Eqn.map e)) := by
    rw [eqnVars_append, eqnVars_map, List.mem_append, List.mem_map]
    rintro (h | ⟨w, -, hw⟩)
    · exact tFresh h
    · exact tNew w hw
  have tyOut : t ∉ (d.ty.map e).vars := by
    rw [Ty.vars_map, List.mem_map]
    rintro ⟨w, -, hw⟩
    exact tNew w hw
  refine ⟨fun u => if u = t then (d.ty.map e).bind σ else σ u, ?_⟩
  rw [solves_append, solves_singleton]
  constructor
  · refine (solves_congr fun u hu => ?_).mpr hσ
    have : u ≠ t := fun h => tOut (h ▸ hu)
    simp [this]
  · rw [Ty.bind_var']
    simp only [if_true]
    exact Ty.bind_congr _ fun u hu => by
      have : u ≠ t := fun h => tyOut (h ▸ hu)
      simp [this]

/-- **Under functional declarations `get-type` has exactly one answer at a
fresh type variable**, whatever the value. -/
theorem card_getType_fresh_eq_one {Γ : Decls} (hΓ : Functional Γ) (e : DVar → U)
    (injective : Function.Injective e) (S : List (Eqn U)) (fresh : ∀ v, e v ∉ eqnVars S)
    (hS : Sat S) (t : U) (tFresh : t ∉ eqnVars S) (tNew : ∀ v, e v ≠ t) (v : Atom) :
    Multiset.card (getType e S (.var t) (info Γ v)) = 1 := by
  rw [card_getType_fresh e injective S fresh hS t tFresh tNew _
    (eff_sat (cands_sat Γ v)), card_eff hΓ v]

/-- **The guard of a fresh type variable succeeds exactly once** under functional
declarations: a parameter whose type variable nothing else names admits every
value once. -/
theorem card_guard_fresh {Γ : Decls} (hΓ : Functional Γ) (e : DVar → U)
    (injective : Function.Injective e) (S : List (Eqn U)) (fresh : ∀ v, e v ∉ eqnVars S)
    (hS : Sat S) (t : U) (tFresh : t ∉ eqnVars S) (tNew : ∀ v, e v ≠ t) (v : Atom)
    (kind : String) : Multiset.card (guard e S (.var t) (info Γ v) kind) = 1 := by
  have one := card_getType_fresh_eq_one hΓ e injective S fresh hS t tFresh tNew v
  unfold guard
  rw [if_neg (by omega)]
  exact one

/-- The number of continuations of the guard at a closed formal: the answers of
the type relation, or, when it has none, one if the formal is the metatype. -/
noncomputable def guardCount (j : Info) (T : Ty Empty) (kind : String) : ℕ :=
  if count j T = 0 then (if T = .sym kind then 1 else 0) else count j T

open Classical in
theorem sat_closed_iff (S : List (Eqn U)) (a b : Ty Empty) (hS : Sat S) :
    Sat (S ++ [(a.lift, b.lift)]) ↔ a = b := by
  constructor
  · rintro ⟨σ, hσ⟩
    have h := ((solves_append σ S _).mp hσ).2
    rw [solves_singleton, Ty.lift_bind_ground, Ty.lift_bind_ground] at h
    exact h
  · rintro rfl
    obtain ⟨σ, hσ⟩ := hS
    exact ⟨σ, (solves_append σ S _).mpr ⟨hσ, (solves_singleton σ _).mpr rfl⟩⟩

open Classical in
/-- **The guard at a closed formal**, counted. -/
theorem card_guard_closed (e : DVar → U) (injective : Function.Injective e) (S : List (Eqn U))
    (fresh : ∀ v, e v ∉ eqnVars S) (hS : Sat S) (T : Ty Empty) (j : Info) (kind : String) :
    Multiset.card (guard e S T.lift j kind) = guardCount j T kind := by
  unfold guard guardCount
  rw [card_getType_closed e injective S fresh hS T j]
  split_ifs with h0 hk
  · rw [Multiset.card_eq_one]
    refine ⟨S ++ [(.sym kind, T.lift)], Multiset.filter_eq_self.mpr ?_⟩
    intro x hx
    rw [Multiset.mem_singleton] at hx
    subst hx
    have := (sat_closed_iff S (.sym kind) T hS).mpr hk.symm
    simpa [Ty.lift] using this
  · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_singleton] at hx
    subst hx
    intro h
    have : Sat (S ++ [((Ty.sym kind : Ty Empty).lift, T.lift)]) := by simpa [Ty.lift] using h
    exact hk ((sat_closed_iff S _ T hS).mp this).symm
  · exact card_getType_closed e injective S fresh hS T j

/-- **Away from the metatype, the guard is the type relation**: at a closed
formal other than the value's metatype, the guard's continuations are exactly
the relation's answers. -/
theorem guardCount_of_ne (j : Info) (T : Ty Empty) (kind : String) (h : T ≠ .sym kind) :
    guardCount j T kind = count j T := by
  unfold guardCount
  split_ifs with h0
  · rw [h0]
  · rfl

/-- At the metatype the guard always succeeds once, whatever the relation
says, under functional declarations. -/
theorem guardCount_metatype {Γ : Decls} (hΓ : Functional Γ) (v : Atom) (kind : String) :
    guardCount (info Γ v) (.sym kind) kind = 1 := by
  unfold guardCount
  have := count_le_one hΓ v (.sym kind)
  split_ifs with h0 h1
  · rfl
  · exact absurd rfl h1
  · omega

end Requests

/-! ## The rows of a symbol are a bag, and identical rows are one -/

section Rows

/-- Two records agree when their rows are one bag and their derivations one bag. -/
def Info.Agree (j j' : Info) : Prop :=
  (j.rows : Multiset (Ty String)) = j'.rows ∧ j.cands = j'.cands

theorem eff_agree {j j' : Info} (h : j.Agree j') : eff j = eff j' := by
  unfold eff
  rw [h.2]

theorem argEqs_agree : ∀ (i : ℕ) (As : List (Ty String)) (js js' : List Info),
    List.Forall₂ Info.Agree js js' → argEqs i As js = argEqs i As js'
  | _, [], [], [], _ => rfl
  | _, [], _ :: _, _ :: _, _ => rfl
  | _, _ :: _, [], [], _ => rfl
  | i, A :: As, j :: js, j' :: js', .cons hj hjs => by
      simp only [argEqs, eff_agree hj, argEqs_agree (i + 1) As js js' hjs]
  | _, [], [], _ :: _, h => by cases h
  | _, [], _ :: _, [], h => by cases h
  | _, _ :: _, [], _ :: _, h => by cases h
  | _, _ :: _, _ :: _, [], h => by cases h

theorem tupleParts_agree : ∀ (i : ℕ) (js js' : List Info),
    List.Forall₂ Info.Agree js js' → tupleParts i js = tupleParts i js'
  | _, [], [], _ => rfl
  | i, j :: js, j' :: js', .cons hj hjs => by
      simp only [tupleParts, eff_agree hj, tupleParts_agree (i + 1) js js' hjs]
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by cases h

theorem funTrees_agree {head head' : Info} {js js' : List Info} (hh : head.Agree head')
    (hjs : List.Forall₂ Info.Agree js js') : funTrees head js = funTrees head' js' := by
  unfold funTrees
  rw [hh.1, hjs.length_eq]
  congr 1
  funext τ
  split
  · rw [argEqs_agree 1 _ js js' hjs]
  · rfl

theorem nodeInfo_agree {js js' : List Info} (h : List.Forall₂ Info.Agree js js') :
    (nodeInfo js).Agree (nodeInfo js') := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hj hjs =>
      refine ⟨rfl, ?_⟩
      simp only [nodeInfo, funTrees_agree hj hjs, tupleTrees,
        tupleParts_agree 0 _ _ (List.Forall₂.cons hj hjs)]

variable {Γ Γ' : Decls}

mutual
/-- **The relation reads each symbol's rows as a bag.** -/
theorem info_agree (h : ∀ s, (Γ s : Multiset (Ty String)) = Γ' s) :
    ∀ v : Atom, (info Γ v).Agree (info Γ' v)
  | .symbol s => by
      rw [info_symbol, info_symbol]
      refine ⟨h s, ?_⟩
      rw [← Multiset.map_coe, ← Multiset.map_coe, h s]
  | .var _ => ⟨rfl, rfl⟩
  | .grounded (.int _) => ⟨rfl, rfl⟩
  | .grounded (.string _) => ⟨rfl, rfl⟩
  | .grounded (.bool _) => ⟨rfl, rfl⟩
  | .grounded (.custom _ _) => ⟨rfl, rfl⟩
  | .expression xs => by
      rw [info_expression, info_expression]
      exact nodeInfo_agree (infoAll_agree h xs)

/-- The list version. -/
theorem infoAll_agree (h : ∀ s, (Γ s : Multiset (Ty String)) = Γ' s) :
    ∀ xs : List Atom, List.Forall₂ Info.Agree (xs.map (info Γ)) (xs.map (info Γ'))
  | [] => .nil
  | x :: xs => .cons (info_agree h x) (infoAll_agree h xs)
end

/-- CeTTa's declaration index: identical rows are one declaration. -/
def Decls.idem (Γ : Decls) : Decls := fun s => (Γ s).dedup

/-- One more row for the symbol `s`. -/
def Decls.addRow (Γ : Decls) (s : String) (τ : Ty String) : Decls :=
  Function.update Γ s (Γ s ++ [τ])

/-- **A repeated identical row changes nothing**: with identical rows read as
one declaration, every value has the same derivations, so every request and
every guard has the same answers. -/
theorem info_idem_addRow (s : String) (τ : Ty String) (repeated : τ ∈ Γ s) (v : Atom) :
    (info (Decls.idem (Γ.addRow s τ)) v).cands = (info (Decls.idem Γ) v).cands := by
  refine (info_agree (fun s' => ?_) v).2
  by_cases hs : s' = s
  · subst hs
    simp only [Decls.idem, Decls.addRow, Function.update_self]
    rw [← Multiset.coe_dedup, ← Multiset.coe_dedup, Multiset.dedup_ext]
    intro a
    simp only [Multiset.mem_coe, List.mem_append, List.mem_singleton]
    exact ⟨fun h => h.elim id fun h => h ▸ repeated, Or.inl⟩
  · simp [Decls.idem, Decls.addRow, Function.update_of_ne hs]

/-- The index of functional declarations is functional. -/
theorem Functional.idem (hΓ : Functional Γ) : Functional (Decls.idem Γ) := fun s =>
  (List.dedup_sublist (Γ s)).length_le.trans (hΓ s)

/-! ### Rows identical up to the names of their variables -/

namespace Ty

mutual
/-- Rename the variables of a type by the order of their first occurrence:
`seen` lists the variables met so far, and the `i`-th is named `i`. -/
def canonAux : List String → Ty String → Ty String × List String
  | seen, .var x =>
      match seen.idxOf? x with
      | some i => (.var (toString i), seen)
      | none => (.var (toString seen.length), seen ++ [x])
  | seen, .sym s => (.sym s, seen)
  | seen, .app ts =>
      let r := canonAuxList seen ts
      (.app r.1, r.2)

/-- The list version. -/
def canonAuxList : List String → List (Ty String) → List (Ty String) × List String
  | seen, [] => ([], seen)
  | seen, t :: ts =>
      let r := canonAux seen t
      let rs := canonAuxList r.2 ts
      (r.1 :: rs.1, rs.2)
end

/-- The canonical form of a row: its variables named by first occurrence. Two
rows are alpha-equivalent when their canonical forms are equal. -/
def canon (t : Ty String) : Ty String := (canonAux [] t).1

end Ty

/-- **Alpha-equivalent rows**: rows that differ only in the names of their
variables. -/
def AlphaEq (τ τ' : Ty String) : Prop := Ty.canon τ = Ty.canon τ'

instance (τ τ' : Ty String) : Decidable (AlphaEq τ τ') := by
  unfold AlphaEq
  infer_instance

/-- Keep the first row of each alpha-equivalence class, in written order. -/
def dedupAlpha (l : List (Ty String)) : List (Ty String) :=
  l.foldl (fun acc τ => if acc.any fun σ => decide (AlphaEq σ τ) then acc else acc ++ [τ]) []

theorem dedupAlpha_aux_covers (l : List (Ty String)) :
    ∀ acc : List (Ty String), ∀ τ ∈ acc ++ l,
      ∃ σ ∈ l.foldl (fun acc τ => if acc.any fun σ => decide (AlphaEq σ τ) then acc else acc ++ [τ]) acc,
        AlphaEq σ τ := by
  induction l with
  | nil =>
      intro acc τ hτ
      exact ⟨τ, by simpa using hτ, rfl⟩
  | cons x xs ih =>
      intro acc τ hτ
      simp only [List.foldl_cons]
      split_ifs with hx
      · rcases List.mem_append.mp hτ with hτ | hτ
        · exact ih acc τ (List.mem_append_left _ hτ)
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · obtain ⟨σ, hσ, hστ⟩ := List.any_eq_true.mp hx
            obtain ⟨ρ, hρ, hρσ⟩ := ih acc σ (List.mem_append_left _ hσ)
            exact ⟨ρ, hρ, hρσ.trans (of_decide_eq_true hστ)⟩
          · exact ih acc τ (List.mem_append_right _ hτ)
      · rcases List.mem_append.mp hτ with hτ | hτ
        · exact ih (acc ++ [x]) τ (List.mem_append_left _ (List.mem_append_left _ hτ))
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · exact ih (acc ++ [τ]) τ (List.mem_append_left _ (by simp))
          · exact ih (acc ++ [x]) τ (List.mem_append_right _ hτ)

theorem dedupAlpha_aux_subset (l : List (Ty String)) :
    ∀ acc : List (Ty String), ∀ τ ∈ l.foldl (fun acc τ =>
      if acc.any fun σ => decide (AlphaEq σ τ) then acc else acc ++ [τ]) acc, τ ∈ acc ∨ τ ∈ l := by
  induction l with
  | nil => intro acc τ hτ; exact .inl hτ
  | cons x xs ih =>
      intro acc τ hτ
      simp only [List.foldl_cons] at hτ
      split_ifs at hτ
      · rcases ih acc τ hτ with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases ih (acc ++ [x]) τ hτ with h | h
        · rcases List.mem_append.mp h with h | h
          · exact .inl h
          · exact .inr (by simp at h; simp [h])
        · exact .inr (List.mem_cons_of_mem _ h)

/-- The index holds only written rows. -/
theorem dedupAlpha_subset (l : List (Ty String)) : ∀ τ ∈ dedupAlpha l, τ ∈ l := fun τ hτ =>
  (dedupAlpha_aux_subset l [] τ hτ).resolve_left (List.not_mem_nil)

/-- Every row has an alpha-equivalent row in the index. -/
theorem dedupAlpha_covers (l : List (Ty String)) :
    ∀ τ ∈ l, ∃ σ ∈ dedupAlpha l, AlphaEq σ τ := fun τ hτ =>
  dedupAlpha_aux_covers l [] τ (by simpa using hτ)

/-- **A row alpha-equivalent to one already written leaves the index as it was.** -/
theorem dedupAlpha_append_alpha (l : List (Ty String)) (τ : Ty String)
    (repeated : ∃ σ ∈ l, AlphaEq σ τ) : dedupAlpha (l ++ [τ]) = dedupAlpha l := by
  unfold dedupAlpha
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, if_pos]
  obtain ⟨σ, hσ, hστ⟩ := repeated
  obtain ⟨ρ, hρ, hρσ⟩ := dedupAlpha_covers l σ hσ
  exact List.any_eq_true.mpr ⟨ρ, hρ, decide_eq_true (hρσ.trans hστ)⟩

/-- CeTTa's declaration index: the first row of each alpha-equivalence class
(`space_annotated_types_append`). -/
def Decls.idemAlpha (Γ : Decls) : Decls := fun s => dedupAlpha (Γ s)

/-- **Identical rows are one row in every observation**: a row alpha-equivalent
to one the symbol has gives the same index, so every value has the same
derivations, and `get-type`, every guard and every typed call have the same
answers. -/
theorem idemAlpha_addRow (Γ : Decls) (s : String) (τ : Ty String)
    (repeated : ∃ σ ∈ Γ s, AlphaEq σ τ) : Decls.idemAlpha (Γ.addRow s τ) = Decls.idemAlpha Γ := by
  funext s'
  by_cases hs : s' = s
  · subst hs
    simp only [Decls.idemAlpha, Decls.addRow, Function.update_self]
    exact dedupAlpha_append_alpha _ τ repeated
  · simp [Decls.idemAlpha, Decls.addRow, Function.update_of_ne hs]

/-- Rows that are syntactically identical are alpha-equivalent. -/
theorem AlphaEq.refl (τ : Ty String) : AlphaEq τ τ := rfl

theorem AlphaEq.trans {τ σ ρ : Ty String} (h : AlphaEq τ σ) (h' : AlphaEq σ ρ) : AlphaEq τ ρ :=
  Eq.trans h h'

end Rows

/-! ## Value classes and variables -/

/-- The class of a grounded value: `Number`, `String` or `Bool`; spaces and other
grounded values have none. -/
def valueClass : GroundedValue → Option String
  | .int _ => some "Number"
  | .string _ => some "String"
  | .bool _ => some "Bool"
  | .custom _ _ => none

/-- The value classes. -/
def IsValueClass (c : String) : Prop := c = "Number" ∨ c = "String" ∨ c = "Bool"

instance (c : String) : Decidable (IsValueClass c) := by
  unfold IsValueClass
  infer_instance

theorem info_grounded_class (Γ : Decls) {g : GroundedValue} {c : String} (hg : valueClass g = some c) :
    info Γ (.grounded g) = ⟨[], {classDeriv c}⟩ := by
  cases g with
  | int n => simp only [valueClass, Option.some.injEq] at hg; subst hg; exact info_int Γ n
  | string s => simp only [valueClass, Option.some.injEq] at hg; subst hg; exact info_string Γ s
  | bool b => simp only [valueClass, Option.some.injEq] at hg; subst hg; exact info_bool Γ b
  | custom _ _ => cases hg

theorem sat_classDeriv_iff (c : String) (T : Ty Empty) :
    Sat ((classDeriv c).eqs ++ [((classDeriv c).ty, T.lift)]) ↔ T = .sym c := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [solves_append, solves_singleton] at hσ
    have := hσ.2
    rw [Ty.lift_bind_ground] at this
    exact this.symm
  · rintro rfl
    exact ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp [classDeriv],
      (solves_singleton _ _).mpr rfl⟩⟩

/-- **A grounded value has its class and nothing else**, whatever the
declarations. -/
theorem count_class (Γ : Decls) {g : GroundedValue} {c : String} (hg : valueClass g = some c)
    (T : Ty Empty) : count (info Γ (.grounded g)) T = if T = .sym c then 1 else 0 := by
  classical
  unfold count
  rw [info_grounded_class Γ hg]
  unfold eff
  simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
  by_cases h : T = .sym c
  · rw [if_pos ((sat_classDeriv_iff c T).mpr h), if_pos h]
    rfl
  · rw [if_neg (fun hs => h ((sat_classDeriv_iff c T).mp hs)), if_neg h]
    rfl

/-- **A variable value has every type once**, without binding it. -/
theorem count_var (Γ : Decls) (x : String) (T : Ty Empty) : count (info Γ (.var x)) T = 1 := by
  classical
  unfold count
  rw [info_var]
  unfold eff
  simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
  rw [if_pos ⟨fun _ => T, (solves_append _ _ _).mpr ⟨by simp, (solves_singleton _ _).mpr (by
    rw [Ty.bind_var', Ty.lift_bind_ground])⟩⟩]
  rfl

/-- A symbol with one closed declared type is typed once at that type and at no other. -/
theorem count_symbol_closed (Γ : Decls) (s : String) (τ : Ty Empty) (h : Γ s = [τ.lift])
    (T : Ty Empty) : count (info Γ (.symbol s)) T = if T = τ then 1 else 0 := by
  classical
  unfold count
  rw [info_symbol, h]
  unfold eff
  simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.card_singleton,
    one_ne_zero, if_false, Multiset.filter_singleton]
  have own : ((τ.lift : Ty String).map DVar.own) = (τ.lift : Ty DVar) := by
    rw [Ty.lift, Ty.map_map]
    congr 1
    funext v
    exact v.elim
  rw [own]
  by_cases hT : T = τ
  · subst hT
    rw [if_pos ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp,
      (solves_singleton _ _).mpr rfl⟩⟩, if_pos rfl]
    rfl
  · rw [if_neg, if_neg hT]
    · rfl
    · rintro ⟨σ, hσ⟩
      rw [solves_append, solves_singleton, Ty.lift_bind_ground, Ty.lift_bind_ground] at hσ
      exact hT hσ.2.symm

/-! ## Renamed rows: no count changes

A row may be replaced by a row that differs from it by an injective renaming of
its type variables without changing any count (`count_renamed_rows`): every
record is renamed derivation by derivation (`info_ren`), the renaming of a node
renaming its own variables as the row does and each child's as the child's
record does (`nodeRen`), and satisfiability does not see an injective renaming
(`sat_map_injective`). So whichever of two such rows a declaration keeps, every
count is the same. -/

section Renaming

theorem Ty.map_id' {V : Type} : ∀ t : Ty V, t.map id = t
  | .var _ => rfl
  | .sym _ => rfl
  | .app ts => by
      rw [Ty.map_app]
      congr 1
      conv_rhs => rw [← List.map_id ts]
      exact List.map_congr_left fun t _ => Ty.map_id' t

open Classical in
/-- **Satisfiability does not see an injective renaming of the variables.** -/
theorem sat_map_injective {V W : Type} {g : V → W} (hg : Function.Injective g) (E : List (Eqn V)) :
    Sat (E.map (Eqn.map g)) ↔ Sat E := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ ∘ g, (solves_map ρ g E).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun w => if h : ∃ v, g v = w then ρ h.choose else default, (solves_map _ g E).mpr ?_⟩
    have same : (fun w => if h : ∃ v, g v = w then ρ h.choose else default) ∘ g = ρ := by
      funext v
      have h : ∃ v', g v' = g v := ⟨v, rfl⟩
      simp only [Function.comp, dif_pos h]
      rw [hg h.choose_spec]
    rw [same]
    exact hρ

/-- A derivation with its variables renamed. -/
def Deriv.rename (g : DVar → DVar) (d : Deriv) : Deriv := ⟨d.ty.map g, d.eqs.map (Eqn.map g)⟩

/-- Derivations that differ by an injective renaming of their variables. -/
def Renamed (d d' : Deriv) : Prop := ∃ g : DVar → DVar, Function.Injective g ∧ d' = d.rename g

theorem Renamed.refl (d : Deriv) : Renamed d d := by
  refine ⟨id, Function.injective_id, ?_⟩
  have eqn : ∀ e : Eqn DVar, Eqn.map id e = e := fun e => by
    simp only [Eqn.map, Ty.map_id']
  obtain ⟨ty, eqs⟩ := d
  simp only [Deriv.rename, Ty.map_id', Deriv.mk.injEq, true_and]
  conv_lhs => rw [← List.map_id eqs]
  exact List.map_congr_left fun e _ => (eqn e).symm

/-- Rows that differ by an injective renaming of their type variables. -/
def RowRen (τ τ' : Ty String) : Prop := ∃ f : String → String, Function.Injective f ∧ τ' = τ.map f

/-- Records that differ by renamings: rows of type variables, derivations of
their variables. -/
def InfoRen (j j' : Info) : Prop :=
  List.Forall₂ RowRen j.rows j'.rows ∧ Multiset.Rel Renamed j.cands j'.cands

theorem rel_coe_forall₂ {α β : Type} {r : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ r l l' → Multiset.Rel r (l : Multiset α) l'
  | [], [], .nil => .zero
  | _ :: _, _ :: _, .cons h hs => by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe]
      exact .cons h (rel_coe_forall₂ hs)

theorem rel_filter_iff {α β : Type} {r : α → β → Prop} {p : α → Prop} {q : β → Prop}
    [DecidablePred p] [DecidablePred q] {s : Multiset α} {t : Multiset β} (h : Multiset.Rel r s t)
    (hpq : ∀ a b, r a b → (p a ↔ q b)) : Multiset.Rel r (s.filter p) (t.filter q) := by
  induction h with
  | zero => exact .zero
  | @cons a b as bs hab _ ih =>
      by_cases ha : p a
      · rw [Multiset.filter_cons_of_pos _ ha, Multiset.filter_cons_of_pos _ ((hpq a b hab).mp ha)]
        exact .cons hab ih
      · rw [Multiset.filter_cons_of_neg _ ha,
          Multiset.filter_cons_of_neg _ fun hb => ha ((hpq a b hab).mpr hb)]
        exact ih

theorem eff_ren {j j' : Info} (h : Multiset.Rel Renamed j.cands j'.cands) :
    Multiset.Rel Renamed (eff j) (eff j') := by
  unfold eff
  rw [Multiset.card_eq_card_of_rel h]
  split_ifs
  · exact .cons (Renamed.refl _) .zero
  · exact h

/-- The renaming of a node's variables: the own variables by `f`, a child's at
position `k` by `G k`. -/
def nodeRen (f : String → String) (G : ℕ → DVar → DVar) : DVar → DVar
  | ([], o) => ([], o.map f)
  | (k :: p, o) => DVar.push k (G k (p, o))

theorem nodeRen_injective {f : String → String} (hf : Function.Injective f) {G : ℕ → DVar → DVar}
    (hG : ∀ k, Function.Injective (G k)) : Function.Injective (nodeRen f G) := by
  rintro ⟨_ | ⟨k, p⟩, o⟩ ⟨_ | ⟨k', p'⟩, o'⟩ h
  · simp only [nodeRen, Prod.mk.injEq, true_and] at h
    rw [Option.map_injective hf h]
  · simp [nodeRen, DVar.push] at h
  · simp [nodeRen, DVar.push] at h
  · simp only [nodeRen, DVar.push, Prod.mk.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    have := hG k (Prod.ext h₁ h₂)
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]

theorem nodeRen_own (f : String → String) (G : ℕ → DVar → DVar) (x : String) :
    nodeRen f G (DVar.own x) = DVar.own (f x) := rfl

theorem nodeRen_push (f : String → String) (G : ℕ → DVar → DVar) (k : ℕ) (u : DVar) :
    nodeRen f G (DVar.push k u) = DVar.push k (G k u) := rfl

/-- Equation lists of an application's arguments from position `i`, renamed at
the node: one family of child renamings works whatever it is below `i`. -/
def EqRen (f : String → String) (i : ℕ) (E E' : List (Eqn DVar)) : Prop :=
  ∃ G : ℕ → DVar → DVar, (∀ k, Function.Injective (G k)) ∧
    ∀ G' : ℕ → DVar → DVar, (∀ k, i ≤ k → G' k = G k) → E' = E.map (Eqn.map (nodeRen f G'))

theorem map_map_own (f : String → String) (G : ℕ → DVar → DVar) (A : Ty String) :
    (A.map DVar.own).map (nodeRen f G) = (A.map f).map DVar.own := by
  rw [Ty.map_map, Ty.map_map]
  rfl

theorem map_push_ren (f : String → String) (G : ℕ → DVar → DVar) (k : ℕ) (g : DVar → DVar)
    (hk : G k = g) (t : Ty DVar) :
    (t.map (DVar.push k)).map (nodeRen f G) = (t.map g).map (DVar.push k) := by
  rw [Ty.map_map, Ty.map_map]
  congr 1
  funext u
  simp only [Function.comp, nodeRen_push, hk]

theorem eqns_push_ren (f : String → String) (G : ℕ → DVar → DVar) (k : ℕ) (g : DVar → DVar)
    (hk : G k = g) (E : List (Eqn DVar)) :
    (E.map (Eqn.map (DVar.push k))).map (Eqn.map (nodeRen f G)) =
      (E.map (Eqn.map g)).map (Eqn.map (DVar.push k)) := by
  simp only [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp, Eqn.map, map_push_ren f G k g hk]

open Classical in
theorem argEqs_ren {f : String → String} : ∀ (i : ℕ) (As : List (Ty String)) (js js' : List Info),
    List.Forall₂ (fun j j' => Multiset.Rel Renamed (eff j) (eff j')) js js' →
      Multiset.Rel (EqRen f i) (argEqs i As js) (argEqs i (As.map (Ty.map f)) js')
  | i, [], [], [], .nil =>
      .cons ⟨fun _ => id, fun _ => Function.injective_id, fun _ _ => rfl⟩ .zero
  | i, A :: As, j :: js, j' :: js', .cons hj hjs => by
      have rest := argEqs_ren (f := f) (i + 1) As js js' hjs
      have mono : ∀ E E', EqRen f (i + 1) E E' → EqRen f i E E' := fun E E' ⟨G, hG, h⟩ =>
        ⟨G, hG, fun G' hG' => h G' fun k hk => hG' k (by omega)⟩
      have unchecked : Unchecked (A.map f) ↔ Unchecked A := by
        cases A <;> simp [Unchecked, Ty.map]
      simp only [List.map_cons, argEqs]
      by_cases hu : Unchecked A
      · rw [if_pos hu, if_pos (unchecked.mpr hu)]
        exact Multiset.Rel.mono rest fun E _ E' _ h => mono E E' h
      · rw [if_neg hu, if_neg fun h => hu (unchecked.mp h)]
        refine Multiset.rel_bind (fun d d' ⟨g, hg, hd'⟩ => ?_) hj
        rw [Multiset.rel_map]
        refine Multiset.Rel.mono rest fun E _ E' _ ⟨G, hG, hE⟩ => ?_
        refine ⟨Function.update G i g, fun k => ?_, fun G' hG' => ?_⟩
        · by_cases hk : k = i
          · subst hk
            rw [Function.update_self]
            exact hg
          · rw [Function.update_of_ne hk]
            exact hG k
        · have atI : G' i = g := by rw [hG' i le_rfl, Function.update_self]
          have later : ∀ k, i + 1 ≤ k → G' k = G k := fun k hk => by
            rw [hG' k (by omega), Function.update_of_ne (by omega)]
          rw [hE G' later, hd']
          simp only [Deriv.rename, Deriv.push, List.cons_append, List.map_cons, List.map_append,
            Eqn.map, map_map_own f G' A, map_push_ren f G' i g atI, eqns_push_ren f G' i g atI]
  | _, [], _ :: _, _ :: _, _ => by simp only [List.map_nil, argEqs]; exact .zero
  | _, [], _ :: _, [], h => nomatch h
  | _, [], [], _ :: _, h => nomatch h
  | _, _ :: _, [], [], _ => by simp only [List.map_cons, argEqs]; exact .zero
  | _, _ :: _, [], _ :: _, h => nomatch h
  | _, _ :: _, _ :: _, [], h => nomatch h

/-- Tuple parts from position `i`, renamed at the node. -/
def PartsRen (i : ℕ) (p p' : List (Ty DVar) × List (Eqn DVar)) : Prop :=
  ∃ G : ℕ → DVar → DVar, (∀ k, Function.Injective (G k)) ∧
    ∀ G' : ℕ → DVar → DVar, (∀ k, i ≤ k → G' k = G k) →
      p'.1 = p.1.map (Ty.map (nodeRen id G')) ∧ p'.2 = p.2.map (Eqn.map (nodeRen id G'))

theorem tupleParts_ren : ∀ (i : ℕ) (js js' : List Info),
    List.Forall₂ (fun j j' => Multiset.Rel Renamed (eff j) (eff j')) js js' →
      Multiset.Rel (PartsRen i) (tupleParts i js) (tupleParts i js')
  | i, [], [], .nil => .cons ⟨fun _ => id, fun _ => Function.injective_id, fun _ _ => ⟨rfl, rfl⟩⟩ .zero
  | i, j :: js, j' :: js', .cons hj hjs => by
      have rest := tupleParts_ren (i + 1) js js' hjs
      simp only [tupleParts]
      refine Multiset.rel_bind (fun d d' ⟨g, hg, hd'⟩ => ?_) hj
      rw [Multiset.rel_map]
      refine Multiset.Rel.mono rest fun p _ p' _ ⟨G, hG, hp⟩ => ?_
      refine ⟨Function.update G i g, fun k => ?_, fun G' hG' => ?_⟩
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]
          exact hg
        · rw [Function.update_of_ne hk]
          exact hG k
      · have atI : G' i = g := by rw [hG' i le_rfl, Function.update_self]
        have later : ∀ k, i + 1 ≤ k → G' k = G k := fun k hk => by
          rw [hG' k (by omega), Function.update_of_ne (by omega)]
        obtain ⟨h₁, h₂⟩ := hp G' later
        rw [h₁, h₂, hd']
        simp only [Deriv.rename, Deriv.push, List.map_cons, List.map_append,
          map_push_ren id G' i g atI, eqns_push_ren id G' i g atI, and_self]

theorem arrowSplit_map (f : String → String) : ∀ τ : Ty String,
    arrowSplit (τ.map f) = (arrowSplit τ).map fun p => (p.1.map (Ty.map f), p.2.map f)
  | .var _ => rfl
  | .sym _ => rfl
  | .app [] => rfl
  | .app (.var _ :: _) => by simp [arrowSplit, Ty.map_app]
  | .app (.app _ :: _) => by simp [arrowSplit, Ty.map_app]
  | .app (.sym s :: ts) => by
      simp only [Ty.map_app, List.map_cons, Ty.map_sym, arrowSplit]
      split_ifs
      · rw [List.getLast?_map, Option.map_map, Option.map_map]
        congr 1
        funext r
        simp [List.map_dropLast]
      · rfl

open Classical in
theorem funTrees_ren {head head' : Info} {args args' : List Info}
    (rows : List.Forall₂ RowRen head.rows head'.rows)
    (hargs : List.Forall₂ (fun j j' => Multiset.Rel Renamed (eff j) (eff j')) args args') :
    Multiset.Rel Renamed (funTrees head args) (funTrees head' args') := by
  unfold funTrees
  refine Multiset.rel_bind (fun τ τ' ⟨f, hf, hτ'⟩ => ?_) (rel_coe_forall₂ rows)
  subst hτ'
  rw [arrowSplit_map]
  cases arrowSplit τ with
  | none => exact .zero
  | some p =>
      obtain ⟨As, R⟩ := p
      simp only [Option.map_some, List.length_map, hargs.length_eq]
      split_ifs
      · refine rel_filter_iff ?_ fun d d' ⟨g, hg, hd'⟩ => by
          rw [hd']
          exact (sat_map_injective hg _).symm
        rw [Multiset.rel_map]
        refine Multiset.Rel.mono (argEqs_ren 1 As args args' hargs) fun E _ E' _ ⟨G, hG, hE⟩ => ?_
        refine ⟨nodeRen f G, nodeRen_injective hf hG, ?_⟩
        rw [hE G fun _ _ => rfl]
        simp only [Deriv.rename, map_map_own]
      · exact .zero

open Classical in
theorem nodeInfo_ren : ∀ {js js' : List Info}, List.Forall₂ InfoRen js js' →
    InfoRen (nodeInfo js) (nodeInfo js')
  | [], [], .nil => ⟨.nil, Multiset.rel_refl_of_refl_on fun d _ => Renamed.refl d⟩
  | j :: js, j' :: js', .cons hj hjs => by
      have effs : List.Forall₂ (fun j j' => Multiset.Rel Renamed (eff j) (eff j')) (j :: js) (j' :: js') :=
        (List.Forall₂.cons hj hjs).imp fun _ _ h => eff_ren h.2
      have ft := funTrees_ren hj.1 (hjs.imp fun _ _ h => eff_ren h.2)
      refine ⟨.nil, ?_⟩
      simp only [nodeInfo]
      rw [Multiset.card_eq_card_of_rel ft]
      split_ifs
      · unfold tupleTrees
        rw [Multiset.rel_map]
        refine Multiset.Rel.mono (tupleParts_ren 0 _ _ effs) fun p _ p' _ ⟨G, hG, hp⟩ => ?_
        obtain ⟨h₁, h₂⟩ := hp G fun _ _ => rfl
        refine ⟨nodeRen id G, nodeRen_injective Function.injective_id hG, ?_⟩
        rw [h₁, h₂]
        simp only [Deriv.rename, Ty.map_app]
      · exact ft

theorem InfoRen.refl (j : Info) : InfoRen j j :=
  ⟨List.forall₂_same.mpr fun τ _ => ⟨id, Function.injective_id, (Ty.map_id' τ).symm⟩,
    Multiset.rel_refl_of_refl_on fun d _ => Renamed.refl d⟩

variable {Γ Γ' : Decls}

mutual
/-- **Renamed rows give renamed records**: when every row of `Γ'` is a row of `Γ`
with its type variables renamed injectively, in order, every value's record
under `Γ'` is its record under `Γ` with each derivation's variables renamed. -/
theorem info_ren (h : ∀ s, List.Forall₂ RowRen (Γ s) (Γ' s)) :
    ∀ v : Atom, InfoRen (info Γ v) (info Γ' v)
  | .symbol s => by
      rw [info_symbol, info_symbol]
      refine ⟨h s, rel_coe_forall₂ ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine (h s).imp fun τ τ' ⟨f, hf, hτ'⟩ => ⟨nodeRen f fun _ => id,
        nodeRen_injective hf fun _ => Function.injective_id, ?_⟩
      rw [hτ']
      simp only [Deriv.rename, map_map_own, List.map_nil]
  | .var x => InfoRen.refl _
  | .grounded g => by cases g <;> exact InfoRen.refl _
  | .expression es => by
      rw [info_expression, info_expression]
      exact nodeInfo_ren (infoAll_ren h es)

/-- The list version. -/
theorem infoAll_ren (h : ∀ s, List.Forall₂ RowRen (Γ s) (Γ' s)) :
    ∀ es : List Atom, List.Forall₂ InfoRen (es.map (info Γ)) (es.map (info Γ'))
  | [] => .nil
  | e :: es => .cons (info_ren h e) (infoAll_ren h es)
end

/-- **No count changes when rows are renamed** (alpha-variant rows): every value
has the same number of derivations at every closed type. -/
theorem count_renamed_rows (h : ∀ s, List.Forall₂ RowRen (Γ s) (Γ' s)) (v : Atom) (T : Ty Empty) :
    count (info Γ v) T = count (info Γ' v) T := by
  classical
  unfold count
  refine Multiset.card_eq_card_of_rel (rel_filter_iff (eff_ren (info_ren h v).2) fun d d' ⟨g, hg, hd'⟩ => ?_)
  rw [hd']
  have : (d.rename g).eqs ++ [((d.rename g).ty, (T.lift : Ty DVar))] =
      (d.eqs ++ [(d.ty, T.lift)]).map (Eqn.map g) := by
    simp only [Deriv.rename, List.map_append, List.map_cons, List.map_nil, Eqn.map, lift_map]
  rw [this, sat_map_injective hg]

end Renaming


/-! ## Controls -/

namespace Controls

/-- `(-> A B)` as written in a row. -/
def arrow2 (a b : Ty String) : Ty String := .app [.sym "->", a, b]

/-- `(-> $t $t)` and `(-> $u $u)` are one row. -/
theorem renamed_rows_alpha : AlphaEq (arrow2 (.var "t") (.var "t")) (arrow2 (.var "u") (.var "u")) := by
  decide

/-- `(-> Number Number)` and `(-> $t $t)` are distinct rows: typed alternatives. -/
theorem distinct_rows_not_alpha : ¬ AlphaEq (arrow2 (.sym "Number") (.sym "Number"))
    (arrow2 (.var "t") (.var "t")) := by
  decide

/-- `(-> $a $b)` and `(-> $a $a)` are distinct rows: the second couples its types. -/
theorem coupled_rows_not_alpha : ¬ AlphaEq (arrow2 (.var "a") (.var "b")) (arrow2 (.var "a") (.var "a")) := by
  decide

/-- The index of `(: f (-> $t $t))` written twice, once renamed, is one row. -/
theorem renamed_row_index :
    dedupAlpha [arrow2 (.var "t") (.var "t"), arrow2 (.var "u") (.var "u")] =
      [arrow2 (.var "t") (.var "t")] := by
  decide

/-- The index keeps distinct rows. -/
theorem distinct_row_index :
    dedupAlpha [arrow2 (.sym "Number") (.sym "Number"), arrow2 (.var "t") (.var "t")] =
      [arrow2 (.sym "Number") (.sym "Number"), arrow2 (.var "t") (.var "t")] := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
