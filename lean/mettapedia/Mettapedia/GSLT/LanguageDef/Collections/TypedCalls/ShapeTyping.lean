import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRelation

/-!
# HE's type relation as a tree automaton over solved typings

HE types an application `(c a₁ … aₙ)` from the typings of its parts, and a
typed constructor checks its arguments by typing them. Recomputing an
argument's typings walks the whole value below it, so building a list, a
numeral or a tree costs a walk per constructor. This module shows that the
walk is not needed: a value's typings, read by their solutions, are a
**stamp** that determines every typing above it, so the stamp of a new
constructor is one transition from its head's rows and its arguments' stamps.

**HE's relation** (`heRelation`, `heInfo`) is the rule of HE's type checker,
as a compositional judgment over the declarations:
* a symbol has a typing for each declared row other than `%Undefined%`, a
  number, string or truth value has its class, a variable has none;
* an expression `(h a₁ … aₙ)` has, first, a **tuple typing** for every
  choice of a value typing of `h` and a typing of each argument, the last
  argument varying fastest (`heTupleParts`); then, for every function
  typing of `h` in order, the **application typings** of HE's argument check
  (`checkArgs`): a parameter that is `%Undefined%`, `Atom` or the argument's
  metatype, or an argument without typings, is not checked; an argument whose
  every typing is an error passes its errors up; otherwise each valid typing
  whose type meets the parameter under the path's equations continues the
  path, and when none does, one error stands for each valid typing; a path
  that meets every parameter gives the range;
* `get-type` answers the valid typings, or `%Undefined%` when there are none
  at all (`answers`).
Equations are solved over finite terms, as in `TypeRelation`; every typing
of a part is renamed apart by its position.

**Stamps.** A typing is read by its solutions, the ground types it allows
(`sols`), and a stamp is an atom's metatype with its typings so read
(`stamp`). A derivation carries the equations of every row below it, so its
size grows with the value; its solutions do not.

**The stamp of a node follows from its children's** (`stamp_node`): for a
symbol head, `stamp (h a₁ … aₙ) = semNode (rows h) [stamp a₁, …, stamp aₙ]`,
where `semNode` reads nothing but the head's rows and the arguments' stamps
(`semCheck` follows the assignments of the row's variables that the path
allows). The equations of the parts are never needed again once their
solutions are known (`sols_push`, `rowSols_extend`, `tupleParts_sols`).

**The automaton.** Stamps with the rows of symbols form a compositional
judgment (`automaton`) whose state is the stamp on every constructor term
(`automaton_stamp`). A table of transitions keyed by the head's rows and the
arguments' stamps answers every constructor of that shape, whatever lies
below its arguments (`TransitionTable.read_eq`, `TransitionTable.valid_record`).
Everything `TypedCertificates` proves of recorded
judgments holds of it: a check that stops at recorded stamps is the full one,
a token-scoped record is sound under revision, a stamp depends only on the
declarations of the term's symbols (`stamp_congr`), and the build loop costs
four visits per constructor with the previous stamp recorded, against a
quadratic total without (`build_linear`, `build_quadratic`).

**The answers.** HE's `get-type` answers, read by their solutions, are the
stamp's valid typings, in order and with multiplicity (`answers_sols`,
`answers_multiset`); at a closed request their number is read off the stamp
(`count_answers`).

**Addresses.** A store keyed by address is sound when each entry records the
arena and the arena's reset epoch of the atom it was computed for: an
address keeps its atom while its arena's epoch is unchanged
(`Heap.run_keeps_cell`). The store's invariant (`Sound`) holds of the empty
store, survives recording (`sound_record`) and every allocation and reset
(`sound_step`, `sound_run`), and makes every hit whose epoch is current the
stamp of the atom now at that address (`validated_hit`), while a reused
address with the epoch unchecked would answer with the old atom's stamp
(`Controls.unvalidated_reuse`).

**Controls.** Positive: lists of numbers, Peano numerals and complete trees
of every size have one typing, `(List Number)`, `Nat` and `Tree`
(`Controls.list_stamp`, `Controls.peano_stamp`, `Controls.tree_stamp`).
Negative: a list holding a string after a number has no valid typing
(`Controls.wrong_class`); an element with two declarations gives two typings
(`Controls.element_two_rows`), and a head with two rows gives an answer and an
error (`Controls.head_two_rows`); a parameter the range does not fix copies the
argument's multiplicity, so equal answers repeat (`Controls.unfixed_parameter`);
a range variable no parameter fixes gives a stamp with every instance
(`Controls.unfixed_range`).

The model covers symbol-headed values without subtype declarations and
without declarations whose subject is an expression; `%Undefined%` inside a
declared type is a symbol here, where HE matches it with anything.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## HE's typing rule -/

/-- HE's metatype of an atom. -/
def metaName : Atom → String
  | .symbol _ => "Symbol"
  | .var _ => "Variable"
  | .grounded _ => "Grounded"
  | .expression _ => "Expression"

/-- HE's function types: expressions headed by `->` with at least one more
element. -/
def IsFun {V : Type} : Ty V → Bool
  | .app (.sym s :: _ :: _) => s == "->"
  | _ => false

/-- A parameter HE does not check against an argument's typings: `%Undefined%`,
`Atom`, or the argument's own metatype. -/
def heUnchecked {V : Type} (P : Ty V) (kind : String) : Bool :=
  match P with
  | .sym s => s == "%Undefined%" || s == "Atom" || s == kind
  | _ => false

/-- One entry of HE's typing list. A valid entry is a derivation: its type and
the equations its rows impose. An error entry carries the type HE records with
it, the failing function's type. -/
inductive Typing where
  | ok : Deriv → Typing
  | err : Deriv → Typing

namespace Typing

/-- The derivation an entry carries. -/
def deriv : Typing → Deriv
  | ok d => d
  | err d => d

/-- Whether an entry is valid. -/
def isOk : Typing → Bool
  | ok _ => true
  | err _ => false

/-- An entry of the part at position `i`, seen from its parent. -/
def push (i : ℕ) : Typing → Typing
  | ok d => ok (d.push i)
  | err d => err (d.push i)

/-- The derivation of a valid entry. -/
def okDeriv : Typing → Option Deriv
  | ok d => some d
  | err _ => none

end Typing

/-- What HE's type checker records of an atom: its metatype and its typings. -/
structure HeInfo where
  kind : String
  typs : List Typing

/-- The typing of a declared row: its type, with no equations. -/
def rowTyping (τ : Ty String) : Typing := .ok ⟨τ.map DVar.own, []⟩

/-- The rows HE reads for a symbol: every row except `%Undefined%`. -/
def readRows (rows : List (Ty String)) : List (Ty String) :=
  rows.filter fun τ => τ ≠ (undefinedTy : Ty String)

/-- HE's typings of the atoms that are not expressions. -/
def heLeaf (Γ : Decls) : Atom → HeInfo
  | .symbol s => ⟨"Symbol", (readRows (Γ s)).map rowTyping⟩
  | .var _ => ⟨"Variable", []⟩
  | .grounded g => ⟨"Grounded", match valueClass g with
      | some c => [.ok (classDeriv c)]
      | none => []⟩
  | .expression _ => ⟨"Expression", []⟩

/-- The parts of HE's tuple typings from position `i`: one typing of every
element, the last element varying fastest. -/
def heTupleParts : ℕ → List (List Typing) → List (List (Ty DVar) × List (Eqn DVar))
  | _, [] => [([], [])]
  | i, ts :: tss => ts.flatMap fun t =>
      (heTupleParts (i + 1) tss).map fun p =>
        ((t.deriv.push i).ty :: p.1, (t.deriv.push i).eqs ++ p.2)

/-- The equations of a path extended by a valid typing `d` of the argument at
position `i` against the parameter `P`. -/
def extendEqs (E : List (Eqn DVar)) (P : Ty DVar) (i : ℕ) (d : Deriv) : List (Eqn DVar) :=
  E ++ (d.push i).eqs ++ [(P, (d.push i).ty)]

open Classical in
/-- One typing of an argument continues the path when its type meets the
parameter under the path's equations. -/
noncomputable def stepMatch (E : List (Eqn DVar)) (P : Ty DVar) (i : ℕ) :
    Typing → Option (List (Eqn DVar))
  | .ok d => if Sat (extendEqs E P i d) then some (extendEqs E P i d) else none
  | .err _ => none

/-- **HE's argument check** against one function type `f` with range `R`, from
argument position `i` under the equations `E` of the path so far. -/
noncomputable def checkArgs (f : Deriv) (R : Ty DVar) : ℕ → List (Ty DVar) → List HeInfo →
    List (Eqn DVar) → List Typing
  | _, [], [], E => [.ok ⟨R, E⟩]
  | i, P :: Ps, j :: js, E =>
      if j.typs.isEmpty || heUnchecked P j.kind then checkArgs f R (i + 1) Ps js E
      else if j.typs.all (fun t => !t.isOk) then j.typs.map (Typing.push i)
      else
        let ms := j.typs.filterMap (stepMatch E P i)
        if ms.isEmpty then (j.typs.filter Typing.isOk).map fun _ => .err f
        else ms.flatMap (checkArgs f R (i + 1) Ps js)
  | _, [], _ :: _, _ => []
  | _, _ :: _, [], _ => []

/-- The application typings of one typing of the head. -/
noncomputable def appTypings (args : List HeInfo) (t : Typing) : List Typing :=
  match arrowSplit (t.deriv.push 0).ty with
  | some (Ps, R) =>
      if Ps.length = args.length then checkArgs (t.deriv.push 0) R 1 Ps args (t.deriv.push 0).eqs
      else [.err (t.deriv.push 0)]
  | none => []

/-- **HE's rule for an expression**: its tuple typings, then the application
typings of each function typing of its head. -/
noncomputable def heNode : List HeInfo → HeInfo
  | [] => ⟨"Expression", []⟩
  | h :: args =>
      ⟨"Expression",
        ((heTupleParts 0 (h.typs.filter (fun t => !IsFun t.deriv.ty) :: args.map HeInfo.typs)).map
            fun p => Typing.ok ⟨.app p.1, p.2⟩) ++
          (h.typs.filter (fun t => IsFun t.deriv.ty)).flatMap (appTypings args)⟩

/-- **HE's type relation** is a compositional judgment: the declarations enter
at the leaves. -/
noncomputable def heRelation : TypedCertificates.Judgment Decls HeInfo where
  leaf := heLeaf
  node := heNode

/-- HE's typings of an atom. -/
noncomputable def heInfo (Γ : Decls) (v : Atom) : HeInfo :=
  TypedCertificates.Judgment.full heRelation Γ v

theorem heInfo_expression (Γ : Decls) (xs : List Atom) :
    heInfo Γ (.expression xs) = heNode (xs.map (heInfo Γ)) :=
  TypedCertificates.Judgment.full_expression heRelation Γ xs

theorem heInfo_symbol (Γ : Decls) (s : String) : heInfo Γ (.symbol s) = heLeaf Γ (.symbol s) := rfl

theorem heInfo_var (Γ : Decls) (x : String) : heInfo Γ (.var x) = heLeaf Γ (.var x) := rfl

theorem heInfo_grounded (Γ : Decls) (g : GroundedValue) :
    heInfo Γ (.grounded g) = heLeaf Γ (.grounded g) := rfl

/-- HE's `get-type` answers of a typing list: its valid typings, or
`%Undefined%` when the list is empty. A list of errors answers nothing. -/
def answersOf (ts : List Typing) : List Deriv :=
  if ts.isEmpty then [undefinedDeriv] else ts.filterMap Typing.okDeriv

/-- HE's `get-type` answers of an atom. -/
noncomputable def answers (Γ : Decls) (v : Atom) : List Deriv := answersOf (heInfo Γ v).typs

/-! ## Solutions -/

/-- The ground types a derivation allows: the values of its type under the
solutions of its equations. -/
def sols (d : Deriv) : Set (Ty Empty) :=
  {T | ∃ σ : DVar → Ty Empty, Solves σ d.eqs ∧ d.ty.bind σ = T}

/-- Membership in the solutions is the satisfiability `TypeRelation` reads at a
closed request. -/
theorem mem_sols_iff (d : Deriv) (T : Ty Empty) : T ∈ sols d ↔ Sat (d.eqs ++ [(d.ty, T.lift)]) := by
  constructor
  · rintro ⟨σ, hσ, hT⟩
    refine ⟨σ, (solves_append _ _ _).mpr ⟨hσ, (solves_singleton _ _).mpr ?_⟩⟩
    simp only [Ty.lift_bind_ground, hT]
  · rintro ⟨σ, hσ⟩
    obtain ⟨h1, h2⟩ := (solves_append _ _ _).mp hσ
    refine ⟨σ, h1, ?_⟩
    have := (solves_singleton _ _).mp h2
    simpa only [Ty.lift_bind_ground] using this

/-- The ground instances of a row. -/
def inst (τ : Ty String) : Set (Ty Empty) := {T | ∃ θ : String → Ty Empty, τ.bind θ = T}

/-- An assignment of the variables of a derivation at position `i`, read back
from an assignment of its parent's variables. -/
def unpush (τ : DVar → Ty Empty) : DVar → Ty Empty := fun v => τ (v.1.tail, v.2)

theorem unpush_push (τ : DVar → Ty Empty) (i : ℕ) : unpush τ ∘ DVar.push i = τ := by
  funext w
  rfl

theorem solves_push (σ : DVar → Ty Empty) (i : ℕ) (d : Deriv) :
    Solves σ (d.push i).eqs ↔ Solves (σ ∘ DVar.push i) d.eqs := by
  simp only [Deriv.push]
  exact solves_map σ (DVar.push i) d.eqs

theorem bind_push_ty (σ : DVar → Ty Empty) (i : ℕ) (d : Deriv) :
    (d.push i).ty.bind σ = d.ty.bind (σ ∘ DVar.push i) := by
  simp only [Deriv.push]
  exact Ty.bind_map _ _ _

/-- **A part renamed by its position allows what it allowed alone.** -/
theorem sols_push (i : ℕ) (d : Deriv) : sols (d.push i) = sols d := by
  ext T
  constructor
  · rintro ⟨σ, hσ, hT⟩
    exact ⟨σ ∘ DVar.push i, (solves_push σ i d).mp hσ, by rw [← bind_push_ty]; exact hT⟩
  · rintro ⟨τ, hτ, hT⟩
    refine ⟨unpush τ, (solves_push _ i d).mpr ?_, ?_⟩
    · rw [unpush_push]; exact hτ
    · rw [bind_push_ty, unpush_push]; exact hT

/-- The solutions of a declared row are its ground instances. -/
theorem sols_row (τ : Ty String) (g : String → DVar) (hg : Function.Injective g) :
    sols ⟨τ.map g, []⟩ = inst τ := by
  ext T
  constructor
  · rintro ⟨σ, -, hT⟩
    exact ⟨σ ∘ g, by rw [← Ty.bind_map]; exact hT⟩
  · rintro ⟨θ, hT⟩
    classical
    refine ⟨fun v => if h : ∃ x, g x = v then θ h.choose else default, solves_nil _, ?_⟩
    rw [Ty.bind_map, ← hT]
    apply Ty.bind_congr
    intro x _
    have h : ∃ y, g y = g x := ⟨x, rfl⟩
    simp only [Function.comp, dif_pos h]
    rw [hg h.choose_spec]

theorem sols_classDeriv (c : String) : sols (classDeriv c) = {.sym c} := by
  ext T
  simp only [sols, classDeriv, Set.mem_singleton_iff, Ty.bind_sym]
  constructor
  · rintro ⟨-, -, hT⟩
    exact hT.symm
  · intro hT
    exact ⟨fun _ => default, solves_nil _, hT.symm⟩

theorem sols_undefinedDeriv : sols undefinedDeriv = {undefinedTy} := sols_classDeriv "%Undefined%"

/-! ## Stamps and the transition -/

/-- A typing read by its solutions. -/
inductive Sem where
  | ok : Set (Ty Empty) → Sem
  | err : Set (Ty Empty) → Sem

namespace Sem

/-- The solutions a read typing carries. -/
def set : Sem → Set (Ty Empty)
  | ok S => S
  | err S => S

/-- Whether a read typing is valid. -/
def isOk : Sem → Bool
  | ok _ => true
  | err _ => false

/-- The solutions of a valid read typing. -/
def okSet : Sem → Option (Set (Ty Empty))
  | ok S => some S
  | err _ => none

end Sem

/-- An entry read by its solutions. -/
def Typing.solve : Typing → Sem
  | .ok d => .ok (sols d)
  | .err d => .err (sols d)

theorem Typing.solve_push (i : ℕ) (t : Typing) : (t.push i).solve = t.solve := by
  cases t <;> simp only [Typing.push, Typing.solve, sols_push]

theorem Typing.isOk_solve (t : Typing) : t.solve.isOk = t.isOk := by cases t <;> rfl

theorem Typing.set_solve (t : Typing) : t.solve.set = sols t.deriv := by cases t <;> rfl

/-- **A stamp**: an atom's metatype, and its typings read by their solutions. -/
structure Stamp where
  kind : String
  typs : List Sem

/-- The stamp of what HE records of an atom. -/
def HeInfo.stamp (j : HeInfo) : Stamp := ⟨j.kind, j.typs.map Typing.solve⟩

/-- The stamp of an atom. -/
noncomputable def stamp (Γ : Decls) (v : Atom) : Stamp := (heInfo Γ v).stamp

/-- The products of solution sets, in HE's tuple order. -/
def prodSets : List (List (Set (Ty Empty))) → List (Set (List (Ty Empty)))
  | [] => [{[]}]
  | Ss :: Sss => Ss.flatMap fun S =>
      (prodSets Sss).map fun L => {l | ∃ T ∈ S, ∃ l' ∈ L, l = T :: l'}

/-- The tuple types of a set of element lists. -/
def appSet (L : Set (List (Ty Empty))) : Set (Ty Empty) := {T | ∃ l ∈ L, T = .app l}

/-- The assignments in `Θ` of a row's variables that send the parameter `P`
into the solutions `S`. -/
def narrow (Θ : Set (String → Ty Empty)) (P : Ty String) (S : Set (Ty Empty)) :
    Set (String → Ty Empty) :=
  {θ | θ ∈ Θ ∧ P.bind θ ∈ S}

open Classical in
/-- One read typing of an argument continues the path when some assignment the
path allows sends the parameter into its solutions. -/
noncomputable def semStep (Θ : Set (String → Ty Empty)) (P : Ty String) :
    Sem → Option (Set (String → Ty Empty))
  | .ok S => if (narrow Θ P S).Nonempty then some (narrow Θ P S) else none
  | .err _ => none

/-- **The argument check on stamps.** A path is the set `Θ` of the assignments of
the row's variables it allows. -/
noncomputable def semCheck (ρ R : Ty String) : List (Ty String) → List Stamp →
    Set (String → Ty Empty) → List Sem
  | [], [], Θ => [.ok {T | ∃ θ ∈ Θ, R.bind θ = T}]
  | P :: Ps, s :: ss, Θ =>
      if s.typs.isEmpty || heUnchecked P s.kind then semCheck ρ R Ps ss Θ
      else if s.typs.all (fun t => !t.isOk) then s.typs
      else
        let ms := s.typs.filterMap (semStep Θ P)
        if ms.isEmpty then (s.typs.filter Sem.isOk).map fun _ => .err (inst ρ)
        else ms.flatMap (semCheck ρ R Ps ss)
  | [], _ :: _, _ => []
  | _ :: _, [], _ => []

/-- The application typings of one function row, on stamps. -/
noncomputable def semApp (args : List Stamp) (ρ : Ty String) : List Sem :=
  match arrowSplit ρ with
  | some (Ps, R) =>
      if Ps.length = args.length then semCheck ρ R Ps args Set.univ else [.err (inst ρ)]
  | none => []

/-- **The transition**: the stamp of `(h a₁ … aₙ)` from the rows of the symbol
`h` and the arguments' stamps. -/
noncomputable def semNode (rows : List (Ty String)) (args : List Stamp) : Stamp :=
  ⟨"Expression",
    ((prodSets ((((readRows rows).filter fun τ => !IsFun τ).map inst) ::
        args.map fun s => s.typs.map Sem.set)).map fun L => Sem.ok (appSet L)) ++
      ((readRows rows).filter fun τ => IsFun τ).flatMap (semApp args)⟩

/-! ## Solutions of parts renamed apart -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
        flatMap_congr_mem fun y hy => h y (by simp [hy])]

/-- The assignment that reads the part at position `i` from `τ` and every other
variable from `σ`. -/
def splice (i : ℕ) (τ σ : DVar → Ty Empty) : DVar → Ty Empty :=
  fun v => if v.1.head? = some i then τ (v.1.tail, v.2) else σ v

theorem splice_push (i : ℕ) (τ σ : DVar → Ty Empty) : splice i τ σ ∘ DVar.push i = τ := by
  funext w
  simp [splice, DVar.push]

theorem splice_other {i : ℕ} (τ σ : DVar → Ty Empty) {v : DVar} (h : v.1.head? ≠ some i) :
    splice i τ σ v = σ v := by
  simp [splice, h]

theorem head_of_mem_vars_push {i : ℕ} {t : Ty DVar} {v : DVar} (h : v ∈ (t.map (DVar.push i)).vars) :
    v.1.head? = some i := by
  rw [Ty.vars_map, List.mem_map] at h
  obtain ⟨w, -, rfl⟩ := h
  rfl

theorem head_of_mem_eqnVars_push {i : ℕ} {E : List (Eqn DVar)} {v : DVar}
    (h : v ∈ eqnVars (E.map (Eqn.map (DVar.push i)))) : v.1.head? = some i := by
  rw [eqnVars_map, List.mem_map] at h
  obtain ⟨w, -, rfl⟩ := h
  rfl

/-- The variables of a tuple part. -/
def partVars (p : List (Ty DVar) × List (Eqn DVar)) : List DVar :=
  p.1.flatMap Ty.vars ++ eqnVars p.2

/-- The solutions of a tuple part: the lists of values of its types. -/
def partSols (p : List (Ty DVar) × List (Eqn DVar)) : Set (List (Ty Empty)) :=
  {l | ∃ σ : DVar → Ty Empty, Solves σ p.2 ∧ p.1.map (fun t => t.bind σ) = l}

theorem heTupleParts_vars : ∀ (i : ℕ) (tss : List (List Typing)),
    ∀ p ∈ heTupleParts i tss, ∀ v ∈ partVars p, ∃ k, i ≤ k ∧ v.1.head? = some k
  | _, [], p, hp, v, hv => by
      simp only [heTupleParts, List.mem_singleton] at hp
      subst hp
      simp [partVars, eqnVars] at hv
  | i, ts :: tss, p, hp, v, hv => by
      simp only [heTupleParts, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨t, -, p', hp', rfl⟩ := hp
      simp only [partVars, List.flatMap_cons, List.mem_append, eqnVars_append] at hv
      rcases hv with (hv | hv) | (hv | hv)
      · exact ⟨i, le_refl i, head_of_mem_vars_push hv⟩
      · obtain ⟨k, hk, h⟩ := heTupleParts_vars (i + 1) tss p' hp' v
          (by simp [partVars, hv])
        exact ⟨k, by omega, h⟩
      · exact ⟨i, le_refl i, head_of_mem_eqnVars_push hv⟩
      · obtain ⟨k, hk, h⟩ := heTupleParts_vars (i + 1) tss p' hp' v
          (by simp [partVars, hv])
        exact ⟨k, by omega, h⟩

/-- **A part renamed apart is solved separately**: the solutions of a tuple part
headed by the typing at position `i` are its solutions by the solutions of the
rest. -/
theorem partSols_cons (i : ℕ) (d : Deriv) (p : List (Ty DVar) × List (Eqn DVar))
    (hp : ∀ v ∈ partVars p, v.1.head? ≠ some i) :
    partSols ((d.push i).ty :: p.1, (d.push i).eqs ++ p.2) =
      {l | ∃ T ∈ sols d, ∃ l' ∈ partSols p, l = T :: l'} := by
  ext l
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨h1, h2⟩ := (solves_append _ _ _).mp hσ
    refine ⟨d.ty.bind (σ ∘ DVar.push i), ⟨σ ∘ DVar.push i, (solves_push σ i d).mp h1, rfl⟩,
      p.1.map fun t => t.bind σ, ⟨σ, h2, rfl⟩, ?_⟩
    simp only [List.map_cons, bind_push_ty]
  · rintro ⟨T, ⟨τ, hτ, hT⟩, l', ⟨σ', hσ', hl'⟩, rfl⟩
    refine ⟨splice i τ σ', (solves_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · rw [solves_push, splice_push]
      exact hτ
    · refine (solves_congr fun v hv => ?_).mpr hσ'
      exact splice_other τ σ' (hp v (by simp [partVars, hv]))
    · simp only [List.map_cons, bind_push_ty, splice_push, hT, ← hl']
      congr 1
      apply List.map_congr_left
      intro t ht
      apply Ty.bind_congr
      intro v hv
      exact splice_other τ σ' (hp v (by simp only [partVars, List.mem_append, List.mem_flatMap]; exact .inl ⟨t, ht, hv⟩))

/-- **Tuple parts read by their solutions are products of their elements'
solutions**, in HE's order. -/
theorem tupleParts_sols : ∀ (i : ℕ) (tss : List (List Typing)),
    (heTupleParts i tss).map partSols = prodSets (tss.map fun ts => ts.map fun t => sols t.deriv)
  | _, [] => by
      simp only [heTupleParts, List.map_cons, List.map_nil, prodSets, List.cons.injEq, and_true]
      ext l
      simp only [partSols, List.map_nil, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨fun _ => default, solves_nil _, h.symm⟩⟩
  | i, ts :: tss => by
      rw [List.map_cons, prodSets, ← tupleParts_sols (i + 1) tss, List.flatMap_map]
      simp only [heTupleParts, List.map_flatMap, List.map_map]
      apply flatMap_congr_mem
      intro t _
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp]
      rw [partSols_cons i t.deriv p fun v hv => by
        obtain ⟨k, hk, h⟩ := heTupleParts_vars (i + 1) tss p hp v hv
        rw [h]
        intro e
        cases e
        omega]

theorem sols_app (p : List (Ty DVar) × List (Eqn DVar)) :
    sols ⟨.app p.1, p.2⟩ = appSet (partSols p) := by
  ext T
  simp only [sols, appSet, partSols, Ty.bind_app]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
  · rintro ⟨l, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨σ, hσ, rfl⟩

/-! ## The argument check: paths read by the assignments of the row -/

/-- The variables of a row as an application sees them: the head's own
variables, at position `0`. -/
def own0 (x : String) : DVar := DVar.push 0 (DVar.own x)

theorem own0_injective : Function.Injective own0 := fun x y h => by
  simpa [own0, DVar.push, DVar.own] using h

/-- The assignments of a row's variables that extend to a solution of `E`. -/
def rowSols (E : List (Eqn DVar)) : Set (String → Ty Empty) :=
  {θ | ∃ σ : DVar → Ty Empty, Solves σ E ∧ ∀ x, σ (own0 x) = θ x}

theorem rowSols_nil : rowSols [] = Set.univ := by
  ext θ
  simp only [rowSols, Set.mem_univ, iff_true]
  exact ⟨fun v => match v.2 with
    | some x => θ x
    | none => default, solves_nil _, fun _ => rfl⟩

theorem rowSols_nonempty_iff (E : List (Eqn DVar)) : (rowSols E).Nonempty ↔ Sat E :=
  ⟨fun ⟨_, σ, hσ, _⟩ => ⟨σ, hσ⟩, fun ⟨σ, hσ⟩ => ⟨σ ∘ own0, σ, hσ, fun _ => rfl⟩⟩

/-- Every variable of `E` belongs to a part at a position below `i`. -/
def Below (i : ℕ) (E : List (Eqn DVar)) : Prop :=
  ∀ v ∈ eqnVars E, ∀ k, v.1.head? = some k → k < i

theorem below_mono {i j : ℕ} {E : List (Eqn DVar)} (h : Below i E) (le : i ≤ j) : Below j E :=
  fun v hv k hk => lt_of_lt_of_le (h v hv k hk) le

theorem head_own0_vars {P : Ty String} {v : DVar} (h : v ∈ (P.map own0).vars) : v.1.head? = some 0 := by
  rw [Ty.vars_map, List.mem_map] at h
  obtain ⟨w, -, rfl⟩ := h
  rfl

theorem below_extend {i : ℕ} {E : List (Eqn DVar)} (h : Below i E) (P : Ty String) (d : Deriv) :
    Below (i + 1) (extendEqs E (P.map own0) i d) := by
  intro v hv k hk
  unfold extendEqs at hv
  rw [eqnVars_append, eqnVars_append, List.mem_append, List.mem_append, eqnVars_cons] at hv
  rcases hv with (hv | hv) | hv
  · exact Nat.lt_succ_of_lt (h v hv k hk)
  · rw [head_of_mem_eqnVars_push (E := d.eqs) hv] at hk
    cases hk
    omega
  · simp only [Eqn.vars, eqnVars, List.flatMap_nil, List.append_nil, List.mem_append] at hv
    rcases hv with hv | hv
    · rw [head_own0_vars hv] at hk
      cases hk
      omega
    · rw [head_of_mem_vars_push (t := d.ty) hv] at hk
      cases hk
      omega

/-- **One step of a path**: the assignments a path extended by a typing allows
are those the path allowed that send the parameter into the typing's
solutions. -/
theorem rowSols_extend (E : List (Eqn DVar)) (P : Ty String) {i : ℕ} (d : Deriv) (hi : 1 ≤ i)
    (hE : Below i E) : rowSols (extendEqs E (P.map own0) i d) = narrow (rowSols E) P (sols d) := by
  ext θ
  constructor
  · rintro ⟨σ, hσ, hθ⟩
    simp only [extendEqs, solves_append, solves_singleton] at hσ
    obtain ⟨⟨hE', hd⟩, heq⟩ := hσ
    have own : σ ∘ own0 = θ := funext hθ
    refine ⟨⟨σ, hE', hθ⟩, σ ∘ DVar.push i, (solves_push σ i d).mp hd, ?_⟩
    rw [← bind_push_ty, ← heq, Ty.bind_map, own]
  · rintro ⟨⟨σ₁, hσ₁, hθ⟩, τ, hτ, hT⟩
    have own : ∀ x, splice i τ σ₁ (own0 x) = θ x := fun x => by
      rw [splice_other τ σ₁ (by simp only [own0, DVar.push]; intro e; cases e; omega), hθ]
    refine ⟨splice i τ σ₁, ?_, own⟩
    simp only [extendEqs, solves_append, solves_singleton]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (solves_congr fun v hv => ?_).mpr hσ₁
      apply splice_other
      intro e
      have := hE v hv i e
      omega
    · rw [solves_push, splice_push]
      exact hτ
    · rw [bind_push_ty, splice_push, hT, Ty.bind_map]
      exact Ty.bind_congr P fun x _ => own x

theorem sols_range (E : List (Eqn DVar)) (R : Ty String) :
    sols ⟨R.map own0, E⟩ = {T | ∃ θ ∈ rowSols E, R.bind θ = T} := by
  ext T
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ ∘ own0, ⟨σ, hσ, fun _ => rfl⟩, by rw [Ty.bind_map]⟩
  · rintro ⟨θ, ⟨σ, hσ, hθ⟩, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    rw [Ty.bind_map]
    exact Ty.bind_congr R fun x _ => hθ x

theorem heUnchecked_map {V W : Type} (g : V → W) (P : Ty V) (kind : String) :
    heUnchecked (P.map g) kind = heUnchecked P kind := by
  cases P <;> rfl

theorem stepMatch_rowSols (E : List (Eqn DVar)) (P : Ty String) {i : ℕ} (hi : 1 ≤ i)
    (hE : Below i E) (t : Typing) :
    (stepMatch E (P.map own0) i t).map rowSols = semStep (rowSols E) P t.solve := by
  classical
  cases t with
  | err d => rfl
  | ok d =>
      simp only [stepMatch, Typing.solve, semStep]
      rw [← rowSols_extend E P d hi hE]
      by_cases h : Sat (extendEqs E (P.map own0) i d)
      · rw [if_pos h, if_pos ((rowSols_nonempty_iff _).mpr h)]
        rfl
      · rw [if_neg h, if_neg (fun h' => h ((rowSols_nonempty_iff _).mp h'))]
        rfl

/-- **HE's argument check read by solutions is the check on stamps.** -/
theorem checkArgs_solve (ρ R : Ty String) :
    ∀ (Ps : List (Ty String)) (js : List HeInfo) (i : ℕ) (E : List (Eqn DVar)), 1 ≤ i → Below i E →
      (checkArgs ⟨ρ.map own0, []⟩ (R.map own0) i (Ps.map (Ty.map own0)) js E).map Typing.solve =
        semCheck ρ R Ps (js.map HeInfo.stamp) (rowSols E)
  | [], [], i, E, _, _ => by
      simp only [List.map_nil, checkArgs, List.map_cons, Typing.solve, semCheck, sols_range]
  | [], _ :: _, _, _, _, _ => by simp only [List.map_nil, List.map_cons, checkArgs, semCheck]
  | _ :: _, [], _, _, _, _ => by simp only [List.map_nil, List.map_cons, checkArgs, semCheck]
  | P :: Ps, j :: js, i, E, hi, hE => by
      have hm : (j.typs.filterMap (stepMatch E (P.map own0) i)).map rowSols =
          (j.typs.map Typing.solve).filterMap (semStep (rowSols E) P) := by
        rw [List.map_filterMap, List.filterMap_map]
        congr 1
        funext t
        exact stepMatch_rowSols E P hi hE t
      have hall : (j.typs.map Typing.solve).all (fun t => !t.isOk) = j.typs.all (fun t => !t.isOk) := by
        rw [List.all_map]
        congr 1
        funext t
        simp only [Function.comp, Typing.isOk_solve]
      simp only [List.map_cons, checkArgs, semCheck, HeInfo.stamp, List.isEmpty_map, heUnchecked_map]
      by_cases c : (j.typs.isEmpty || heUnchecked P j.kind) = true
      · rw [if_pos c, if_pos c]
        exact checkArgs_solve ρ R Ps js (i + 1) E (by omega) (below_mono hE (by omega))
      · rw [if_neg c, if_neg c, hall]
        by_cases c2 : j.typs.all (fun t => !t.isOk) = true
        · rw [if_pos c2, if_pos c2, List.map_map]
          congr 1
          funext t
          exact Typing.solve_push i t
        · rw [if_neg c2, if_neg c2]
          rw [← hm, List.isEmpty_map]
          by_cases c3 : (j.typs.filterMap (stepMatch E (P.map own0) i)).isEmpty = true
          · rw [if_pos c3, if_pos c3, List.map_map, List.filter_map, List.map_map]
            have hf : (Sem.isOk ∘ Typing.solve) = Typing.isOk := funext Typing.isOk_solve
            rw [hf]
            congr 1
            funext t
            simp only [Function.comp, Typing.solve, sols_row ρ own0 own0_injective]
          · rw [if_neg c3, if_neg c3, List.map_flatMap, List.flatMap_map]
            apply flatMap_congr_mem
            intro E' hE'
            rw [List.mem_filterMap] at hE'
            obtain ⟨t, -, ht⟩ := hE'
            cases t with
            | err d => simp [stepMatch] at ht
            | ok d =>
                simp only [stepMatch] at ht
                split_ifs at ht
                cases ht
                exact checkArgs_solve ρ R Ps js (i + 1) _ (by omega) (below_extend hE P d)

/-! ## The stamp of a node follows from its children's -/

theorem arrowSplit_map' {V W : Type} (g : V → W) : ∀ τ : Ty V,
    arrowSplit (τ.map g) = (arrowSplit τ).map fun p => (p.1.map (Ty.map g), p.2.map g)
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

theorem IsFun_map {V W : Type} (g : V → W) (τ : Ty V) : IsFun (τ.map g) = IsFun τ := by
  match τ with
  | .var _ => rfl
  | .sym _ => rfl
  | .app [] => rfl
  | .app [_] => cases ‹Ty V› <;> rfl
  | .app (x :: _ :: _) => cases x <;> rfl

theorem rowTyping_push (τ : Ty String) : (rowTyping τ).deriv.push 0 = ⟨τ.map own0, []⟩ := by
  simp only [rowTyping, Typing.deriv, Deriv.push, List.map_nil, Ty.map_map]
  rfl

theorem sols_rowTyping (τ : Ty String) : sols (rowTyping τ).deriv = inst τ :=
  sols_row τ DVar.own DVar.own_injective

theorem sols_own0 (τ : Ty String) : sols ⟨τ.map own0, []⟩ = inst τ := sols_row τ own0 own0_injective

/-- **The application typings of a row, read by solutions, are the transition's.** -/
theorem appTypings_solve (js : List HeInfo) (τ : Ty String) :
    (appTypings js (rowTyping τ)).map Typing.solve = semApp (js.map HeInfo.stamp) τ := by
  unfold appTypings semApp
  rw [rowTyping_push]
  dsimp only
  rw [arrowSplit_map']
  cases h : arrowSplit τ with
  | none => rfl
  | some p =>
      obtain ⟨Ps, R⟩ := p
      simp only [Option.map_some, List.length_map]
      split_ifs with hl
      · rw [← rowSols_nil]
        exact checkArgs_solve τ R Ps js 1 [] (le_refl 1) (fun v hv => by simp [eqnVars] at hv)
      · simp only [List.map_cons, List.map_nil, Typing.solve, sols_own0]

theorem tuple_heads (rows : List (Ty String)) :
    ((rows.map rowTyping).filter (fun t => !IsFun t.deriv.ty)).map (fun t => sols t.deriv) =
      (rows.filter fun τ => !IsFun τ).map inst := by
  rw [List.filter_map, List.map_map]
  have hf : ((fun t : Typing => !IsFun t.deriv.ty) ∘ rowTyping) = fun τ => !IsFun τ := by
    funext τ
    simp only [Function.comp, rowTyping, Typing.deriv, IsFun_map]
  rw [hf]
  apply List.map_congr_left
  intro τ _
  exact sols_rowTyping τ

theorem tuple_args (Γ : Decls) (args : List Atom) :
    ((args.map (heInfo Γ)).map HeInfo.typs).map (fun ts => ts.map fun t => sols t.deriv) =
      (args.map (stamp Γ)).map fun s => s.typs.map Sem.set := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp, stamp, HeInfo.stamp, List.map_map]
  apply List.map_congr_left
  intro t _
  exact (Typing.set_solve t).symm

theorem app_rows (rows : List (Ty String)) (js : List HeInfo) :
    (((rows.map rowTyping).filter (fun t => IsFun t.deriv.ty)).flatMap (appTypings js)).map
        Typing.solve = (rows.filter fun τ => IsFun τ).flatMap (semApp (js.map HeInfo.stamp)) := by
  rw [List.filter_map, List.flatMap_map, List.map_flatMap]
  have hf : ((fun t : Typing => IsFun t.deriv.ty) ∘ rowTyping) = fun τ => IsFun τ := by
    funext τ
    simp only [Function.comp, rowTyping, Typing.deriv, IsFun_map]
  rw [hf]
  apply flatMap_congr_mem
  intro τ _
  exact appTypings_solve js τ

/-- **The stamp of a symbol-headed expression is the transition** from the
head's rows and the arguments' stamps. -/
theorem stamp_node (Γ : Decls) (s : String) (args : List Atom) :
    stamp Γ (.expression (.symbol s :: args)) = semNode (Γ s) (args.map (stamp Γ)) := by
  have hsols : ∀ p : List (Ty DVar) × List (Eqn DVar),
      (Typing.ok ⟨.app p.1, p.2⟩).solve = Sem.ok (appSet (partSols p)) := fun p => by
    simp only [Typing.solve, sols_app]
  have hargs : args.map (stamp Γ) = (args.map (heInfo Γ)).map HeInfo.stamp := by
    rw [List.map_map]
    rfl
  simp only [stamp, heInfo_expression, List.map_cons, heInfo_symbol, heLeaf, heNode,
    HeInfo.stamp, semNode, List.map_append]
  congr 2
  · rw [List.map_map,
      show (Typing.solve ∘ fun p : List (Ty DVar) × List (Eqn DVar) => Typing.ok ⟨.app p.1, p.2⟩) =
        (fun L => Sem.ok (appSet L)) ∘ partSols from funext hsols,
      ← List.map_map, tupleParts_sols, List.map_cons, tuple_heads, tuple_args]
  · rw [app_rows]
    congr 1
    funext τ
    congr 1
    rw [List.map_map]
    rfl

/-! ## HE's answers, read by solutions, are the stamp's -/

/-- The answers a stamp gives: its valid typings, or `%Undefined%` when it has
none at all. -/
def stampAnswers (s : Stamp) : List (Set (Ty Empty)) :=
  if s.typs.isEmpty then [{undefinedTy}] else s.typs.filterMap Sem.okSet

/-- **HE's `get-type` answers, read by their solutions, are the stamp's**, in
order and with multiplicity. -/
theorem answers_sols (Γ : Decls) (v : Atom) :
    (answers Γ v).map sols = stampAnswers (stamp Γ v) := by
  simp only [answers, answersOf, stampAnswers, stamp, HeInfo.stamp, List.isEmpty_map]
  split_ifs
  · simp only [List.map_cons, List.map_nil, sols_undefinedDeriv]
  · rw [List.map_filterMap, List.filterMap_map]
    congr 1
    funext t
    cases t <;> rfl

theorem answers_multiset (Γ : Decls) (v : Atom) :
    (((answers Γ v).map sols : List (Set (Ty Empty))) : Multiset (Set (Ty Empty))) =
      (stampAnswers (stamp Γ v) : Multiset (Set (Ty Empty))) := by
  rw [answers_sols]

open Classical in
/-- **At a closed request the number of answers is read off the stamp.** -/
theorem count_answers (Γ : Decls) (v : Atom) (T : Ty Empty) :
    ((answers Γ v).filter fun d => decide (Sat (d.eqs ++ [(d.ty, T.lift)]))).length =
      ((stampAnswers (stamp Γ v)).filter fun S => decide (T ∈ S)).length := by
  rw [← answers_sols, List.filter_map, List.length_map]
  congr 2
  funext d
  simp only [Function.comp, mem_sols_iff]

/-! ## The automaton -/

/-- **Constructor terms**: symbols, variables, values, and expressions headed
by a symbol whose arguments are constructor terms. -/
inductive Ctor : Atom → Prop
  | symbol (s : String) : Ctor (.symbol s)
  | var (x : String) : Ctor (.var x)
  | grounded (g : GroundedValue) : Ctor (.grounded g)
  | app (s : String) (args : List Atom) : (∀ a ∈ args, Ctor a) → Ctor (.expression (.symbol s :: args))

/-- A state of the automaton: a stamp, and for a symbol its declared rows,
which the transition of an expression headed by it reads. -/
structure State where
  stamp : Stamp
  rows : Option (List (Ty String))

/-- The automaton's states at the leaves. -/
noncomputable def stateLeaf (Γ : Decls) : Atom → State
  | .symbol s => ⟨(heLeaf Γ (.symbol s)).stamp, some (Γ s)⟩
  | v => ⟨(heLeaf Γ v).stamp, none⟩

/-- The automaton's transition. An expression whose head is not a symbol is
outside the constructor terms; it gets the empty stamp. -/
noncomputable def stateNode : List State → State
  | h :: args => match h.rows with
      | some rows => ⟨semNode rows (args.map State.stamp), none⟩
      | none => ⟨⟨"Expression", []⟩, none⟩
  | [] => ⟨⟨"Expression", []⟩, none⟩

/-- **The automaton**: stamps as a compositional judgment over the declarations. -/
noncomputable def automaton : TypedCertificates.Judgment Decls State where
  leaf := stateLeaf
  node := stateNode

/-- **The automaton computes the stamps** of constructor terms, by transitions
alone. -/
theorem automaton_stamp (Γ : Decls) {v : Atom} (hv : Ctor v) :
    (TypedCertificates.Judgment.full automaton Γ v).stamp = stamp Γ v := by
  induction hv with
  | symbol s => rfl
  | var x => rfl
  | grounded g => rfl
  | app s args _ ih =>
      rw [TypedCertificates.Judgment.full_expression, stamp_node, List.map_cons]
      show (stateNode (stateLeaf Γ (.symbol s) :: _)).stamp = _
      simp only [stateNode, stateLeaf, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a ha

/-- A transition table: transitions recorded by the head's rows and the
arguments' stamps. -/
abbrev TransitionTable := List (Ty String) → List Stamp → Option Stamp

/-- Every recorded transition is the transition. -/
def TransitionTable.Valid (δ : TransitionTable) : Prop :=
  ∀ rows args s, δ rows args = some s → s = semNode rows args

/-- The transition read from a table, or computed where nothing is recorded. -/
noncomputable def TransitionTable.read (δ : TransitionTable) (rows : List (Ty String))
    (args : List Stamp) : Stamp :=
  (δ rows args).getD (semNode rows args)

/-- **A shape is typed by its holes' stamps**: a valid table answers every
transition, so one entry serves every constructor with the same head rows and
argument stamps, whatever the values below the arguments. -/
theorem TransitionTable.read_eq {δ : TransitionTable} (valid : δ.Valid) (rows : List (Ty String))
    (args : List Stamp) : δ.read rows args = semNode rows args := by
  unfold TransitionTable.read
  cases h : δ rows args with
  | none => rfl
  | some s => exact valid rows args s h

open Classical in
/-- Recording a computed transition keeps a table valid. -/
theorem TransitionTable.valid_record {δ : TransitionTable} (valid : δ.Valid)
    (rows : List (Ty String)) (args : List Stamp) :
    TransitionTable.Valid fun rows' args' =>
      if rows' = rows ∧ args' = args then some (semNode rows args) else δ rows' args' := by
  intro rows' args' s h
  simp only at h
  by_cases e : rows' = rows ∧ args' = args
  · rw [if_pos e] at h
    cases h
    rw [e.1, e.2]
  · rw [if_neg e] at h
    exact valid rows' args' s h

/-- **Recorded stamps**: a check that stops at every recorded state is the full
one, so its stamp is the stamp. -/
theorem recorded_stamp (Γ : Decls) (m : TypedCertificates.Judgment.Memo State)
    (valid : TypedCertificates.Judgment.Valid automaton Γ m) {v : Atom} (hv : Ctor v) :
    (TypedCertificates.Judgment.check automaton Γ m v).stamp = stamp Γ v := by
  rw [TypedCertificates.Judgment.check_eq automaton Γ m valid v, automaton_stamp Γ hv]

/-- **Recorded under a revision token**: states recorded with the token they
were computed under are used only under that token, and give the stamps of
its declarations. -/
theorem scoped_stamp {Tok : Type} [DecidableEq Tok] (decls : Tok → Decls)
    (m : TypedCertificates.Judgment.ScopedMemo Tok State)
    (valid : TypedCertificates.Judgment.ScopedValid automaton decls m) (tok : Tok)
    {v : Atom} (hv : Ctor v) :
    (TypedCertificates.Judgment.check automaton (decls tok)
      (TypedCertificates.Judgment.lookup tok m) v).stamp = stamp (decls tok) v := by
  rw [TypedCertificates.Judgment.check_scoped automaton decls valid tok v, automaton_stamp _ hv]

/-- **Unchanged declarations keep the stamp**: a stamp depends only on the rows
of the symbols in its term. -/
theorem stamp_congr {Γ Γ' : Decls} (v : Atom)
    (same : ∀ s, Atom.symbol s ∈ TypedCertificates.Judgment.leaves v → Γ s = Γ' s) :
    stamp Γ v = stamp Γ' v := by
  have h : heInfo Γ v = heInfo Γ' v := by
    apply TypedCertificates.Judgment.full_congr heRelation v
    intro ℓ hℓ
    cases ℓ with
    | symbol s => show heLeaf Γ (.symbol s) = heLeaf Γ' (.symbol s); simp only [heLeaf, same s hℓ]
    | var x => rfl
    | grounded g => rfl
    | expression xs => rfl
  simp only [stamp, h]

/-- **Linear with recorded stamps**: the build loop costs four visits per
constructor when the previous accumulator's state is recorded. -/
theorem build_linear (Γ : Decls) (n : ℕ) :
    ∑ k ∈ Finset.range n,
      TypedCertificates.Judgment.cost (TypedCertificates.memoUpTo automaton Γ k)
        (TypedCertificates.acc (k + 1)) = 4 * n :=
  TypedCertificates.incremental_total automaton Γ n

/-- **Quadratic without them**: walking each new argument costs
`(3n² + 5n) / 2` visits in all. -/
theorem build_quadratic (n : ℕ) :
    2 * ∑ k ∈ Finset.range n,
      TypedCertificates.Judgment.cost (fun _ => (none : Option State))
        (TypedCertificates.acc (k + 1)) = 3 * n * n + 5 * n :=
  TypedCertificates.full_total n

/-! ## Stamps kept by address -/

/-- Atoms at addresses: an address holds an atom of an arena, or nothing, and
every arena has a reset epoch. -/
structure Heap (Addr : Type) where
  cell : Addr → Option (Atom × ℕ)
  epoch : ℕ → ℕ

/-- What happens to a heap: an atom is placed at a free address of an arena, or
an arena is reset, which frees all its addresses for reuse and advances its
epoch. -/
inductive HeapOp (Addr : Type) where
  | alloc (p : Addr) (t : Atom) (a : ℕ)
  | reset (a : ℕ)

namespace Heap

variable {Addr : Type} [DecidableEq Addr]

/-- One heap operation. -/
def step (H : Heap Addr) : HeapOp Addr → Heap Addr
  | .alloc p t a =>
      if (H.cell p).isNone then ⟨Function.update H.cell p (some (t, a)), H.epoch⟩ else H
  | .reset a =>
      ⟨fun q => match H.cell q with
        | some (t, b) => if b = a then none else some (t, b)
        | none => none,
        Function.update H.epoch a (H.epoch a + 1)⟩

/-- A sequence of heap operations. -/
def run (H : Heap Addr) (ops : List (HeapOp Addr)) : Heap Addr := ops.foldl step H

theorem epoch_le_step (H : Heap Addr) (op : HeapOp Addr) (a : ℕ) :
    H.epoch a ≤ (H.step op).epoch a := by
  cases op with
  | alloc p t b =>
      simp only [step]
      split_ifs <;> exact le_refl _
  | reset b =>
      simp only [step]
      by_cases h : a = b
      · subst h
        simp
      · simp [Function.update_of_ne h]

theorem epoch_le_run (H : Heap Addr) (ops : List (HeapOp Addr)) (a : ℕ) :
    H.epoch a ≤ (H.run ops).epoch a := by
  induction ops generalizing H with
  | nil => exact le_refl _
  | cons op ops ih => exact le_trans (epoch_le_step H op a) (ih (H.step op))

theorem step_keeps_cell (H : Heap Addr) (op : HeapOp Addr) {p : Addr} {t : Atom} {a : ℕ}
    (hp : H.cell p = some (t, a)) (he : (H.step op).epoch a = H.epoch a) :
    (H.step op).cell p = some (t, a) := by
  cases op with
  | alloc q t' b =>
      simp only [step]
      split_ifs with hq
      · have hne : p ≠ q := fun e => by subst e; simp [hp] at hq
        simp only [Function.update_of_ne hne, hp]
      · exact hp
  | reset b =>
      by_cases hab : a = b
      · subst hab
        simp [step] at he
      · simp only [step, hp, if_neg hab]

/-- **An address keeps its atom while its arena's epoch is unchanged.** -/
theorem run_keeps_cell (H : Heap Addr) (ops : List (HeapOp Addr)) {p : Addr} {t : Atom} {a : ℕ}
    (hp : H.cell p = some (t, a)) (he : (H.run ops).epoch a = H.epoch a) :
    (H.run ops).cell p = some (t, a) := by
  induction ops generalizing H with
  | nil => exact hp
  | cons op ops ih =>
      have h1 := epoch_le_step H op a
      have h2 := epoch_le_run (H.step op) ops a
      have hs : (H.step op).epoch a = H.epoch a := le_antisymm (by
        show (H.step op).epoch a ≤ H.epoch a
        calc (H.step op).epoch a ≤ ((H.step op).run ops).epoch a := h2
          _ = H.epoch a := he) h1
      exact ih (H.step op) (step_keeps_cell H op hp hs) (by
        show ((H.step op).run ops).epoch a = (H.step op).epoch a
        rw [hs]
        exact he)

end Heap

/-- Stamps kept by address: each entry with the arena and the arena's epoch of
the atom it was computed for. -/
abbrev AddrMemo (Addr J : Type) := Addr → Option (ℕ × ℕ × J)

variable {Addr J : Type} [DecidableEq Addr]

/-- A lookup that checks the entry's arena and epoch against the atom now at the
address. -/
def lookupAt (H : Heap Addr) (m : AddrMemo Addr J) (p : Addr) : Option J :=
  match m p, H.cell p with
  | some (a, e, j), some (_, b) => if a = b ∧ e = H.epoch b then some j else none
  | _, _ => none

/-- **The store's invariant**: no entry has an epoch beyond its arena's, and every
entry whose epoch is current was computed for the atom at its address. -/
def Sound (H : Heap Addr) (f : Atom → J) (m : AddrMemo Addr J) : Prop :=
  (∀ p a e j, m p = some (a, e, j) → e ≤ H.epoch a) ∧
    ∀ p a e j, m p = some (a, e, j) → e = H.epoch a → ∃ t, H.cell p = some (t, a) ∧ j = f t

omit [DecidableEq Addr] in
theorem sound_empty (H : Heap Addr) (f : Atom → J) : Sound H f (fun _ => none) := by
  constructor <;> intro p a e j h <;> cases h

/-- Recording the value of the atom at an address, with its arena and the
current epoch, keeps the invariant. -/
theorem sound_record {H : Heap Addr} {f : Atom → J} {m : AddrMemo Addr J} (hm : Sound H f m)
    {p : Addr} {t : Atom} {a : ℕ} (hp : H.cell p = some (t, a)) :
    Sound H f (Function.update m p (some (a, H.epoch a, f t))) := by
  constructor
  · intro q b e j hq
    by_cases h : q = p
    · subst h
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      exact le_refl _
    · rw [Function.update_of_ne h] at hq
      exact hm.1 q b e j hq
  · intro q b e j hq he
    by_cases h : q = p
    · subst h
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, -, rfl⟩ := hq
      exact ⟨t, hp, rfl⟩
    · rw [Function.update_of_ne h] at hq
      exact hm.2 q b e j hq he

/-- Heap operations keep the invariant: allocation fills only free addresses, and
a reset advances the epoch past every entry of its arena. -/
theorem sound_step {H : Heap Addr} {f : Atom → J} {m : AddrMemo Addr J} (hm : Sound H f m)
    (op : HeapOp Addr) : Sound (H.step op) f m := by
  constructor
  · intro p a e j hp
    exact le_trans (hm.1 p a e j hp) (Heap.epoch_le_step H op a)
  · intro p a e j hp he
    have hle := hm.1 p a e j hp
    have hmono := Heap.epoch_le_step H op a
    have hs : (H.step op).epoch a = H.epoch a := by omega
    obtain ⟨t, ht, hj⟩ := hm.2 p a e j hp (by omega)
    exact ⟨t, Heap.step_keeps_cell H op ht hs, hj⟩

omit [DecidableEq Addr] in
/-- **A hit whose epoch is current is the value of the atom now at its address.** -/
theorem validated_hit {H : Heap Addr} {f : Atom → J} {m : AddrMemo Addr J} (hm : Sound H f m)
    {p : Addr} {j : J} (hit : lookupAt H m p = some j) :
    ∃ t a, H.cell p = some (t, a) ∧ j = f t := by
  unfold lookupAt at hit
  cases hmp : m p with
  | none => rw [hmp] at hit; cases hit
  | some entry =>
      obtain ⟨a, e, j'⟩ := entry
      cases hc : H.cell p with
      | none => rw [hmp, hc] at hit; cases hit
      | some content =>
          obtain ⟨t, b⟩ := content
          rw [hmp, hc] at hit
          simp only at hit
          split_ifs at hit with hv
          cases hit
          obtain ⟨hab, heb⟩ := hv
          subst hab
          obtain ⟨t', ht', hj⟩ := hm.2 p a e j hmp heb
          rw [hc] at ht'
          cases ht'
          exact ⟨t, a, rfl, hj⟩

/-- Along any sequence of heap operations, validated hits stay sound. -/
theorem sound_run {H : Heap Addr} {f : Atom → J} {m : AddrMemo Addr J} (hm : Sound H f m) :
    ∀ ops : List (HeapOp Addr), Sound (H.run ops) f m
  | [] => hm
  | op :: ops => sound_run (H := H.step op) (sound_step hm op) ops

/-- A stamp's kind is HE's metatype of its atom. -/
theorem stamp_kind (Γ : Decls) (v : Atom) : (stamp Γ v).kind = metaName v := by
  cases v with
  | symbol s => rfl
  | var x => rfl
  | grounded g => rfl
  | expression xs =>
      simp only [stamp, heInfo_expression, HeInfo.stamp, metaName]
      cases xs <;> rfl

theorem stamp_eta (Γ : Decls) (v : Atom) : stamp Γ v = ⟨metaName v, (stamp Γ v).typs⟩ := by
  rw [← stamp_kind]

/-! ## Controls -/

namespace Controls

/-- A type variable and a type constant of the control declarations. -/
def tv (x : String) : Ty String := .var x
def tc (c : String) : Ty String := .sym c

/-- An arrow row. -/
def arrow (ts : List (Ty String)) : Ty String := .app (.sym "->" :: ts)

/-- `(List t)`. -/
def listT (t : Ty String) : Ty String := .app [.sym "List", t]

/-- The rows of `Cons`, `S`, `Node`, `Wrap`, `Ph` and the two of `Box`. -/
def consRow : Ty String := arrow [tv "x", listT (tv "x"), listT (tv "x")]
def succRow : Ty String := arrow [tc "Nat", tc "Nat"]
def nodeRow : Ty String := arrow [tc "Tree", tc "Tree", tc "Tree"]
def wrapRow : Ty String := arrow [tv "y", tc "W"]
def phRow : Ty String := arrow [tv "v", .app [.sym "Ph", tv "w"]]
def boxNumber : Ty String := arrow [tc "Number", tc "Box"]
def boxString : Ty String := arrow [tc "String", tc "Box"]

/-- The control declarations: `(: Nil (List $x))`, `(: Cons (-> $x (List $x) (List $x)))`,
`(: Z Nat)`, `(: S (-> Nat Nat))`, `(: Leaf Tree)`, `(: Node (-> Tree Tree Tree))`,
`(: a A)`, `(: a B)`, `(: Wrap (-> $y W))`, `(: Ph (-> $v (Ph $w)))`,
`(: Box (-> Number Box))` and `(: Box (-> String Box))`. -/
def decls : Decls := fun s =>
  if s = "Nil" then [listT (tv "x")]
  else if s = "Cons" then [consRow]
  else if s = "Z" then [tc "Nat"]
  else if s = "S" then [succRow]
  else if s = "Leaf" then [tc "Tree"]
  else if s = "Node" then [nodeRow]
  else if s = "a" then [tc "A", tc "B"]
  else if s = "Wrap" then [wrapRow]
  else if s = "Ph" then [phRow]
  else if s = "Box" then [boxNumber, boxString]
  else []

/-- A number, a string, and an application of a symbol. -/
def num (n : ℤ) : Atom := .grounded (.int n)
def str (s : String) : Atom := .grounded (.string s)
def app (h : String) (args : List Atom) : Atom := .expression (.symbol h :: args)

/-- A ground type constant and `(List t)` over ground types. -/
def gc (c : String) : Ty Empty := .sym c
def glist (t : Ty Empty) : Ty Empty := .app [.sym "List", t]

theorem inst_const (c : String) : inst (tc c) = {gc c} := by
  ext T
  simp only [inst, tc, gc, Ty.bind_sym, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨fun _ => default, h.symm⟩⟩

theorem stamp_num (n : ℤ) : stamp decls (num n) = ⟨"Grounded", [.ok {gc "Number"}]⟩ := by
  simp only [stamp, num, heInfo_grounded, heLeaf, valueClass, HeInfo.stamp, List.map_cons,
    List.map_nil, Typing.solve, sols_classDeriv]
  rfl

theorem stamp_str (s : String) : stamp decls (str s) = ⟨"Grounded", [.ok {gc "String"}]⟩ := by
  simp only [stamp, str, heInfo_grounded, heLeaf, valueClass, HeInfo.stamp, List.map_cons,
    List.map_nil, Typing.solve, sols_classDeriv]
  rfl

theorem stamp_symbol (s : String) :
    stamp decls (.symbol s) = ⟨"Symbol", (readRows (decls s)).map fun τ => .ok (inst τ)⟩ := by
  simp only [stamp, heInfo_symbol, heLeaf, HeInfo.stamp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp, rowTyping, Typing.solve]
  rw [show (⟨τ.map DVar.own, []⟩ : Deriv) = (rowTyping τ).deriv from rfl, sols_rowTyping]

open Classical in
/-- The check of one argument with one valid typing. -/
theorem semCheck_one (ρ R P : Ty String) (Ps : List (Ty String)) (k : String) (S : Set (Ty Empty))
    (ss : List Stamp) (Θ : Set (String → Ty Empty)) (hP : heUnchecked P k = false) :
    semCheck ρ R (P :: Ps) (⟨k, [.ok S]⟩ :: ss) Θ =
      if (narrow Θ P S).Nonempty then semCheck ρ R Ps ss (narrow Θ P S) else [.err (inst ρ)] := by
  classical
  by_cases h : (narrow Θ P S).Nonempty
  · simp [semCheck, hP, semStep, h, Sem.isOk]
  · simp [semCheck, hP, semStep, h, Sem.isOk]
    rfl

/-- The check of one argument with two valid typings, each of which continues. -/
theorem semCheck_two (ρ R P : Ty String) (Ps : List (Ty String)) (k : String)
    (S₁ S₂ : Set (Ty Empty)) (ss : List Stamp) (Θ : Set (String → Ty Empty))
    (hP : heUnchecked P k = false) (h₁ : (narrow Θ P S₁).Nonempty) (h₂ : (narrow Θ P S₂).Nonempty) :
    semCheck ρ R (P :: Ps) (⟨k, [.ok S₁, .ok S₂]⟩ :: ss) Θ =
      semCheck ρ R Ps ss (narrow Θ P S₁) ++ semCheck ρ R Ps ss (narrow Θ P S₂) := by
  classical
  simp [semCheck, hP, semStep, h₁, h₂, Sem.isOk]

theorem semCheck_end (ρ R : Ty String) (Θ : Set (String → Ty Empty)) :
    semCheck ρ R [] [] Θ = [.ok {T | ∃ θ ∈ Θ, R.bind θ = T}] := by
  simp [semCheck]

/-- The transition of a head with one function row. -/
theorem semNode_one (ρ R : Ty String) (Ps : List (Ty String)) (args : List Stamp)
    (split : arrowSplit ρ = some (Ps, R)) (fn : IsFun ρ = true) (read : readRows [ρ] = [ρ])
    (len : Ps.length = args.length) :
    semNode [ρ] args = ⟨"Expression", semCheck ρ R Ps args Set.univ⟩ := by
  simp [semNode, read, fn, prodSets, semApp, split, len]

theorem narrow_var (Θ : Set (String → Ty Empty)) (x : String) (S : Set (Ty Empty)) :
    narrow Θ (tv x) S = {θ | θ ∈ Θ ∧ θ x ∈ S} := rfl

theorem narrow_const (Θ : Set (String → Ty Empty)) (c : String) (S : Set (Ty Empty)) :
    narrow Θ (tc c) S = {θ | θ ∈ Θ ∧ gc c ∈ S} := rfl

theorem decls_cons : decls "Cons" = [consRow] := by simp [decls]
theorem decls_nil : decls "Nil" = [listT (tv "x")] := by simp [decls]
theorem decls_succ : decls "S" = [succRow] := by simp [decls]
theorem decls_zero : decls "Z" = [tc "Nat"] := by simp [decls]
theorem decls_leaf : decls "Leaf" = [tc "Tree"] := by simp [decls]
theorem decls_node : decls "Node" = [nodeRow] := by simp [decls]
theorem decls_a : decls "a" = [tc "A", tc "B"] := by simp [decls]
theorem decls_wrap : decls "Wrap" = [wrapRow] := by simp [decls]
theorem decls_ph : decls "Ph" = [phRow] := by simp [decls]
theorem decls_box : decls "Box" = [boxNumber, boxString] := by simp [decls]

theorem read_one (τ : Ty String) (h : τ ≠ undefinedTy) : readRows [τ] = [τ] := by
  simp [readRows, h]

theorem consRow_split : arrowSplit consRow = some ([tv "x", listT (tv "x")], listT (tv "x")) := rfl
theorem succRow_split : arrowSplit succRow = some ([tc "Nat"], tc "Nat") := rfl
theorem nodeRow_split : arrowSplit nodeRow = some ([tc "Tree", tc "Tree"], tc "Tree") := rfl
theorem wrapRow_split : arrowSplit wrapRow = some ([tv "y"], tc "W") := rfl
theorem phRow_split : arrowSplit phRow = some ([tv "v"], .app [.sym "Ph", tv "w"]) := rfl

theorem stamp_nil : stamp decls (.symbol "Nil") = ⟨"Symbol", [.ok (inst (listT (tv "x")))]⟩ := by
  rw [stamp_symbol, decls_nil, read_one _ (by decide)]
  rfl

theorem stamp_a : stamp decls (.symbol "a") = ⟨"Symbol", [.ok {gc "A"}, .ok {gc "B"}]⟩ := by
  rw [stamp_symbol, decls_a]
  simp only [readRows, tc, undefinedTy, ne_eq, Ty.sym.injEq, decide_eq_true_eq, List.filter_cons,
    List.filter_nil]
  simp only [show ("A" = "%Undefined%") = False from by simp, show ("B" = "%Undefined%") = False from by simp,
    not_false_eq_true, if_true]
  rw [show (Ty.sym "A" : Ty String) = tc "A" from rfl, show (Ty.sym "B" : Ty String) = tc "B" from rfl]
  simp only [List.map_cons, List.map_nil, inst_const]

theorem stamp_const (s c : String) (h : decls s = [tc c]) (hc : c ≠ "%Undefined%") :
    stamp decls (.symbol s) = ⟨"Symbol", [.ok {gc c}]⟩ := by
  rw [stamp_symbol, h, read_one _ (by simp [tc, undefinedTy, hc])]
  simp [inst_const]

/-- The range set of a constant range. -/
theorem range_const (Θ : Set (String → Ty Empty)) (c : String) (hΘ : Θ.Nonempty) :
    {T | ∃ θ ∈ Θ, (tc c).bind θ = T} = {gc c} := by
  ext T
  simp only [tc, Ty.bind_sym, Set.mem_singleton_iff, gc]
  constructor
  · rintro ⟨_, _, h⟩
    exact h.symm
  · intro h
    obtain ⟨θ, hθ⟩ := hΘ
    exact ⟨θ, hθ, h.symm⟩

/-- A typing of an element at a constant type sends `$x` there. -/
theorem nonempty_var (Θ : Set (String → Ty Empty)) (x : String) (T : Ty Empty)
    (hΘ : ∀ θ, θ ∈ Θ) : (narrow Θ (tv x) {T}).Nonempty :=
  ⟨fun _ => T, hΘ _, rfl⟩

/-- One cell of a list of numbers: an element of class `Number` and a tail whose
one typing allows `(List Number)`. -/
theorem cons_number (n : ℤ) (tl : Atom) (S : Set (Ty Empty))
    (htl : (stamp decls tl).typs = [.ok S]) (hS : glist (gc "Number") ∈ S) :
    stamp decls (app "Cons" [num n, tl]) = ⟨"Expression", [.ok {glist (gc "Number")}]⟩ := by
  classical
  rw [app, stamp_node, decls_cons, List.map_cons, List.map_cons, List.map_nil, stamp_num,
    stamp_eta decls tl, htl,
    semNode_one consRow (listT (tv "x")) [tv "x", listT (tv "x")] _ consRow_split rfl
      (read_one _ (by decide)) rfl,
    semCheck_one _ _ (tv "x") _ "Grounded" {gc "Number"} _ _ rfl]
  have h1 : (narrow Set.univ (tv "x") {gc "Number"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  rw [if_pos h1, semCheck_one _ _ (listT (tv "x")) _ (metaName tl) S _ _ rfl]
  have bind_list : ∀ θ : String → Ty Empty, (listT (tv "x")).bind θ = glist (θ "x") := fun θ => by
    simp only [listT, tv, glist, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym, Ty.bind_var']
  have mem : ∀ θ : String → Ty Empty, θ ∈ narrow Set.univ (tv "x") {gc "Number"} →
      θ ∈ narrow (narrow Set.univ (tv "x") {gc "Number"}) (listT (tv "x")) S := by
    intro θ hθ
    refine ⟨hθ, ?_⟩
    have hx : θ "x" = gc "Number" := hθ.2
    show (listT (tv "x")).bind θ ∈ S
    rw [bind_list, hx]
    exact hS
  have h2 : (narrow (narrow Set.univ (tv "x") {gc "Number"}) (listT (tv "x")) S).Nonempty :=
    ⟨_, mem _ h1.some_mem⟩
  have hset : {T | ∃ θ ∈ narrow (narrow Set.univ (tv "x") {gc "Number"}) (listT (tv "x")) S,
      (listT (tv "x")).bind θ = T} = {glist (gc "Number")} := by
    ext T
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨θ, ⟨⟨-, hx⟩, -⟩, rfl⟩
      have hx : θ "x" = gc "Number" := hx
      rw [bind_list, hx]
    · rintro rfl
      exact ⟨fun _ => gc "Number", mem _ ⟨trivial, rfl⟩, bind_list _⟩
  rw [if_pos h2, semCheck_end, hset]

/-- A list of numbers ending in `Nil`. -/
def numList : List ℤ → Atom
  | [] => .symbol "Nil"
  | n :: ns => app "Cons" [num n, numList ns]

/-- **Positive control, lists**: a list of numbers of any positive length has one
typing, and it allows `(List Number)` alone. -/
theorem list_stamp : ∀ (n : ℤ) (ns : List ℤ),
    stamp decls (numList (n :: ns)) = ⟨"Expression", [.ok {glist (gc "Number")}]⟩
  | n, [] => cons_number n (.symbol "Nil") (inst (listT (tv "x")))
      (by rw [stamp_nil]) ⟨fun _ => gc "Number", rfl⟩
  | n, m :: ms => cons_number n _ {glist (gc "Number")} (by rw [list_stamp m ms]) rfl

/-- Peano numerals. -/
def peano : ℕ → Atom
  | 0 => .symbol "Z"
  | n + 1 => app "S" [peano n]

/-- **Positive control, Peano numerals**: every numeral has one typing, `Nat`. -/
theorem peano_stamp : ∀ n, (stamp decls (peano n)).typs = [.ok {gc "Nat"}]
  | 0 => by rw [peano, stamp_const "Z" "Nat" decls_zero (by decide)]
  | n + 1 => by
      classical
      have hk : heUnchecked (tc "Nat") (metaName (peano n)) = false := by
        cases n <;> rfl
      rw [peano, app, stamp_node, decls_succ, List.map_cons, List.map_nil, stamp_eta decls (peano n),
        peano_stamp n,
        semNode_one succRow (tc "Nat") [tc "Nat"] _ succRow_split rfl (read_one _ (by decide)) rfl,
        semCheck_one _ _ (tc "Nat") _ _ {gc "Nat"} _ _ hk]
      have h1 : (narrow Set.univ (tc "Nat") {gc "Nat"}).Nonempty := ⟨fun _ => default, trivial, rfl⟩
      rw [if_pos h1, semCheck_end, range_const _ _ h1]

/-- Complete binary trees. -/
def tree : ℕ → Atom
  | 0 => .symbol "Leaf"
  | n + 1 => app "Node" [tree n, tree n]

/-- **Positive control, trees**: every complete tree has one typing, `Tree`. -/
theorem tree_stamp : ∀ n, (stamp decls (tree n)).typs = [.ok {gc "Tree"}]
  | 0 => by rw [tree, stamp_const "Leaf" "Tree" decls_leaf (by decide)]
  | n + 1 => by
      classical
      have hk : heUnchecked (tc "Tree") (metaName (tree n)) = false := by
        cases n <;> rfl
      rw [tree, app, stamp_node, decls_node, List.map_cons, List.map_cons, List.map_nil,
        stamp_eta decls (tree n), tree_stamp n,
        semNode_one nodeRow (tc "Tree") [tc "Tree", tc "Tree"] _ nodeRow_split rfl
          (read_one _ (by decide)) rfl,
        semCheck_one _ _ (tc "Tree") _ _ {gc "Tree"} _ _ hk]
      have h1 : (narrow Set.univ (tc "Tree") {gc "Tree"}).Nonempty := ⟨fun _ => default, trivial, rfl⟩
      rw [if_pos h1, semCheck_one _ _ (tc "Tree") _ _ {gc "Tree"} _ _ hk]
      have h2 : (narrow (narrow Set.univ (tc "Tree") {gc "Tree"}) (tc "Tree") {gc "Tree"}).Nonempty :=
        ⟨fun _ => default, ⟨trivial, rfl⟩, rfl⟩
      rw [if_pos h2, semCheck_end, range_const _ _ h2]

/-- `(Cons "x" (Cons 1 Nil))`. -/
def stringFirst : Atom := app "Cons" [str "x", numList [1]]

/-- **Negative control, a wrong-class element**: a string before a list of numbers
leaves only an error, so `get-type` answers nothing. -/
theorem wrong_class : (stamp decls stringFirst).typs = [.err (inst consRow)] := by
  classical
  rw [stringFirst, app, stamp_node, decls_cons, List.map_cons, List.map_cons, List.map_nil,
    stamp_str, list_stamp 1 [],
    semNode_one consRow (listT (tv "x")) [tv "x", listT (tv "x")] _ consRow_split rfl
      (read_one _ (by decide)) rfl,
    semCheck_one _ _ (tv "x") _ "Grounded" {gc "String"} _ _ rfl]
  have h1 : (narrow Set.univ (tv "x") {gc "String"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  rw [if_pos h1, semCheck_one _ _ (listT (tv "x")) _ "Expression" {glist (gc "Number")} _ _ rfl]
  have h2 : ¬ (narrow (narrow Set.univ (tv "x") {gc "String"}) (listT (tv "x"))
      {glist (gc "Number")}).Nonempty := by
    rintro ⟨θ, ⟨-, hx⟩, hl⟩
    have hx : θ "x" = gc "String" := hx
    have hl : (listT (tv "x")).bind θ = glist (gc "Number") := hl
    simp only [listT, tv, glist, gc, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym,
      Ty.bind_var', hx] at hl
    simp at hl
  rw [if_neg h2]

theorem wrong_class_answers : answers decls stringFirst = [] := by
  have h := answers_sols decls stringFirst
  rw [stampAnswers, wrong_class] at h
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.filterMap_cons, Sem.okSet,
    List.filterMap_nil, List.map_eq_nil_iff] at h
  exact h

/-- `(Cons a Nil)`, where `a` is declared `A` and `B`. -/
def twoRowElement : Atom := app "Cons" [.symbol "a", .symbol "Nil"]

theorem nil_after (Θ : Set (String → Ty Empty)) (c : String)
    (hΘ : Θ = {θ | θ ∈ Set.univ ∧ θ "x" ∈ ({gc c} : Set (Ty Empty))}) :
    semCheck consRow (listT (tv "x")) [listT (tv "x")] [stamp decls (.symbol "Nil")] Θ =
      [.ok {glist (gc c)}] := by
  classical
  have bind_list : ∀ θ : String → Ty Empty, (listT (tv "x")).bind θ = glist (θ "x") := fun θ => by
    simp only [listT, tv, glist, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym, Ty.bind_var']
  rw [stamp_nil, semCheck_one _ _ (listT (tv "x")) _ "Symbol" _ _ _ rfl]
  have mem : ∀ θ ∈ Θ, θ ∈ narrow Θ (listT (tv "x")) (inst (listT (tv "x"))) :=
    fun θ hθ => ⟨hθ, θ, rfl⟩
  have inΘ : (fun _ => gc c) ∈ Θ := by rw [hΘ]; exact ⟨trivial, rfl⟩
  have h1 : (narrow Θ (listT (tv "x")) (inst (listT (tv "x")))).Nonempty := ⟨_, mem _ inΘ⟩
  have hset : {T | ∃ θ ∈ narrow Θ (listT (tv "x")) (inst (listT (tv "x"))),
      (listT (tv "x")).bind θ = T} = {glist (gc c)} := by
    ext T
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨θ, ⟨hθ, -⟩, rfl⟩
      rw [hΘ] at hθ
      have hx : θ "x" = gc c := hθ.2
      rw [bind_list, hx]
    · rintro rfl
      exact ⟨fun _ => gc c, mem _ inΘ, bind_list _⟩
  rw [if_pos h1, semCheck_end, hset]

/-- **Negative control, an element with two declarations**: the list has two
typings, `(List A)` and `(List B)`, as HE answers. -/
theorem element_two_rows :
    (stamp decls twoRowElement).typs = [.ok {glist (gc "A")}, .ok {glist (gc "B")}] := by
  classical
  rw [twoRowElement, app, stamp_node, decls_cons, List.map_cons, List.map_cons, List.map_nil, stamp_a,
    semNode_one consRow (listT (tv "x")) [tv "x", listT (tv "x")] _ consRow_split rfl
      (read_one _ (by decide)) rfl,
    semCheck_two _ _ (tv "x") _ "Symbol" {gc "A"} {gc "B"} _ _ rfl
      (nonempty_var Set.univ _ _ fun _ => trivial) (nonempty_var Set.univ _ _ fun _ => trivial),
    nil_after (narrow Set.univ (tv "x") {gc "A"}) "A" rfl,
    nil_after (narrow Set.univ (tv "x") {gc "B"}) "B" rfl]
  rfl

/-- `(Box 1)` and `(Box Z)`, where `Box` has a row for numbers and one for strings. -/
def boxOne : Atom := app "Box" [num 1]
def boxZ : Atom := app "Box" [.symbol "Z"]

theorem semNode_box (args : List Stamp) (h : args.length = 1) :
    semNode (decls "Box") args = ⟨"Expression",
      semCheck boxNumber (tc "Box") [tc "Number"] args Set.univ ++
        semCheck boxString (tc "Box") [tc "String"] args Set.univ⟩ := by
  rw [decls_box]
  simp [semNode, readRows, boxNumber, boxString, arrow, IsFun, prodSets, semApp, arrowSplit, h,
    undefinedTy, tc]

/-- **Negative control, a head with two declarations**: `(Box 1)` meets the row
for numbers and fails the row for strings, so it has an answer and an error. -/
theorem head_two_rows :
    (stamp decls boxOne).typs = [.ok {gc "Box"}, .err (inst boxString)] := by
  classical
  rw [boxOne, app, stamp_node, List.map_cons, List.map_nil, stamp_num, semNode_box _ rfl]
  simp only []
  rw [semCheck_one _ _ (tc "Number") _ "Grounded" {gc "Number"} _ _ rfl,
    semCheck_one _ _ (tc "String") _ "Grounded" {gc "Number"} _ _ rfl]
  have h1 : (narrow Set.univ (tc "Number") {gc "Number"}).Nonempty := ⟨fun _ => default, trivial, rfl⟩
  have h2 : ¬ (narrow Set.univ (tc "String") {gc "Number"}).Nonempty := by
    rintro ⟨θ, -, h⟩
    simp [tc, gc] at h
  rw [if_pos h1, if_neg h2, semCheck_end, range_const _ _ h1]
  rfl

/-- `(Box Z)` fails both rows: two errors, and `get-type` answers nothing. -/
theorem head_two_rows_fail :
    (stamp decls boxZ).typs = [.err (inst boxNumber), .err (inst boxString)] := by
  classical
  rw [boxZ, app, stamp_node, List.map_cons, List.map_nil,
    stamp_const "Z" "Nat" decls_zero (by decide), semNode_box _ rfl]
  simp only []
  rw [semCheck_one _ _ (tc "Number") _ "Symbol" {gc "Nat"} _ _ rfl,
    semCheck_one _ _ (tc "String") _ "Symbol" {gc "Nat"} _ _ rfl]
  have h1 : ¬ (narrow Set.univ (tc "Number") {gc "Nat"}).Nonempty := by
    rintro ⟨θ, -, h⟩
    simp [tc, gc] at h
  have h2 : ¬ (narrow Set.univ (tc "String") {gc "Nat"}).Nonempty := by
    rintro ⟨θ, -, h⟩
    simp [tc, gc] at h
  rw [if_neg h1, if_neg h2]
  rfl

/-- `(Wrap a)` and `(Wrap 1)`, where `Wrap`'s range does not mention its parameter. -/
def wrapA : Atom := app "Wrap" [.symbol "a"]
def wrapOne : Atom := app "Wrap" [num 1]

/-- **Negative control, a parameter the range does not fix**: `(Wrap a)` has the
answer `W` twice, one for each declaration of `a`, so a stamp is a list with
multiplicity, not a set of types. -/
theorem unfixed_parameter : (stamp decls wrapA).typs = [.ok {gc "W"}, .ok {gc "W"}] := by
  classical
  rw [wrapA, app, stamp_node, decls_wrap, List.map_cons, List.map_nil, stamp_a,
    semNode_one wrapRow (tc "W") [tv "y"] _ wrapRow_split rfl (read_one _ (by decide)) rfl]
  have h1 : (narrow Set.univ (tv "y") {gc "A"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  have h2 : (narrow Set.univ (tv "y") {gc "B"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  rw [semCheck_two _ _ (tv "y") _ "Symbol" {gc "A"} {gc "B"} _ _ rfl h1 h2, semCheck_end, semCheck_end,
    range_const _ _ h1, range_const _ _ h2]
  rfl

theorem unfixed_parameter_one : (stamp decls wrapOne).typs = [.ok {gc "W"}] := by
  classical
  rw [wrapOne, app, stamp_node, decls_wrap, List.map_cons, List.map_nil, stamp_num,
    semNode_one wrapRow (tc "W") [tv "y"] _ wrapRow_split rfl (read_one _ (by decide)) rfl,
    semCheck_one _ _ (tv "y") _ "Grounded" {gc "Number"} _ _ rfl]
  have h1 : (narrow Set.univ (tv "y") {gc "Number"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  rw [if_pos h1, semCheck_end, range_const _ _ h1]

/-- `(Ph 1)`, where a variable of `Ph`'s range is fixed by no parameter. -/
def phOne : Atom := app "Ph" [num 1]

/-- **Negative control, a range variable no parameter fixes**: the stamp's one
typing allows every instance `(Ph T)`, so a stamp is a typing with variables,
not one ground type, and is read with fresh variables. -/
theorem unfixed_range :
    (stamp decls phOne).typs = [.ok {T | ∃ U : Ty Empty, T = .app [.sym "Ph", U]}] := by
  classical
  rw [phOne, app, stamp_node, decls_ph, List.map_cons, List.map_nil, stamp_num,
    semNode_one phRow (.app [.sym "Ph", tv "w"]) [tv "v"] _ phRow_split rfl (read_one _ (by decide)) rfl,
    semCheck_one _ _ (tv "v") _ "Grounded" {gc "Number"} _ _ rfl]
  have h1 : (narrow Set.univ (tv "v") {gc "Number"}).Nonempty := nonempty_var _ _ _ fun _ => trivial
  have hset : {T | ∃ θ ∈ narrow Set.univ (tv "v") {gc "Number"},
      (Ty.app [.sym "Ph", tv "w"]).bind θ = T} = {T | ∃ U : Ty Empty, T = .app [.sym "Ph", U]} := by
    ext T
    constructor
    · rintro ⟨θ, -, rfl⟩
      exact ⟨θ "w", by simp only [tv, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym, Ty.bind_var']⟩
    · rintro ⟨U, rfl⟩
      refine ⟨fun x => if x = "w" then U else gc "Number", ⟨trivial, ?_⟩, ?_⟩
      · show (if "v" = "w" then U else gc "Number") ∈ ({gc "Number"} : Set (Ty Empty))
        simp
      · simp only [tv, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym, Ty.bind_var', if_true]
  rw [if_pos h1, semCheck_end, hset]

/-- **Negative control, address reuse**: an entry kept for `Z` at address `0`
of arena `1`; the arena is reset and the address reused for `Leaf`. Without
the epoch the entry would answer `Z` for `Leaf`; the epoch-checked lookup
misses. -/
theorem unvalidated_reuse :
    let H₀ : Heap ℕ := ⟨fun _ => none, fun _ => 0⟩
    let H₁ := H₀.step (.alloc 0 (.symbol "Z") 1)
    let m : AddrMemo ℕ Atom := Function.update (fun _ => none) 0 (some (1, H₁.epoch 1, .symbol "Z"))
    let H₂ := H₁.run [.reset 1, .alloc 0 (.symbol "Leaf") 1]
    H₂.cell 0 = some (.symbol "Leaf", 1) ∧ m 0 = some (1, 0, .symbol "Z") ∧ lookupAt H₂ m 0 = none ∧
      Sound H₂ id m := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply sound_run
  apply sound_record (sound_empty _ _)
  rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping
