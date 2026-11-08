import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContracts

/-!
# Controls: `Atom` inside compound types

The runtime typing draft gives `(: wide (Index Atom Atom))` and `(: f (-> (Index $a $a) $a $a Bool))`
and asks that `(f wide 1 "s")` not succeed by setting `$a = Atom`, in every argument order. Here
every value is an `Atom` (a nominal fact with a variable pattern), `wide` is declared
`Index Atom Atom` and nothing else, and helpers may not take a type that writes `Atom`.

* `wide_meets_written_index`: `wide` meets a written requirement `Index Atom Atom`.
* `wide_refused_at_parameter_index`: it does not meet `Index $a $a`; with improper helpers it would
  (`wide_admitted_if_improper`).
* `mixed_refused_every_order`: `(f wide 1 "s")` is refused in every order of its arguments; with
  improper helpers it would be admitted (`mixed_admitted_if_improper`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsAtom

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Logic.ConstraintTypes renaming Tree → VTree
open Mettapedia.Logic.ConstraintTypes.SymbolicTypes (Expr Closed)
open TypingFirings

inductive Sym where
  | number (n : Nat)
  | text (s : String)
  | bool (b : Bool)
  | wide

def valueArity : Sym → Nat := fun _ => 0

inductive Name where
  | number | string | bool | atom
  deriving DecidableEq

inductive Con where
  | index
  deriving DecidableEq

def typeArity : Con → Nat := fun _ => 2

abbrev Ty := Closed Name Con typeArity
abbrev Value := VTree Sym valueArity

def leaf (s : Sym) : Value := .node s Fin.elim0

def index {X : Type} (x y : Expr X Name Con typeArity) : Expr X Name Con typeArity :=
  .app .index fun i => if i.val = 0 then x else y

def rules (s : Sym) : List (ConstructorTyping.Rule Empty Name Con typeArity (valueArity s)) :=
  match s with
  | .number _ => [⟨Fin.elim0, .closed .number⟩]
  | .text _ => [⟨Fin.elim0, .closed .string⟩]
  | .bool _ => [⟨Fin.elim0, .closed .bool⟩]
  | .wide => []

/-- Every value is an `Atom`. -/
def atomFact : DeclarationTyping.Fact Unit Empty Name Con Sym typeArity valueArity where
  pattern := .var ()
  type := .closed .atom

/-- `(: wide (Index Atom Atom))`. -/
def wideFact : DeclarationTyping.Fact Unit Empty Name Con Sym typeArity valueArity where
  pattern := .node .wide Fin.elim0
  type := index (.closed .atom) (.closed .atom)

def decls : DeclarationTyping.Declarations Unit Unit Empty Name Con Sym typeArity valueArity where
  childContext _ _ _ := ()
  constructors _ := rules
  facts _ := [atomFact, wideFact]

def isAtom (q : Name) : Prop := q = .atom

def nothing (_ : Name) : Prop := False

theorem atom_typed (v : Value) : DeclarationTyping.HasType decls () v (.closed .atom) :=
  .nominal atomFact List.mem_cons_self (fun _ => v) rfl Empty.elim (fun _ present => by cases present)

theorem wide_typed : DeclarationTyping.HasType decls () (leaf .wide) (index (.closed .atom) (.closed .atom)) := by
  have typed : DeclarationTyping.HasType decls () (leaf .wide) (wideFact.type.substitute Empty.elim) :=
    .nominal wideFact (List.mem_cons_of_mem _ List.mem_cons_self) (fun _ => leaf .wide)
      (congrArg (Mettapedia.Logic.ConstraintTypes.Tree.node Sym.wide) (funext fun i => i.elim0))
      Empty.elim (fun _ present => by cases present)
  rwa [SymbolicTypes.closed_substitute] at typed

theorem index_substitute {X Y : Type} (x y : Expr X Name Con typeArity)
    (θ : X → Expr Y Name Con typeArity) :
    (index x y).substitute θ = index (x.substitute θ) (y.substitute θ) := by
  show TypeExpr.app Con.index (fun i => (if i.val = 0 then x else y).substitute θ) =
    TypeExpr.app Con.index (fun i => if i.val = 0 then x.substitute θ else y.substitute θ)
  congr 1
  funext i
  split <;> rfl

theorem wide_typed_at (θ : Unit → Ty) (atom : θ () = .closed .atom) :
    DeclarationTyping.HasType decls () (leaf .wide)
      ((index (.parameter ()) (.parameter ())).substitute θ) := by
  rw [index_substitute]
  show DeclarationTyping.HasType decls () (leaf .wide) (index (θ ()) (θ ()))
  rw [atom]
  exact wide_typed

theorem wide_typed_written (θ : Unit → Ty) :
    DeclarationTyping.HasType decls () (leaf .wide)
      ((index (.closed .atom) (.closed .atom) : Expr Unit Name Con typeArity).substitute θ) := by
  rw [index_substitute]
  exact wide_typed

theorem number_typed (n : Nat) : DeclarationTyping.HasType decls () (leaf (.number n)) (.closed .number) :=
  DeclarationTyping.HasType.constructor (declarations := decls) (context := ()) (symbol := .number n)
    (children := Fin.elim0) ⟨Fin.elim0, .closed .number⟩ (by simp [decls, rules]) Empty.elim
    (fun i => i.elim0)

theorem bool_typed (b : Bool) : DeclarationTyping.HasType decls () (leaf (.bool b)) (.closed .bool) :=
  DeclarationTyping.HasType.constructor (declarations := decls) (context := ()) (symbol := .bool b)
    (children := Fin.elim0) ⟨Fin.elim0, .closed .bool⟩ (by simp [decls, rules]) Empty.elim
    (fun i => i.elim0)

theorem not_wide_pattern (s : Sym) (different : s ≠ .wide) (matched : Unit → Value) :
    wideFact.pattern.evaluate matched ≠ .node s Fin.elim0 := by
  intro same
  exact different (Mettapedia.Logic.ConstraintTypes.Tree.node.inj same).1.symm

theorem types_of_number (n : Nat) (τ : Ty) (typed : DeclarationTyping.HasType decls () (leaf (.number n)) τ) :
    τ = .closed .number ∨ τ = .closed .atom := by
  rcases (DeclarationTyping.hasType_node_iff decls () (.number n) Fin.elim0 τ).1 typed with
    ⟨rule, present, _, rfl, _⟩ | ⟨fact, present, matched, equal, _, _, rfl⟩
  · simp only [decls, rules, List.mem_singleton] at present
    subst present
    exact .inl rfl
  · simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact .inr rfl
    · exact absurd equal (not_wide_pattern _ (by simp) matched)

theorem types_of_text (s : String) (τ : Ty) (typed : DeclarationTyping.HasType decls () (leaf (.text s)) τ) :
    τ = .closed .string ∨ τ = .closed .atom := by
  rcases (DeclarationTyping.hasType_node_iff decls () (.text s) Fin.elim0 τ).1 typed with
    ⟨rule, present, _, rfl, _⟩ | ⟨fact, present, matched, equal, _, _, rfl⟩
  · simp only [decls, rules, List.mem_singleton] at present
    subst present
    exact .inl rfl
  · simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact .inr rfl
    · exact absurd equal (not_wide_pattern _ (by simp) matched)

theorem types_of_wide (τ : Ty) (typed : DeclarationTyping.HasType decls () (leaf .wide) τ) :
    τ = .closed .atom ∨ τ = index (.closed .atom) (.closed .atom) := by
  rcases (DeclarationTyping.hasType_node_iff decls () .wide Fin.elim0 τ).1 typed with
    ⟨rule, present, _⟩ | ⟨fact, present, _, _, _, _, rfl⟩
  · simp [decls, rules] at present
  · simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact .inl rfl
    · exact .inr (SymbolicTypes.closed_substitute _ _)

theorem atom_improper (θ : Ty) (proper : Proper isAtom θ) : θ ≠ .closed .atom := by
  rintro rfl
  exact proper .atom (List.mem_singleton.mpr rfl) rfl

/-- A type `Index θ θ` written by a helper is never the declared `Index Atom Atom`. -/
theorem index_improper (θ : Ty) (proper : Proper isAtom θ) :
    index θ θ ≠ index (.closed .atom) (.closed .atom) := by
  intro same
  simp only [index, TypeExpr.app.injEq, heq_eq_eq, true_and] at same
  exact atom_improper θ proper (by simpa using congrFun same ⟨0, by decide⟩)

theorem proper_closed (reserved : Name → Prop) {q : Name} (allowed : ¬ reserved q) :
    Proper reserved (.closed q : Ty) := by
  intro q' written
  simp only [names, List.mem_singleton] at written
  subst written
  exact allowed

abbrev T := Term Unit Nat Nat Name Con Sym typeArity valueArity
abbrev Pt (reserved : Name → Prop) := Point Nat Nat Name Con Sym typeArity valueArity reserved

def label : Nat → T := fun _ => .yes

def start : Configuration T Nat := ⟨[], ∅⟩

def pointAt (reserved : Name → Prop) (q : Name) (allowed : ¬ reserved q) : Pt reserved :=
  ⟨fun _ => leaf (.number 0), fun _ => .closed q, fun _ => proper_closed reserved allowed⟩

theorem start_solvable (reserved : Name → Prop) (q : Name) (allowed : ¬ reserved q) :
    ∃ ρ : Pt reserved, Holds decls reserved ρ start.equations :=
  ⟨pointAt reserved q allowed, fun _ member => by cases member⟩

def ν : Unit → Nat := fun _ => 0

theorem ν_injective : Function.Injective ν := fun _ _ _ => rfl

/-! ## `wide` against a written index and a parameter index -/

/-- `(: k (-> (Index Atom Atom) Bool))`. -/
def kSig : Signature Unit Name Con typeArity 1 := ⟨fun _ => index (.closed .atom) (.closed .atom), .closed .bool⟩

/-- `(: h (-> (Index $a $a) Bool))`. -/
def hSig : Signature Unit Name Con typeArity 1 := ⟨fun _ => index (.parameter ()) (.parameter ()), .closed .bool⟩

def oneCall (reserved : Name → Prop) (sig : Signature Unit Name Con typeArity 1) :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Con Sym typeArity valueArity reserved) Nat :=
  callFiring ν sig () () (fun _ => ofTree (leaf .wide)) (ofTree (leaf (.bool true)))

theorem wide_meets_written_index :
    (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start) (oneCall isAtom kSig) := by
  rw [oneCall, closed_call_admits_iff label start (start_solvable isAtom .number (by simp [isAtom]))
    ν_injective (avoids_nil ν)]
  exact ⟨fun _ => .closed .number, fun _ => proper_closed isAtom (by simp [isAtom]),
    fun _ => wide_typed_written _, bool_typed true⟩

theorem wide_refused_at_parameter_index :
    ¬ (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start) (oneCall isAtom hSig) := by
  rw [oneCall, closed_call_admits_iff label start (start_solvable isAtom .number (by simp [isAtom]))
    ν_injective (avoids_nil ν)]
  rintro ⟨θ, proper, inputs, _⟩
  have reading : (hSig.argument 0).substitute θ = index (θ ()) (θ ()) := index_substitute _ _ θ
  rcases types_of_wide _ (inputs 0) with wrong | wrong
  · cases wrong
  · rw [reading] at wrong
    exact index_improper (θ ()) (proper ()) wrong

theorem wide_admitted_if_improper :
    (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start) (oneCall nothing hSig) := by
  rw [oneCall, closed_call_admits_iff label start (start_solvable nothing .number id)
    ν_injective (avoids_nil ν)]
  exact ⟨fun _ => .closed .atom, fun _ _ _ impossible => impossible, fun _ => wide_typed_at _ rfl, bool_typed true⟩

/-! ## `(f wide 1 "s")` in every order -/

/-- `(: f (-> (Index $a $a) $a $a Bool))`. -/
def fSig : Signature Unit Name Con typeArity 3 :=
  ⟨fun i => if i.val = 0 then index (.parameter ()) (.parameter ()) else .parameter (), .closed .bool⟩

def fArgs : Fin 3 → Value := ![leaf .wide, leaf (.number 1), leaf (.text "s")]

def fCall (reserved : Name → Prop) (e : Fin 3 ≃ Fin 3) :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Con Sym typeArity valueArity reserved) Nat :=
  callFiring ν (permuteInputs fSig e) () () (fun i => ofTree ((fArgs ∘ e) i)) (ofTree (leaf (.bool true)))

theorem mixed_refused_every_order (e : Fin 3 ≃ Fin 3) :
    ¬ (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start) (fCall isAtom e) := by
  rw [fCall, closed_call_admits_iff label start (start_solvable isAtom .number (by simp [isAtom]))
    ν_injective (avoids_nil ν), joint_permute]
  rintro ⟨θ, proper, inputs, _⟩
  have first := types_of_number 1 _ (inputs 1)
  have second := types_of_text "s" _ (inputs 2)
  have improper := atom_improper (θ ()) (proper ())
  change θ () = _ ∨ θ () = _ at first second
  rcases first with first | first
  · rcases second with second | second
    · rw [first] at second
      cases second
    · exact improper second
  · exact improper first

theorem mixed_admitted_if_improper (e : Fin 3 ≃ Fin 3) :
    (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start) (fCall nothing e) := by
  rw [fCall, closed_call_admits_iff label start (start_solvable nothing .number id)
    ν_injective (avoids_nil ν), joint_permute]
  refine ⟨fun _ => .closed .atom, fun _ _ _ impossible => impossible, ?_, bool_typed true⟩
  intro i
  fin_cases i
  · exact wide_typed_at _ rfl
  · exact atom_typed _
  · exact atom_typed _

#print axioms types_of_wide
#print axioms wide_meets_written_index
#print axioms wide_refused_at_parameter_index
#print axioms wide_admitted_if_improper
#print axioms mixed_refused_every_order
#print axioms mixed_admitted_if_improper

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsAtom
