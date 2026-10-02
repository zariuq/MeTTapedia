import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerCodes
import Metatheory.SystemF.Typing
import Metatheory.SystemF.StrongReduction

/-!
# System F in the impredicative package of proposition codes

System F (Church-style terms, with separate unscoped de Bruijn indices for type and term
variables, and full β- and type-β-reduction) embeds in the package of proposition codes
over the cumulative tower. The package used has the type of codes `prop`, the decoder
`holds`, implication, and one quantifier `allProp : (prop → prop) → prop` whose carrier is
the type of codes itself; it has no equation codes. A type becomes a code and a term
becomes a proof:

* a type variable is a variable of type `prop`, `σ → τ` is `imp σ τ`, and `∀ α. τ` is
  `allProp (λ α. τ)`;
* a term variable is a variable of type `holds σ`, both abstractions are abstractions (the
  annotation of a term abstraction is dropped), and both applications are applications.

The scoped telescope of the package interleaves the two sorts of variables. A layout, a
list of booleans read innermost first, records for each variable of the telescope whether
it is a type variable (`true`) or a term variable (`false`); the `j`-th variable of a sort
is found by counting the entries of that sort. A variable that the layout does not bind is
read as `allProp (λ p. p)`, the code of `∀ α. α`. With this reading the translation of
every type is a code, so neither well-formedness of types nor the number of type variables
in scope enters the statements below; the only condition is that the layout carry the term
context.

Shifting and substitution of System F commute with the translation: each is realized by
every scoped renaming or substitution that acts the same way on the variables of the
layout, a property stable under binders. A β-step and a type-β-step each become one β-step,
congruence steps become congruence steps, and no root computation is used, so full
reduction is simulated step by step.

A term of type `τ` in the term context `Γ` becomes, in the context of any layout carrying
`Γ`, a proof of `holds τ`. The decoding steps `holds (imp p q) ⟶ Π (_ : holds p). holds q`
and `holds (allProp f) ⟶ Π (x : prop). holds (f x)` enter by the typed root-computation
rule, both sides in the lowest universe after cumulativity, and a β-step under the
quantifier's binder turns `holds ((λ α. τ) x)` back into `holds τ`.

Hence strong normalization of the package's reduction on typed terms implies strong
normalization of System F.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Metatheory.SystemF

namespace SystemF

/-! ## The code package -/

/-- The name of the quantifier over codes. -/
def allProp : DeclName := `SystemF.allProp

/-- The name of the type of codes. -/
def propName : DeclName := `SystemF.prop

/-- The name of the decoder. -/
def holdsName : DeclName := `SystemF.holds

/-- The name of implication. -/
def impName : DeclName := `SystemF.imp

/-- The proposition codes of System F over the tower of a level order: a type `prop` of
codes, the decoder `holds`, implication, and one quantifier `allProp` whose carrier is `prop`
itself. Proofs live in the lowest universe. There are no equation codes. -/
def codesOver (Lev : Type) [UniverseLevel.LevelOrder Lev] : Codes (LevelTower.Head Lev) where
  proofs := .sort LevelTower.zero
  prop := propName
  holds := holdsName
  imp := impName
  quantifiers := fun name => [(allProp, .const propName)].lookup name
  equations := fun _ => none
  identity := false

/-- The rule package `(codesOver Lev).extend (LevelTower.rules Lev)`: the cumulative tower
over a level order, extended by the System F codes and their decoding. -/
abbrev rulesOver (Lev : Type) [UniverseLevel.LevelOrder Lev] : Rules (LevelTower.Head Lev) :=
  (codesOver Lev).extend (LevelTower.rules Lev)

/-- The proposition codes of System F over the tower with natural-number levels. -/
abbrev codes : Codes Tower.Head := codesOver Nat

/-- The rule package `codes.extend Tower.rules`: the cumulative tower extended by the
System F codes and their decoding. -/
abbrev rules : Rules Tower.Head := rulesOver Nat

/-- The quantifier applied to a family of codes. -/
abbrev allOf {n : Nat} (f : Tower.Tm n) : Tower.Tm n := .app (.const allProp) f

/-- The code of `∀ α. α`. It stands for every variable a layout does not bind. -/
def bottom {n : Nat} : Tower.Tm n := allOf (.lam (.var 0))

@[simp] theorem rename_bottom {n m : Nat} (ρ : Ren n m) :
    rename ρ (bottom : Tower.Tm n) = bottom := rfl

@[simp] theorem subst_bottom {n m : Nat} (σ : Sub Tower.Head n m) :
    subst σ (bottom : Tower.Tm n) = bottom := rfl

/-! ## Layouts and the translation -/

/-- The scoped variable of the layout `L` for the `j`-th variable of kind `kind` (`true`
for type variables, `false` for term variables), both counted innermost first; `bottom`
when `L` has no such variable. -/
def varOf (kind : Bool) : (L : List Bool) → Nat → Tower.Tm L.length
  | [], _ => bottom
  | b :: L, j =>
      if b = kind then
        match j with
        | 0 => .var 0
        | j + 1 => rename wk (varOf kind L j)
      else rename wk (varOf kind L j)

@[simp] theorem varOf_nil (kind : Bool) (j : Nat) : varOf kind [] j = bottom := rfl

@[simp] theorem varOf_self_zero (kind : Bool) (L : List Bool) :
    varOf kind (kind :: L) 0 = .var 0 := by
  simp [varOf]

@[simp] theorem varOf_self_succ (kind : Bool) (L : List Bool) (j : Nat) :
    varOf kind (kind :: L) (j + 1) = rename wk (varOf kind L j) := by
  simp [varOf]

theorem varOf_other {kind b : Bool} (other : b ≠ kind) (L : List Bool) (j : Nat) :
    varOf kind (b :: L) j = rename wk (varOf kind L j) := by
  simp [varOf, other]

/-- The code of a System F type in the layout `L`: type variables are variables of `L`,
arrows are implications, and `∀ α. τ` quantifies over the code family `λ α. τ`. -/
def trTy : (L : List Bool) → Ty → Tower.Tm L.length
  | L, .tvar j => varOf true L j
  | L, .arr τ σ => codes.impOf (trTy L τ) (trTy L σ)
  | L, .all τ => allOf (.lam (trTy (true :: L) τ))

/-- The proof term of a System F term in the layout `L`. Both abstractions become
abstractions (the annotation of a term abstraction is dropped) and both applications
become applications. -/
def trTm : (L : List Bool) → Term → Tower.Tm L.length
  | L, .var i => varOf false L i
  | L, .lam _ M => .lam (trTm (false :: L) M)
  | L, .app M N => .app (trTm L M) (trTm L N)
  | L, .tlam M => .lam (trTm (true :: L) M)
  | L, .tapp M σ => .app (trTm L M) (trTy L σ)

/-! ## Commutation with the operations of System F

A scoped substitution `S` realizes a System F operation when it does so on the variables
of the layout. Each property below is stable under passing a binder, which is what the
inductions on types and terms need. -/

/-- The index map of the shifts `shiftTyUp d c` and `shiftTermUp d c` on variables. -/
def shiftIdx (d c j : Nat) : Nat := if j < c then j else j + d

theorem shiftIdx_zero (c : Nat) : shiftIdx 0 c = fun j => j := by
  funext j
  unfold shiftIdx
  split <;> rfl

theorem shiftIdx_succ_zero (d c : Nat) : shiftIdx d (c + 1) 0 = 0 :=
  if_pos (Nat.succ_pos c)

theorem shiftIdx_succ_succ (d c j : Nat) : shiftIdx d (c + 1) (j + 1) = shiftIdx d c j + 1 := by
  unfold shiftIdx
  by_cases h : j < c
  · rw [if_pos (Nat.succ_lt_succ h), if_pos h]
  · rw [if_neg (fun h' => h (Nat.lt_of_succ_lt_succ h')), if_neg h]
    omega

theorem shiftTyUp_tvar (d c j : Nat) : Ty.shiftTyUp d c (.tvar j) = .tvar (shiftIdx d c j) := by
  unfold Ty.shiftTyUp shiftIdx
  split <;> rfl

theorem shiftTermUp_var (d c i : Nat) :
    Term.shiftTermUp d c (.var i) = .var (shiftIdx d c i) := by
  unfold Term.shiftTermUp shiftIdx
  split <;> rfl

theorem substTy_tvar_succ (k j : Nat) (σ : Ty) :
    Ty.substTy (k + 1) (Ty.shiftTyUp 1 0 σ) (.tvar (j + 1)) =
      Ty.shiftTyUp 1 0 (Ty.substTy k σ (.tvar j)) := by
  simp only [Ty.substTy]
  by_cases lt : j < k
  · rw [if_pos (Nat.succ_lt_succ lt), if_pos lt, shiftTyUp_tvar]
    rfl
  · rw [if_neg (fun h => lt (Nat.lt_of_succ_lt_succ h)), if_neg lt]
    by_cases eq : j = k
    · rw [if_pos (congrArg (· + 1) eq), if_pos eq]
    · rw [if_neg (fun h => eq (Nat.succ.inj h)), if_neg eq, shiftTyUp_tvar]
      unfold shiftIdx
      rw [if_neg (Nat.not_lt_zero _)]
      congr 1
      omega

theorem substTerm_var_succ (k i : Nat) (N : Term) :
    Term.substTerm (k + 1) (Term.shiftTermUp 1 0 N) (.var (i + 1)) =
      Term.shiftTermUp 1 0 (Term.substTerm k N (.var i)) := by
  simp only [Term.substTerm]
  by_cases lt : i < k
  · rw [if_pos (Nat.succ_lt_succ lt), if_pos lt, shiftTermUp_var]
    rfl
  · rw [if_neg (fun h => lt (Nat.lt_of_succ_lt_succ h)), if_neg lt]
    by_cases eq : i = k
    · rw [if_pos (congrArg (· + 1) eq), if_pos eq]
    · rw [if_neg (fun h => eq (Nat.succ.inj h)), if_neg eq, shiftTermUp_var]
      unfold shiftIdx
      rw [if_neg (Nat.not_lt_zero _)]
      congr 1
      omega

theorem substTerm_var_shiftType (k i : Nat) (N : Term) :
    Term.substTerm k (Term.shiftTypeInTerm 1 0 N) (.var i) =
      Term.shiftTypeInTerm 1 0 (Term.substTerm k N (.var i)) := by
  simp only [Term.substTerm]
  by_cases lt : i < k
  · rw [if_pos lt, if_pos lt]
    rfl
  · rw [if_neg lt, if_neg lt]
    by_cases eq : i = k
    · rw [if_pos eq, if_pos eq]
    · rw [if_neg eq, if_neg eq]
      rfl

/-- `S` moves the variables of kind `kind` of `L` to those of `L'` along the index map
`f`. -/
def Moves (kind : Bool) (f : Nat → Nat) (L L' : List Bool)
    (S : Sub Tower.Head L.length L'.length) : Prop :=
  ∀ j, subst S (varOf kind L j) = varOf kind L' (f j)

namespace Moves

variable {kind : Bool} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length}

theorem liftSame {d c : Nat} (moves : Moves kind (shiftIdx d c) L L' S) :
    Moves kind (shiftIdx d (c + 1)) (kind :: L) (kind :: L') (liftSub S) := by
  intro j
  cases j with
  | zero => rw [shiftIdx_succ_zero, varOf_self_zero, varOf_self_zero]; rfl
  | succ j =>
      rw [shiftIdx_succ_succ, varOf_self_succ, varOf_self_succ, subst_liftSub_wk, moves j]

theorem liftOther {f : Nat → Nat} {b : Bool} (moves : Moves kind f L L' S) (other : b ≠ kind) :
    Moves kind f (b :: L) (b :: L') (liftSub S) := by
  intro j
  rw [varOf_other other, varOf_other other, subst_liftSub_wk, moves j]

theorem liftId (moves : Moves kind (fun j => j) L L' S) (b : Bool) :
    Moves kind (fun j => j) (b :: L) (b :: L') (liftSub S) := by
  by_cases same : b = kind
  · subst same
    rw [← shiftIdx_zero 0] at moves
    have lifted := moves.liftSame
    rwa [shiftIdx_zero] at lifted
  · exact moves.liftOther same

/-- Weakening past a variable of the same kind moves every variable one place out. -/
theorem wkSame (kind : Bool) (L : List Bool) :
    Moves kind (shiftIdx 1 0) L (kind :: L) (renSub wk) := by
  intro j
  rw [subst_renSub]
  unfold shiftIdx
  rw [if_neg (Nat.not_lt_zero _), varOf_self_succ]

/-- Weakening past a variable of the other kind fixes the variables of this kind. -/
theorem wkOther {kind b : Bool} (other : b ≠ kind) (L : List Bool) :
    Moves kind (fun j => j) L (b :: L) (renSub wk) := by
  intro j
  rw [subst_renSub, varOf_other other]

end Moves

/-- Shifting a type is realized by any substitution moving its type variables along the
shift. -/
theorem subst_trTy_shift {d : Nat} (τ : Ty) :
    ∀ {c : Nat} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      Moves true (shiftIdx d c) L L' S → subst S (trTy L τ) = trTy L' (Ty.shiftTyUp d c τ) := by
  induction τ with
  | tvar j =>
      intro c L L' S moves
      rw [shiftTyUp_tvar]
      exact moves j
  | arr τ σ ihτ ihσ =>
      intro c L L' S moves
      simp only [trTy, Ty.shiftTyUp, subst, ihτ moves, ihσ moves]
  | all τ ih =>
      intro c L L' S moves
      simp only [trTy, Ty.shiftTyUp, subst, ih moves.liftSame]

/-- A substitution fixing the type variables fixes the codes of types. -/
theorem subst_trTy_fix {L L' : List Bool} {S : Sub Tower.Head L.length L'.length}
    (moves : Moves true (fun j => j) L L' S) (τ : Ty) : subst S (trTy L τ) = trTy L' τ := by
  rw [← shiftIdx_zero 0] at moves
  rw [subst_trTy_shift τ moves, Ty.shiftTyUp_zero]

/-- Translating under an extra term variable is weakening. -/
theorem trTy_cons_false (L : List Bool) (τ : Ty) :
    trTy (false :: L) τ = rename wk (trTy L τ) := by
  rw [← subst_renSub, subst_trTy_fix (Moves.wkOther (by decide) L)]

/-- Translating a shifted type under an extra type variable is weakening. -/
theorem trTy_cons_true_shift (L : List Bool) (τ : Ty) :
    trTy (true :: L) (Ty.shiftTyUp 1 0 τ) = rename wk (trTy L τ) := by
  rw [← subst_renSub, subst_trTy_shift τ (Moves.wkSame true L)]

/-- Shifting the term variables of a term is realized by any substitution moving them
along the shift and fixing the type variables. -/
theorem subst_trTm_shiftTerm {d : Nat} (M : Term) :
    ∀ {c : Nat} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      Moves false (shiftIdx d c) L L' S → Moves true (fun j => j) L L' S →
        subst S (trTm L M) = trTm L' (Term.shiftTermUp d c M) := by
  induction M with
  | var i =>
      intro c L L' S terms _
      rw [shiftTermUp_var]
      exact terms i
  | lam τ M ih =>
      intro c L L' S terms types
      simp only [trTm, Term.shiftTermUp, subst, ih terms.liftSame (types.liftId false)]
  | app M N ihM ihN =>
      intro c L L' S terms types
      simp only [trTm, Term.shiftTermUp, subst, ihM terms types, ihN terms types]
  | tlam M ih =>
      intro c L L' S terms types
      simp only [trTm, Term.shiftTermUp, subst,
        ih (terms.liftOther (by decide)) (types.liftId true)]
  | tapp M σ ih =>
      intro c L L' S terms types
      simp only [trTm, Term.shiftTermUp, subst, ih terms types, subst_trTy_fix types]

/-- Shifting the type variables of a term is realized by any substitution moving them
along the shift and fixing the term variables. -/
theorem subst_trTm_shiftType {d : Nat} (M : Term) :
    ∀ {c : Nat} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      Moves true (shiftIdx d c) L L' S → Moves false (fun j => j) L L' S →
        subst S (trTm L M) = trTm L' (Term.shiftTypeInTerm d c M) := by
  induction M with
  | var i =>
      intro c L L' S _ terms
      exact terms i
  | lam τ M ih =>
      intro c L L' S types terms
      simp only [trTm, Term.shiftTypeInTerm, subst,
        ih (types.liftOther (by decide)) (terms.liftId false)]
  | app M N ihM ihN =>
      intro c L L' S types terms
      simp only [trTm, Term.shiftTypeInTerm, subst, ihM types terms, ihN types terms]
  | tlam M ih =>
      intro c L L' S types terms
      simp only [trTm, Term.shiftTypeInTerm, subst, ih types.liftSame (terms.liftId true)]
  | tapp M σ ih =>
      intro c L L' S types terms
      simp only [trTm, Term.shiftTypeInTerm, subst, ih types terms, subst_trTy_shift σ types]

/-- Translating a shifted term under an extra term variable is weakening. -/
theorem trTm_cons_false_shift (L : List Bool) (M : Term) :
    trTm (false :: L) (Term.shiftTermUp 1 0 M) = rename wk (trTm L M) := by
  rw [← subst_renSub,
    subst_trTm_shiftTerm M (Moves.wkSame false L) (Moves.wkOther (by decide) L)]

/-- Translating a term with shifted types under an extra type variable is weakening. -/
theorem trTm_cons_true_shift (L : List Bool) (M : Term) :
    trTm (true :: L) (Term.shiftTypeInTerm 1 0 M) = rename wk (trTm L M) := by
  rw [← subst_renSub,
    subst_trTm_shiftType M (Moves.wkSame true L) (Moves.wkOther (by decide) L)]

/-- `S` substitutes `σ` for the type variable `k` of `L`. -/
def SubstitutesType (k : Nat) (σ : Ty) (L L' : List Bool)
    (S : Sub Tower.Head L.length L'.length) : Prop :=
  ∀ j, subst S (varOf true L j) = trTy L' (Ty.substTy k σ (.tvar j))

theorem SubstitutesType.liftTrue {k : Nat} {σ : Ty} {L L' : List Bool}
    {S : Sub Tower.Head L.length L'.length} (substitutes : SubstitutesType k σ L L' S) :
    SubstitutesType (k + 1) (Ty.shiftTyUp 1 0 σ) (true :: L) (true :: L') (liftSub S) := by
  intro j
  cases j with
  | zero =>
      rw [varOf_self_zero]
      simp only [Ty.substTy, if_pos (Nat.succ_pos k)]
      rfl
  | succ j =>
      rw [varOf_self_succ, subst_liftSub_wk, substitutes j, substTy_tvar_succ,
        trTy_cons_true_shift]

theorem SubstitutesType.liftFalse {k : Nat} {σ : Ty} {L L' : List Bool}
    {S : Sub Tower.Head L.length L'.length} (substitutes : SubstitutesType k σ L L' S) :
    SubstitutesType k σ (false :: L) (false :: L') (liftSub S) := by
  intro j
  rw [varOf_other (by decide), subst_liftSub_wk, substitutes j, trTy_cons_false]

/-- Substituting for a type variable is realized by any substitution doing so on the
type variables of the layout. -/
theorem subst_trTy_substTy (τ : Ty) :
    ∀ {k : Nat} {σ : Ty} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      SubstitutesType k σ L L' S → subst S (trTy L τ) = trTy L' (Ty.substTy k σ τ) := by
  induction τ with
  | tvar j =>
      intro k σ L L' S substitutes
      exact substitutes j
  | arr τ υ ihτ ihυ =>
      intro k σ L L' S substitutes
      simp only [trTy, Ty.substTy, subst, ihτ substitutes, ihυ substitutes]
  | all τ ih =>
      intro k σ L L' S substitutes
      simp only [trTy, Ty.substTy, subst, ih substitutes.liftTrue]

/-- Opening the newest type variable at the code of `σ`. -/
theorem substitutesType_subst0 (L : List Bool) (σ : Ty) :
    SubstitutesType 0 σ (true :: L) L (subst0 (trTy L σ)) := by
  intro j
  cases j with
  | zero => rfl
  | succ j =>
      rw [varOf_self_succ]
      exact inst0_rename_wk _ _

/-- The code of an instantiated type is the instantiated code. -/
theorem trTy_substTy0 (L : List Bool) (σ τ : Ty) :
    trTy L (Ty.substTy0 σ τ) = inst0 (trTy L σ) (trTy (true :: L) τ) :=
  (subst_trTy_substTy τ (substitutesType_subst0 L σ)).symm

/-- `S` substitutes `N` for the term variable `k` of `L`. -/
def SubstitutesTerm (k : Nat) (N : Term) (L L' : List Bool)
    (S : Sub Tower.Head L.length L'.length) : Prop :=
  ∀ i, subst S (varOf false L i) = trTm L' (Term.substTerm k N (.var i))

theorem SubstitutesTerm.liftFalse {k : Nat} {N : Term} {L L' : List Bool}
    {S : Sub Tower.Head L.length L'.length} (substitutes : SubstitutesTerm k N L L' S) :
    SubstitutesTerm (k + 1) (Term.shiftTermUp 1 0 N) (false :: L) (false :: L')
      (liftSub S) := by
  intro i
  cases i with
  | zero =>
      rw [varOf_self_zero]
      simp only [Term.substTerm, if_pos (Nat.succ_pos k)]
      rfl
  | succ i =>
      rw [varOf_self_succ, subst_liftSub_wk, substitutes i, substTerm_var_succ,
        trTm_cons_false_shift]

theorem SubstitutesTerm.liftTrue {k : Nat} {N : Term} {L L' : List Bool}
    {S : Sub Tower.Head L.length L'.length} (substitutes : SubstitutesTerm k N L L' S) :
    SubstitutesTerm k (Term.shiftTypeInTerm 1 0 N) (true :: L) (true :: L') (liftSub S) := by
  intro i
  rw [varOf_other (by decide), subst_liftSub_wk, substitutes i, substTerm_var_shiftType,
    trTm_cons_true_shift]

/-- Substituting for a term variable is realized by any substitution doing so on the term
variables of the layout and fixing its type variables. -/
theorem subst_trTm_substTerm (M : Term) :
    ∀ {k : Nat} {N : Term} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      SubstitutesTerm k N L L' S → Moves true (fun j => j) L L' S →
        subst S (trTm L M) = trTm L' (Term.substTerm k N M) := by
  induction M with
  | var i =>
      intro k N L L' S substitutes _
      exact substitutes i
  | lam τ M ih =>
      intro k N L L' S substitutes types
      simp only [trTm, Term.substTerm, subst, ih substitutes.liftFalse (types.liftId false)]
  | app M M' ihM ihM' =>
      intro k N L L' S substitutes types
      simp only [trTm, Term.substTerm, subst, ihM substitutes types, ihM' substitutes types]
  | tlam M ih =>
      intro k N L L' S substitutes types
      simp only [trTm, Term.substTerm, subst, ih substitutes.liftTrue (types.liftId true)]
  | tapp M σ ih =>
      intro k N L L' S substitutes types
      simp only [trTm, Term.substTerm, subst, ih substitutes types, subst_trTy_fix types]

/-- Substituting for a type variable in a term is realized by any substitution doing so
on the type variables of the layout and fixing its term variables. -/
theorem subst_trTm_substType (M : Term) :
    ∀ {k : Nat} {σ : Ty} {L L' : List Bool} {S : Sub Tower.Head L.length L'.length},
      SubstitutesType k σ L L' S → Moves false (fun j => j) L L' S →
        subst S (trTm L M) = trTm L' (Term.substTypeInTerm k σ M) := by
  induction M with
  | var i =>
      intro k σ L L' S _ terms
      exact terms i
  | lam τ M ih =>
      intro k σ L L' S substitutes terms
      simp only [trTm, Term.substTypeInTerm, subst,
        ih substitutes.liftFalse (terms.liftId false)]
  | app M N ihM ihN =>
      intro k σ L L' S substitutes terms
      simp only [trTm, Term.substTypeInTerm, subst, ihM substitutes terms, ihN substitutes terms]
  | tlam M ih =>
      intro k σ L L' S substitutes terms
      simp only [trTm, Term.substTypeInTerm, subst, ih substitutes.liftTrue (terms.liftId true)]
  | tapp M τ ih =>
      intro k σ L L' S substitutes terms
      simp only [trTm, Term.substTypeInTerm, subst, ih substitutes terms,
        subst_trTy_substTy τ substitutes]

/-- The proof term of a β-contractum is the instantiated body. -/
theorem trTm_substTerm0 (L : List Bool) (N M : Term) :
    trTm L (Term.substTerm0 N M) = inst0 (trTm L N) (trTm (false :: L) M) := by
  refine (subst_trTm_substTerm M (L := false :: L) (S := subst0 (trTm L N)) ?_ ?_).symm
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
        rw [varOf_self_succ]
        exact inst0_rename_wk _ _
  · intro j
    rw [varOf_other (by decide)]
    exact inst0_rename_wk _ _

/-- The proof term of a type-β contractum is the body instantiated at the code. -/
theorem trTm_substTypeInTerm0 (L : List Bool) (σ : Ty) (M : Term) :
    trTm L (Term.substTypeInTerm0 σ M) = inst0 (trTy L σ) (trTm (true :: L) M) := by
  refine (subst_trTm_substType M (substitutesType_subst0 L σ) ?_).symm
  intro i
  rw [varOf_other (by decide)]
  exact inst0_rename_wk _ _

/-! ## Contexts -/

/-- The context of a layout: the type of codes for each type variable, and the decoding of
the code of its System F type for each term variable. The types of `Γ` see every type
variable of the layout, so passing a type variable shifts them back by one. A term
variable beyond `Γ` is typed by the decoding of `bottom`. -/
def ctx : (L : List Bool) → Context → Tower.Ctx L.length
  | [], _ => .nil
  | true :: L, Γ => .snoc (ctx L (Γ.map (Ty.shiftTyDown 0))) codes.propT
  | false :: L, [] => .snoc (ctx L []) (codes.holdsOf bottom)
  | false :: L, τ :: Γ => .snoc (ctx L Γ) (codes.holdsOf (trTy L τ))

/-- The layout `L` carries the System F term context `Γ`: the term variables of `L` are,
innermost first, the entries of `Γ`, and the type of each sees only the type variables
bound outside it. Passing a type variable shifts the types of the term variables outside
it, as System F does under a type abstraction. -/
inductive Carries : List Bool → Context → Prop
  | nil : Carries [] []
  | typeVar {L : List Bool} {Γ : Context} : Carries L Γ → Carries (true :: L) (shiftContext Γ)
  | termVar {L : List Bool} {Γ : Context} (τ : Ty) :
      Carries L Γ → Carries (false :: L) (τ :: Γ)

/-- A layout whose innermost variable is a type variable carries only shifted contexts. -/
theorem Carries.typeVar_inv {L : List Bool} {Γ : Context} (carries : Carries (true :: L) Γ) :
    ∃ Γ', Γ = shiftContext Γ' ∧ Carries L Γ' := by
  cases carries with
  | typeVar carries => exact ⟨_, rfl, carries⟩

/-- Passing a type variable of a carried context. -/
theorem ctx_typeVar (L : List Bool) (Γ : Context) :
    ctx (true :: L) (shiftContext Γ) = .snoc (ctx L Γ) codes.propT := by
  simp [ctx, shiftContext, Function.comp_def, Ty.shiftTyDown_shiftTyUp_cancel]

/-- The layout of a System F context with `k` type variables and term context `Γ`: the
term variables innermost, the type variables outermost. -/
def contextLayout (k : Nat) (Γ : Context) : List Bool :=
  List.replicate Γ.length false ++ List.replicate k true

/-- The layout of a System F context carries its term context. -/
theorem carries_contextLayout (k : Nat) (Γ : Context) : Carries (contextLayout k Γ) Γ := by
  induction Γ with
  | nil =>
      show Carries (List.replicate k true) []
      induction k with
      | zero => exact .nil
      | succ k ih => exact .typeVar (Γ := []) ih
  | cons τ Γ ih => exact .termVar τ ih

/-! ## Typing the codes -/

/-- The level `max 0 0` is below `0`: formation of Π-types over the lowest universe stays
in it. -/
theorem cumulative_max_zero :
    Tower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) :=
  fun _ => Nat.le_of_eq (Nat.max_self 0)

section Typing

variable {n : Nat} {Δ : Tower.Ctx n}

theorem typed_U0 : Typed rules Δ U0 (.head (.sort (.succ Tower.zero))) :=
  .headType (LevelTower.HeadTyping.sort _)

/-- A dependent function type between types of the lowest universe is in the lowest
universe. -/
theorem typed_pi {A : Tower.Tm n} {B : Tower.Tm (n + 1)} (domain : Typed rules Δ A U0)
    (codomain : Typed rules (.snoc Δ A) B U0) : Typed rules Δ (.pi A B) U0 :=
  Derivable.cumul (.piForm domain (LevelTower.IsUniverse.sort _) codomain (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)) cumulative_max_zero

theorem equal_pi {A A' : Tower.Tm n} {B B' : Tower.Tm (n + 1)}
    (domain : Equal rules Δ A A' U0) (codomain : Equal rules (.snoc Δ A) B B' U0) :
    Equal rules Δ (.pi A B) (.pi A' B') U0 :=
  Derivable.cumulEq (.piCong domain (LevelTower.IsUniverse.sort _) codomain
    (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) cumulative_max_zero

/-- Conversion along an equality of types in the lowest universe. -/
theorem typed_conv {t A B : Tower.Tm n} (typing : Typed rules Δ t A)
    (equal : Equal rules Δ A B U0) : Typed rules Δ t B :=
  .conv typing equal (LevelTower.IsUniverse.sort _)

/-- The declared types of the code constants are formed in the empty context, so the
constants are typed in every context. -/
theorem typed_prop : Typed rules Δ codes.propT U0 :=
  .const (codes.extend_constantType_of_code Tower.rules codes.codeType_prop) typed_U0
    (LevelTower.IsUniverse.sort _)

theorem typed_holds : Typed rules Δ (.const codes.holds) (.pi codes.propT U0) :=
  .const (codes.extend_constantType_of_code Tower.rules (codes.codeType_holds (by decide)))
    (.piForm typed_prop (LevelTower.IsUniverse.sort _) typed_U0 (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _)

theorem typed_imp :
    Typed rules Δ (.const codes.imp) (.pi codes.propT (.pi codes.propT codes.propT)) :=
  .const (codes.extend_constantType_of_code Tower.rules (codes.codeType_imp (by decide)))
    (typed_pi typed_prop (typed_pi typed_prop typed_prop)) (LevelTower.IsUniverse.sort _)

theorem typed_allProp :
    Typed rules Δ (.const allProp) (.pi (.pi codes.propT codes.propT) codes.propT) :=
  .const (codes.extend_constantType_of_code Tower.rules
      (codes.codeType_all (a := allProp) (A := .const codes.prop) (by decide) rfl))
    (typed_pi (typed_pi typed_prop typed_prop) typed_prop) (LevelTower.IsUniverse.sort _)

theorem typed_holdsOf {c : Tower.Tm n} (code : Typed rules Δ c codes.propT) :
    Typed rules Δ (codes.holdsOf c) U0 :=
  .appElim typed_holds code

theorem typed_impOf {p q : Tower.Tm n} (left : Typed rules Δ p codes.propT)
    (right : Typed rules Δ q codes.propT) : Typed rules Δ (codes.impOf p q) codes.propT :=
  .appElim (.appElim typed_imp left) right

theorem typed_allOf {f : Tower.Tm n} (family : Typed rules Δ f (.pi codes.propT codes.propT)) :
    Typed rules Δ (allOf f) codes.propT :=
  .appElim typed_allProp family

theorem typed_family {B : Tower.Tm (n + 1)}
    (body : Typed rules (.snoc Δ codes.propT) B codes.propT) :
    Typed rules Δ (.lam B) (.pi codes.propT codes.propT) :=
  .lamIntro (typed_pi typed_prop typed_prop) (LevelTower.IsUniverse.sort _) body

/-- The code read for unbound variables is a code. -/
theorem typed_bottom : Typed rules Δ bottom codes.propT :=
  typed_allOf (typed_family (.var 0))

theorem equal_holdsOf {a b : Tower.Tm n} (equal : Equal rules Δ a b codes.propT) :
    Equal rules Δ (codes.holdsOf a) (codes.holdsOf b) U0 :=
  .appCong (.refl typed_holds) equal

/-- Decoding an implication: `holds (imp p q) ≡ Π (_ : holds p). holds q`. -/
theorem equal_holdsOf_impOf {p q : Tower.Tm n} (left : Typed rules Δ p codes.propT)
    (right : Typed rules Δ q codes.propT) :
    Equal rules Δ (codes.holdsOf (codes.impOf p q))
      (.pi (codes.holdsOf p) (codes.holdsOf (rename wk q))) U0 :=
  .root (codes.extend_decoder_step Tower.rules (DecoderStep.imp p q))
    (typed_holdsOf (typed_impOf left right))
    (typed_pi (typed_holdsOf left) (typed_holdsOf right.weaken))

/-- Decoding a quantification: `holds (allProp f) ≡ Π (x : prop). holds (f x)`. -/
theorem equal_holdsOf_allOf {f : Tower.Tm n}
    (family : Typed rules Δ f (.pi codes.propT codes.propT)) :
    Equal rules Δ (codes.holdsOf (allOf f))
      (.pi codes.propT (codes.holdsOf (.app (rename wk f) (.var 0)))) U0 :=
  .root (codes.extend_decoder_step Tower.rules
      (DecoderStep.all (a := allProp) (A := .const codes.prop) rfl f))
    (typed_holdsOf (typed_allOf family))
    (typed_pi typed_prop (typed_holdsOf (.appElim family.weaken (.var 0))))

/-- Decoding a quantification over an abstraction, with the β-step under the binder:
`holds (allProp (λ α. B)) ≡ Π (α : prop). holds B`. -/
theorem equal_holdsOf_allOf_lam {B : Tower.Tm (n + 1)}
    (body : Typed rules (.snoc Δ codes.propT) B codes.propT) :
    Equal rules Δ (codes.holdsOf (allOf (.lam B))) (.pi codes.propT (codes.holdsOf B)) U0 := by
  refine .trans (equal_holdsOf_allOf (typed_family body))
    (equal_pi (.refl typed_prop) (equal_holdsOf ?_))
  have lifted : Typed rules (.snoc (.snoc Δ codes.propT) codes.propT)
      (rename (liftRen wk) B) codes.propT :=
    body.rename (CtxRen.snoc (fun _ => rfl) codes.propT)
  have beta := Derivable.betaPi (typed_pi typed_prop typed_prop) (LevelTower.IsUniverse.sort _)
    lifted (.var 0)
  rw [inst0_var_rename_liftRen_wk] at beta
  exact beta

/-- Under a new type variable the type variables of the layout are still codes. -/
theorem typed_varOf_true_snoc {L : List Bool} {Δ : Tower.Ctx L.length}
    (vars : ∀ j, Typed rules Δ (varOf true L j) codes.propT) :
    ∀ j, Typed rules (.snoc Δ codes.propT) (varOf true (true :: L) j) codes.propT
  | 0 => by
      rw [varOf_self_zero]
      exact .var 0
  | j + 1 => by
      rw [varOf_self_succ]
      exact (vars j).weaken

/-- The code of every type is a code, in any context where the type variables of the
layout are codes. -/
theorem typed_trTy (τ : Ty) :
    ∀ {L : List Bool} {Δ : Tower.Ctx L.length},
      (∀ j, Typed rules Δ (varOf true L j) codes.propT) →
        Typed rules Δ (trTy L τ) codes.propT := by
  induction τ with
  | tvar j =>
      intro L Δ vars
      exact vars j
  | arr τ σ ihτ ihσ =>
      intro L Δ vars
      exact typed_impOf (ihτ vars) (ihσ vars)
  | all τ ih =>
      intro L Δ vars
      exact typed_allOf (typed_family (ih (L := true :: L) (typed_varOf_true_snoc vars)))

end Typing

/-- In the context of a layout every type variable is a code. -/
theorem typed_varOf_true (L : List Bool) (Γ : Context) (j : Nat) :
    Typed rules (ctx L Γ) (varOf true L j) codes.propT := by
  induction L generalizing Γ j with
  | nil => exact typed_bottom
  | cons b L ih =>
      cases b with
      | true => exact typed_varOf_true_snoc (ih _) j
      | false =>
          rw [varOf_other (by decide)]
          cases Γ with
          | nil => exact (ih [] j).weaken
          | cons τ Γ => exact (ih Γ j).weaken

/-- In the context of a layout carrying `Γ`, the term variables are proofs of the
decodings of the codes of their types. -/
theorem typed_varOf_false {L : List Bool} {Γ : Context} (carries : Carries L Γ) :
    ∀ {i : Nat} {τ : Ty}, lookup Γ i = some τ →
      Typed rules (ctx L Γ) (varOf false L i) (codes.holdsOf (trTy L τ)) := by
  induction carries with
  | nil =>
      intro i τ found
      simp [lookup] at found
  | @typeVar L Γ _ ih =>
      intro i τ found
      simp only [lookup, shiftContext, List.getElem?_map, Option.map_eq_some_iff] at found
      obtain ⟨τ', found', rfl⟩ := found
      rw [ctx_typeVar, varOf_other (by decide), trTy_cons_true_shift]
      exact (ih found').weaken
  | @termVar L Γ τ₀ _ ih =>
      intro i τ found
      cases i with
      | zero =>
          simp only [lookup, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          rw [varOf_self_zero, trTy_cons_false]
          exact .var 0
      | succ i =>
          simp only [lookup, List.getElem?_cons_succ] at found
          rw [varOf_self_succ, trTy_cons_false]
          exact (ih found).weaken

/-- Instantiation passes through the decoder. -/
theorem inst0_holdsOf {n : Nat} (a : Tower.Tm n) (c : Tower.Tm (n + 1)) :
    inst0 a (codes.holdsOf c) = codes.holdsOf (inst0 a c) := rfl

/-- Typing preservation: a System F term of type `τ` in the term context `Γ` translates, in
the context of any layout carrying `Γ`, to a proof of the decoding of the code of `τ`. The
number of type variables in scope plays no role: a type variable the layout does not bind
is read as the code of `∀ α. α`. -/
theorem typed_trTm {k : Nat} {Γ : Context} {M : Term} {τ : Ty}
    (typing : Metatheory.SystemF.HasType k Γ M τ) :
    ∀ {L : List Bool}, Carries L Γ →
      Typed rules (ctx L Γ) (trTm L M) (codes.holdsOf (trTy L τ)) := by
  induction typing with
  | var found =>
      intro L carries
      exact typed_varOf_false carries found
  | @lam k Γ τ₁ τ₂ M _ _ ih =>
      intro L carries
      have body := ih (Carries.termVar τ₁ carries)
      rw [trTy_cons_false] at body
      have domain := typed_trTy τ₁ (typed_varOf_true L Γ)
      have codomain := typed_trTy τ₂ (typed_varOf_true L Γ)
      exact typed_conv
        (.lamIntro (typed_pi (typed_holdsOf domain) (typed_holdsOf codomain.weaken))
          (LevelTower.IsUniverse.sort _) body)
        (.symm (equal_holdsOf_impOf domain codomain))
  | @app k Γ M N τ₁ τ₂ _ _ ihM ihN =>
      intro L carries
      have domain := typed_trTy τ₁ (typed_varOf_true L Γ)
      have codomain := typed_trTy τ₂ (typed_varOf_true L Γ)
      have applied := Derivable.appElim
        (typed_conv (ihM carries) (equal_holdsOf_impOf domain codomain)) (ihN carries)
      rw [inst0_holdsOf, inst0_rename_wk] at applied
      exact applied
  | @tlam k Γ M τ _ ih =>
      intro L carries
      have body := ih (Carries.typeVar carries)
      rw [ctx_typeVar] at body
      have codomain :=
        typed_trTy τ (L := true :: L) (typed_varOf_true_snoc (typed_varOf_true L Γ))
      exact typed_conv
        (.lamIntro (typed_pi typed_prop (typed_holdsOf codomain)) (LevelTower.IsUniverse.sort _) body)
        (.symm (equal_holdsOf_allOf_lam codomain))
  | @tapp k Γ M τ σ _ _ ih =>
      intro L carries
      have argument := typed_trTy σ (typed_varOf_true L Γ)
      have codomain :=
        typed_trTy τ (L := true :: L) (typed_varOf_true_snoc (typed_varOf_true L Γ))
      have applied := Derivable.appElim
        (typed_conv (ih carries) (equal_holdsOf_allOf_lam codomain)) argument
      rw [inst0_holdsOf, ← trTy_substTy0] at applied
      exact applied

/-- Typing preservation in the layout of the System F context itself. -/
theorem typed_trTm_contextLayout {k : Nat} {Γ : Context} {M : Term} {τ : Ty}
    (typing : Metatheory.SystemF.HasType k Γ M τ) :
    Typed rules (ctx (contextLayout k Γ) Γ) (trTm (contextLayout k Γ) M)
      (codes.holdsOf (trTy (contextLayout k Γ) τ)) :=
  typed_trTm typing (carries_contextLayout k Γ)

/-- Typing preservation for closed terms. -/
theorem typed_trTm_closed {M : Term} {τ : Ty} (typing : Metatheory.SystemF.HasType 0 [] M τ) :
    Typed rules .nil (trTm [] M) (codes.holdsOf (trTy [] τ)) :=
  typed_trTm typing .nil

/-! ## Reduction -/

/-- Simulation: a full β-step or type-β-step of System F is one β-step of the translation,
and a congruence step is a congruence step. No root computation and no head step is
used, so this holds for every rule package. -/
theorem trTm_step {root : RootComputation Tower.Head} {headEq : Tower.Head → Tower.Head → Prop}
    {M M' : Term} (step : StrongStep M M') (L : List Bool) :
    StepCore root headEq (trTm L M) (trTm L M') := by
  induction step generalizing L with
  | beta τ M N =>
      rw [trTm_substTerm0]
      exact .betaPi _ _
  | tbeta M σ =>
      rw [trTm_substTypeInTerm0]
      exact .betaPi _ _
  | lam _ ih => exact .congLam (ih _)
  | appL _ ih => exact .congAppFun (ih _)
  | appR _ ih => exact .congAppArg (ih _)
  | tlam _ ih => exact .congLam (ih _)
  | tappL _ ih => exact .congAppFun (ih _)

/-- Reduction sequences of System F are simulated step by step. -/
theorem trTm_steps {root : RootComputation Tower.Head}
    {headEq : Tower.Head → Tower.Head → Prop} {M M' : Term} (steps : StrongMultiStep M M')
    (L : List Bool) : Relation.ReflTransGen (StepCore root headEq) (trTm L M) (trTm L M') := by
  induction steps with
  | refl => exact .refl
  | step step _ ih => exact .head (trTm_step step L) ih

/-- A System F term is strongly normalizing when its translation is. -/
theorem sn_of_acc_trTm {root : RootComputation Tower.Head}
    {headEq : Tower.Head → Tower.Head → Prop} {L : List Bool} {M : Term}
    (acc : Acc (fun u t => StepCore root headEq t u) (trTm L M)) : Metatheory.SystemF.SN M := by
  generalize equal : trTm L M = t at acc
  induction acc generalizing M with
  | intro t _ ih =>
      subst equal
      exact Acc.intro M fun M' step => ih (trTm L M') (trTm_step step L) rfl

/-- Strong normalization of System F from strong normalization of the package: if every
term typed in `codes.extend Tower.rules` is strongly normalizing for its reduction without
universe-head steps, then every well-typed System F term is strongly normalizing. The
hypothesis is, definitionally, strong normalization of typed terms in the sense of
`StrongNormalization.SN`. -/
theorem sn_of_packageSN
    (packageSN : ∀ {n : Nat} {Δ : Tower.Ctx n} {t A : Tower.Tm n}, Typed rules Δ t A →
      Acc (fun u t => StepCore rules.computation (fun _ _ => False) t u) t)
    {k : Nat} {Γ : Context} {M : Term} {τ : Ty} (typing : Metatheory.SystemF.HasType k Γ M τ) :
    Metatheory.SystemF.SN M :=
  sn_of_acc_trTm (packageSN (typed_trTm_contextLayout typing))

/-! ## Formed contexts -/

/-- The context of every layout is formed: each entry is the type of codes or the
decoding of a code. -/
theorem ctx_formed : ∀ (L : List Bool) (Γ : Context), CtxFormed rules (ctx L Γ)
  | [], _ => .nil
  | true :: L, _ => .snoc (ctx_formed L _) ⟨_, .sort _, typed_prop⟩
  | false :: L, [] => .snoc (ctx_formed L []) ⟨_, .sort _, typed_holdsOf typed_bottom⟩
  | false :: L, τ :: Γ =>
      .snoc (ctx_formed L Γ) ⟨_, .sort _, typed_holdsOf (typed_trTy τ (typed_varOf_true L Γ))⟩

/-- Strong normalization of System F from strong normalization of the package on the terms
typed in formed contexts: the context of the layout of a System F context is formed. -/
theorem sn_of_formedPackageSN
    (packageSN : ∀ {n : Nat} {Δ : Tower.Ctx n} {t A : Tower.Tm n}, CtxFormed rules Δ →
      Typed rules Δ t A → Acc (fun u t => StepCore rules.computation (fun _ _ => False) t u) t)
    {k : Nat} {Γ : Context} {M : Term} {τ : Ty} (typing : Metatheory.SystemF.HasType k Γ M τ) :
    Metatheory.SystemF.SN M :=
  sn_of_acc_trTm (packageSN (ctx_formed _ _) (typed_trTm_contextLayout typing))

/-! ## Examples -/

/-- The polymorphic identity `Λ α. λ x : α. x` becomes `λ α. λ x. x`. -/
example : trTm [] Term.polyId = .lam (.lam (.var 0)) := rfl

/-- Its type `∀ α. α → α` becomes the code `allProp (λ α. imp α α)`. -/
example : trTy [] Ty.idTy = allOf (.lam (codes.impOf (.var 0) (.var 0))) := rfl

/-- The polymorphic identity proves `holds (allProp (λ α. imp α α))`. -/
example : Typed rules .nil (.lam (.lam (.var 0)))
    (codes.holdsOf (allOf (.lam (codes.impOf (.var 0) (.var 0))))) :=
  typed_trTm_closed (M := Term.polyId) (τ := Ty.idTy) (.tlam (.lam Nat.zero_lt_one (.var rfl)))

/-- Instantiating the polymorphic identity at a type is one β-step of the translation. -/
example : StepCore rules.computation (fun _ _ => False)
    (.app (.lam (.lam (.var 0))) (trTy [] Ty.idTy)) (.lam (.var 0) : Tower.Tm 0) :=
  trTm_step (.tbeta (.lam (.tvar 0) (.var 0)) Ty.idTy) []

/-- A type variable that the layout does not bind is read as the code of `∀ α. α`. -/
example : trTy [] (.tvar 0) = bottom := rfl

/-- A term variable may have a type in a type variable bound outside it. -/
example : Carries [false, true] [.tvar 0] :=
  .termVar (.tvar 0) (.typeVar .nil)

/-- A term variable may not have a type in a type variable bound inside it. -/
example : ¬ Carries [true, false] [.tvar 0] := by
  intro carries
  obtain ⟨Γ, shifted, -⟩ := carries.typeVar_inv
  cases Γ with
  | nil => cases shifted
  | cons τ Γ =>
      simp only [shiftContext, List.map_cons, List.cons.injEq] at shifted
      cases τ <;> simp [Ty.shiftTyUp] at shifted

end SystemF

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
