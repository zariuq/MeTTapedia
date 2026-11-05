import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.TermEquality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Logic.LP (LPSignature Subst unifyTotal Unifies)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst)

/-- Every MeTTa-IL constructor as a first-order head, with its arity. -/
inductive Head where
  | apply (name : String) (arity : Nat)
  | collection (kind : CollType) (rest : Option String) (arity : Nat)
  | bvar (index : Nat)
  | lambda (name : Option String)
  | multiLambda (count : Nat) (names : List String)
  | subst
  deriving DecidableEq

def Head.arity : Head → Nat
  | .apply _ arity => arity
  | .collection _ _ arity => arity
  | .bvar _ => 0
  | .lambda _ => 1
  | .multiLambda _ _ => 1
  | .subst => 2

abbrev sig : LPSignature where
  constants := Empty
  vars := String
  relationSymbols := Empty
  relationArity := fun e => e.elim
  functionSymbols := Head
  functionArity := Head.arity

/-- First-order terms over the encoded heads. -/
abbrev LTerm := Mettapedia.Logic.LP.Term sig

mutual
def encode : Pattern → LTerm
  | .fvar x => .var x
  | .bvar n => .app (.bvar n) Fin.elim0
  | .apply c args =>
      let encoded := encodeList args
      .app (.apply c encoded.length) fun i => encoded.get i
  | .lambda nm body => .app (.lambda nm) fun _ => encode body
  | .multiLambda n nms body => .app (.multiLambda n nms) fun _ => encode body
  | .subst body repl => .app .subst fun i => if i.val = 0 then encode body else encode repl
  | .collection ct elems rest =>
      let encoded := encodeList elems
      .app (.collection ct rest encoded.length) fun i => encoded.get i
def encodeList : List Pattern → List (LTerm)
  | [] => []
  | p :: ps => encode p :: encodeList ps
end

def decode : LTerm → Pattern
  | .var x => .fvar x
  | .const c => c.elim
  | .app (.apply c n) ts => .apply c (List.ofFn (n := n) fun i => decode (ts i))
  | .app (.collection ct rest n) ts => .collection ct (List.ofFn (n := n) fun i => decode (ts i)) rest
  | .app (.bvar k) _ => .bvar k
  | .app (.lambda nm) ts => .lambda nm (decode (ts ⟨0, Nat.zero_lt_one⟩))
  | .app (.multiLambda n nms) ts => .multiLambda n nms (decode (ts ⟨0, Nat.zero_lt_one⟩))
  | .app .subst ts => .subst (decode (ts ⟨0, by decide⟩)) (decode (ts ⟨1, by decide⟩))

/-! ## A kernel-evaluable Martelli--Montanari run -/

open Mettapedia.Logic.LP (finPairsToList mmSize mmVarCount)

abbrev Equations := List (LTerm × LTerm)

/-- The Martelli--Montanari rules of `unifyTotal`, run with an explicit
decomposition budget. Each elimination hands the rewritten problem to `next`. -/
def solveWith (next : Equations → Option (Subst sig)) : ℕ → Equations → Option (Subst sig)
  | _, [] => some (Subst.id sig)
  | 0, _ :: _ => none
  | size + 1, (source, target) :: rest =>
      match source with
      | .var v =>
          match target with
          | .var other =>
              if v = other then solveWith next size rest
              else
                match next ((Subst.single v (.var other)).applyEqs rest) with
                | none => none
                | some substitution => some (substitution ∘ₛ Subst.single v (.var other))
          | term =>
              if term.occursIn v then none
              else
                match next ((Subst.single v term).applyEqs rest) with
                | none => none
                | some substitution => some (substitution ∘ₛ Subst.single v term)
      | .const constant => constant.elim
      | .app function arguments =>
          match target with
          | .var v =>
              if (Mettapedia.Logic.LP.Term.app function arguments).occursIn v then none
              else
                match next ((Subst.single v (.app function arguments)).applyEqs rest) with
                | none => none
                | some substitution =>
                    some (substitution ∘ₛ Subst.single v (.app function arguments))
          | .const constant => constant.elim
          | .app other otherArguments =>
              if equal : function = other then
                solveWith next size (finPairsToList arguments (equal ▸ otherArguments) ++ rest)
              else none

/-- `eliminations` bounds the number of variable eliminations; between two
eliminations the decomposition budget is the problem's size. -/
def solve : ℕ → Equations → Option (Subst sig)
  | 0, equations => solveWith (fun _ => none) (mmSize equations) equations
  | eliminations + 1, equations => solveWith (solve eliminations) (mmSize equations) equations

/-- Both budgets are read off the problem. -/
def solveEquations (equations : Equations) : Option (Subst sig) :=
  solve (mmSize equations) equations

/-! ## The two-budget run is the total unifier -/

open Mettapedia.Logic.LP (eqVars mmVarCount_eliminate_lt mmSize_var_eq_lt mmVarCount_cons_ge
  mmVarCount_app_eq_decompose_le mmSize_app_eq_decompose_lt)

theorem mmVarCount_swap (left right : LTerm) (rest : Equations) :
    mmVarCount ((left, right) :: rest) = mmVarCount ((right, left) :: rest) := by
  simp only [mmVarCount, eqVars]
  rw [Finset.union_comm left.freeVars right.freeVars]

theorem mmSize_pos_of_cons (head : LTerm × LTerm) (rest : Equations) :
    0 < mmSize (head :: rest) := by
  obtain ⟨left, right⟩ := head
  have := Mettapedia.Logic.LP.Term.size_pos left
  simp only [mmSize]
  omega

theorem solveWith_eq_unifyTotal (next : Equations → Option (Subst sig)) (bound : ℕ)
    (nextSpec : ∀ equations : Equations, mmVarCount equations < bound → next equations = unifyTotal equations)
    (equations : Equations) :
    ∀ size, mmSize equations ≤ size → mmVarCount equations ≤ bound →
      solveWith next size equations = unifyTotal equations := by
  fun_induction unifyTotal equations with
  | case1 => intro size _ _; cases size <;> rfl
  | case2 rest v ih =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, .var v) rest; omega⟩
      simp only [solveWith]
      exact ih s (by have := mmSize_var_eq_lt (σ := sig) v rest; omega)
        (le_trans (mmVarCount_cons_ge _ _ rest) counted)
  | case3 rest v other notEqual childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, .var other) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v (.var other) rest
        (by simpa [Mettapedia.Logic.LP.Term.occursIn] using notEqual)
      simp [solveWith, notEqual, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case4 rest v other notEqual childTheta childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, .var other) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v (.var other) rest
        (by simpa [Mettapedia.Logic.LP.Term.occursIn] using notEqual)
      simp [solveWith, notEqual, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case5 rest v term notVariable occurs =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, term) rest; omega⟩
      cases term with
      | var other => exact absurd rfl (notVariable other)
      | const constant => exact constant.elim
      | app function arguments => simp [solveWith, occurs]
  | case6 rest v term notVariable notOccurs childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, term) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v term rest (by simpa using notOccurs)
      cases term with
      | var other => exact absurd rfl (notVariable other)
      | const constant => exact constant.elim
      | app function arguments =>
          simp [solveWith, notOccurs, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case7 rest v term notVariable notOccurs childTheta childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.var v, term) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v term rest (by simpa using notOccurs)
      cases term with
      | var other => exact absurd rfl (notVariable other)
      | const constant => exact constant.elim
      | app function arguments =>
          simp [solveWith, notOccurs, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case8 rest constant => exact constant.elim
  | case9 rest constant => exact constant.elim
  | case10 rest constant => exact constant.elim
  | case11 rest constant => exact constant.elim
  | case12 rest constant => exact constant.elim
  | case13 rest function arguments v occurs =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.app function arguments, .var v) rest; omega⟩
      simp [solveWith, occurs]
  | case14 rest function arguments v notOccurs childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.app function arguments, .var v) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v (.app function arguments) rest
        (by simpa using notOccurs)
      rw [← mmVarCount_swap] at smaller
      simp [solveWith, notOccurs, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case15 rest function arguments v notOccurs childTheta childResult =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by have := mmSize_pos_of_cons (.app function arguments, .var v) rest; omega⟩
      have smaller := mmVarCount_eliminate_lt (σ := sig) v (.app function arguments) rest
        (by simpa using notOccurs)
      rw [← mmVarCount_swap] at smaller
      simp [solveWith, notOccurs, nextSpec _ (lt_of_lt_of_le smaller counted), childResult]
  | case16 rest function arguments constant => exact constant.elim
  | case17 rest function targetArguments sourceArguments ih =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by
          have := mmSize_pos_of_cons (.app function sourceArguments, .app function targetArguments) rest
          omega⟩
      simp only [solveWith, dite_true]
      have smaller := mmSize_app_eq_decompose_lt (σ := sig) function sourceArguments targetArguments rest
      exact ih s (Nat.le_of_lt_succ (lt_of_lt_of_le smaller sized))
        (le_trans (mmVarCount_app_eq_decompose_le function sourceArguments targetArguments rest) counted)
  | case18 rest leftFunction leftArguments rightFunction rightArguments notEqual =>
      intro size sized counted
      obtain ⟨s, rfl⟩ : ∃ s, size = s + 1 :=
        ⟨size - 1, by
          have := mmSize_pos_of_cons (.app leftFunction leftArguments,
            .app rightFunction rightArguments) rest; omega⟩
      simp [solveWith, notEqual]

theorem solve_eq_unifyTotal (eliminations : ℕ) (equations : Equations)
    (counted : mmVarCount equations ≤ eliminations) :
    solve eliminations equations = unifyTotal equations := by
  induction eliminations generalizing equations with
  | zero =>
      exact solveWith_eq_unifyTotal _ 0 (fun _ impossible => absurd impossible (Nat.not_lt_zero _))
        equations _ le_rfl counted
  | succ eliminations ih =>
      exact solveWith_eq_unifyTotal _ (eliminations + 1)
        (fun smaller fewer => ih smaller (Nat.lt_succ_iff.mp fewer)) equations _ le_rfl counted

theorem card_freeVars_le_size (term : LTerm) : term.freeVars.card ≤ term.size := by
  induction term with
  | var v => simp [Mettapedia.Logic.LP.Term.freeVars, Mettapedia.Logic.LP.Term.size]
  | const constant => exact constant.elim
  | app function arguments ih =>
      simp only [Mettapedia.Logic.LP.Term.freeVars, Mettapedia.Logic.LP.Term.size]
      calc (Finset.univ.biUnion fun i => (arguments i).freeVars).card
          ≤ ∑ i, (arguments i).freeVars.card := Finset.card_biUnion_le
        _ ≤ ∑ i, (arguments i).size := Finset.sum_le_sum fun i _ => ih i
        _ ≤ 1 + ∑ i, (arguments i).size := Nat.le_add_left _ _

theorem mmVarCount_le_mmSize (equations : Equations) : mmVarCount equations ≤ mmSize equations := by
  induction equations with
  | nil => simp [mmVarCount, eqVars]
  | cons head rest ih =>
      obtain ⟨left, right⟩ := head
      simp only [mmVarCount, eqVars, mmSize] at ih ⊢
      calc (left.freeVars ∪ right.freeVars ∪ eqVars rest).card
          ≤ (left.freeVars ∪ right.freeVars).card + (eqVars rest).card := Finset.card_union_le _ _
        _ ≤ left.freeVars.card + right.freeVars.card + (eqVars rest).card := by
            have := Finset.card_union_le left.freeVars right.freeVars; omega
        _ ≤ left.size + right.size + mmSize rest := by
            have := card_freeVars_le_size left
            have := card_freeVars_le_size right
            omega

/-- The kernel-evaluable run computes exactly the total unifier. -/
theorem solveEquations_eq_unifyTotal (equations : Equations) :
    solveEquations equations = unifyTotal equations :=
  solve_eq_unifyTotal _ equations (mmVarCount_le_mmSize equations)

/-! ## The encoding is faithful to structural substitution -/

theorem encodeList_eq_map (ps : List Pattern) : encodeList ps = ps.map encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [encodeList, ih]

theorem psubstList_eq_map (σ : PSubst) (ps : List Pattern) :
    psubst.psubstList σ ps = ps.map (psubst σ) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [psubst.psubstList, ih]

theorem ofFn_get_map {α β : Type} (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
  apply List.ext_get <;> simp

theorem decode_encode (p : Pattern) : decode (encode p) = p := by
  induction p using Pattern.rec (motive_2 := fun ps => (encodeList ps).map decode = ps) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [encode, decode]
      rw [ofFn_get_map, ih]
  | lambda nm body ih => simp only [encode, decode, ih]
  | multiLambda n nms body ih => simp only [encode, decode, ih]
  | subst body repl ihb ihr => simp [encode, decode, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [encode, decode]
      rw [ofFn_get_map, ih]
  | nil => rfl
  | cons p ps head tail => simp [encodeList, head, tail]

theorem encode_injective : Function.Injective encode := fun p q same => by
  rw [← decode_encode p, ← decode_encode q, same]

/-- A substitution of the encoding, read back on patterns. -/
def lower (θ : Subst sig) : PSubst := fun v => some (decode (θ v))

theorem decode_applyTerm_encode (θ : Subst sig) (p : Pattern) :
    decode (θ.applyTerm (encode p)) = psubst (lower θ) p := by
  induction p using Pattern.rec (motive_2 := fun ps =>
      (encodeList ps).map (fun T => decode (θ.applyTerm T)) = psubst.psubstList (lower θ) ps) with
  | bvar n => rfl
  | fvar x => simp [encode, lower, psubst, Subst.applyTerm_var]
  | apply c args ih =>
      simp only [encode, Subst.applyTerm_app, decode, psubst]
      rw [ofFn_get_map (encodeList args) (fun T => decode (θ.applyTerm T)), ih]
  | lambda nm body ih => simp only [encode, Subst.applyTerm_app, decode, psubst, ih]
  | multiLambda n nms body ih => simp only [encode, Subst.applyTerm_app, decode, psubst, ih]
  | subst body repl ihb ihr => simp [encode, Subst.applyTerm_app, decode, psubst, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [encode, Subst.applyTerm_app, decode, psubst]
      rw [ofFn_get_map (encodeList elems) (fun T => decode (θ.applyTerm T)), ih]
  | nil => rfl
  | cons p ps head tail => simp [encodeList, head, tail, psubst.psubstList]

/-- A pattern substitution, as a substitution of the encoding. -/
def lift (τ : PSubst) : Subst sig := fun v => encode ((τ v).getD (.fvar v))

theorem app_apply_cast (c : String) {m n : ℕ} (e : m = n)
    (f : Fin m → LTerm) (g : Fin n → LTerm) (same : ∀ i, f i = g (i.cast e)) :
    (Mettapedia.Logic.LP.Term.app (Head.apply c m) f : LTerm) = .app (Head.apply c n) g := by
  subst e
  have : f = g := funext fun i => by simpa using same i
  subst this
  rfl

theorem app_collection_cast (ct : CollType) (rest : Option String) {m n : ℕ}
    (e : m = n) (f : Fin m → LTerm) (g : Fin n → LTerm) (same : ∀ i, f i = g (i.cast e)) :
    (Mettapedia.Logic.LP.Term.app (Head.collection ct rest m) f : LTerm) =
      .app (Head.collection ct rest n) g := by
  subst e
  have : f = g := funext fun i => by simpa using same i
  subst this
  rfl

theorem encode_psubst (τ : PSubst) (p : Pattern) :
    encode (psubst τ p) = (lift τ).applyTerm (encode p) := by
  induction p using Pattern.rec (motive_2 := fun ps =>
      encodeList (psubst.psubstList τ ps) = (encodeList ps).map (lift τ).applyTerm) with
  | bvar n =>
      simp only [psubst, encode]
      congr 1
      funext i
      exact i.elim0
  | fvar x => simp [encode, lift, psubst, Subst.applyTerm_var]
  | apply c args ih =>
      simp only [psubst, encode, Subst.applyTerm_app]
      exact app_apply_cast c (by rw [ih, List.length_map]) _ _ fun i => by
        rw [List.get_of_eq ih]
        simp
  | lambda nm body ih =>
      simp only [psubst, encode, Subst.applyTerm_app, ih]
  | multiLambda n nms body ih =>
      simp only [psubst, encode, Subst.applyTerm_app, ih]
  | subst body repl ihb ihr =>
      simp only [psubst, encode, Subst.applyTerm_app]
      congr 1
      funext i
      split <;> simp [ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, encode, Subst.applyTerm_app]
      exact app_collection_cast ct rest (by rw [ih, List.length_map]) _ _
        fun i => by
          rw [List.get_of_eq ih]
          simp
  | nil => rfl
  | cons p ps head tail => simp [encodeList, psubst.psubstList, head, tail]

theorem psubst_lower_lift (τ : PSubst) (p : Pattern) : psubst (lower (lift τ)) p = psubst τ p := by
  rw [← decode_applyTerm_encode, ← encode_psubst, decode_encode]

theorem encode_decode (T : LTerm) : encode (decode T) = T := by
  induction T with
  | var x => rfl
  | const c => exact c.elim
  | app head ts ih =>
      cases head with
      | apply c n =>
          simp only [decode, encode]
          exact app_apply_cast c (by simp [encodeList_eq_map]) _ _ fun i => by
            simp only [encodeList_eq_map, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
            exact ih _
      | collection ct rest n =>
          simp only [decode, encode]
          exact app_collection_cast ct rest (by simp [encodeList_eq_map]) _ _ fun i => by
            simp only [encodeList_eq_map, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
            exact ih _
      | bvar k =>
          simp only [decode, encode]
          congr 1
          funext i
          exact i.elim0
      | lambda nm =>
          simp only [decode, encode, ih]
          congr 1
          funext i
          congr 1
          exact Fin.ext (by have bound : i.val < 1 := i.isLt; show 0 = i.val; omega)
      | multiLambda n nms =>
          simp only [decode, encode, ih]
          congr 1
          funext i
          congr 1
          exact Fin.ext (by have bound : i.val < 1 := i.isLt; show 0 = i.val; omega)
      | subst =>
          simp only [decode, encode, ih]
          congr 1
          funext i
          have bound : i.val < 2 := i.isLt
          by_cases zero : i.val = 0
          · simp only [zero, if_true]
            congr 1
            exact Fin.ext zero.symm
          · simp only [zero, if_false]
            congr 1
            exact Fin.ext (by simp; omega)

theorem lift_lower (θ : Subst sig) : lift (lower θ) = θ := by
  funext v
  simp [lift, lower, encode_decode]

theorem encode_psubst_lower (θ : Subst sig) (p : Pattern) :
    encode (psubst (lower θ) p) = θ.applyTerm (encode p) := by
  rw [encode_psubst, lift_lower]

theorem mem_freeVars_app_iff {head : Head} {ts : Fin (Head.arity head) → LTerm} {x : String} :
    x ∈ (Mettapedia.Logic.LP.Term.app (σ := sig) head ts).freeVars ↔ ∃ i, x ∈ (ts i).freeVars := by
  simp only [Mettapedia.Logic.LP.Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem mem_freeVars_listApp (head : Head) (L : List LTerm) (e : Head.arity head = L.length)
    (x : String) :
    x ∈ (Mettapedia.Logic.LP.Term.app (σ := sig) head fun i => L.get (i.cast e)).freeVars ↔
      ∃ T ∈ L, x ∈ T.freeVars := by
  rw [mem_freeVars_app_iff]
  constructor
  · rintro ⟨i, member⟩
    exact ⟨_, List.get_mem _ _, member⟩
  · rintro ⟨T, member, occurs⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem member
    exact ⟨i.cast e.symm, by simpa using occurs⟩

theorem mem_freeVars_encode (p : Pattern) (x : String) :
    x ∈ (encode p).freeVars ↔ x ∈ pvars p := by
  induction p using Pattern.rec (motive_2 := fun ps =>
      (∃ T ∈ encodeList ps, x ∈ T.freeVars) ↔ x ∈ pvars.pvarsList ps) with
  | bvar n =>
      simp only [encode, pvars, List.not_mem_nil, iff_false]
      intro member
      obtain ⟨i, _⟩ := (mem_freeVars_app_iff (head := Head.bvar n) (ts := Fin.elim0)).mp member
      exact i.elim0
  | fvar y =>
      simp [encode, Mettapedia.Logic.LP.Term.freeVars, pvars]
  | apply c args ih =>
      simp only [pvars]
      rw [← ih, ← mem_freeVars_listApp (.apply c (encodeList args).length) (encodeList args) rfl]
      rfl
  | lambda nm body ih =>
      simp only [encode, pvars]
      rw [mem_freeVars_app_iff, ← ih]
      exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨⟨0, Nat.zero_lt_one⟩, member⟩⟩
  | multiLambda n nms body ih =>
      simp only [encode, pvars]
      rw [mem_freeVars_app_iff, ← ih]
      exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨⟨0, Nat.zero_lt_one⟩, member⟩⟩
  | subst body repl ihb ihr =>
      simp only [encode, pvars, List.mem_append]
      rw [mem_freeVars_app_iff, ← ihb, ← ihr]
      constructor
      · rintro ⟨i, member⟩
        by_cases zero : i.val = 0
        · simp only [zero, if_true] at member; exact .inl member
        · simp only [zero, if_false] at member; exact .inr member
      · rintro (member | member)
        · exact ⟨⟨0, by decide⟩, by simpa using member⟩
        · exact ⟨⟨1, by decide⟩, by simpa using member⟩
  | collection ct elems rest ih =>
      simp only [pvars]
      rw [← ih, ← mem_freeVars_listApp (.collection ct rest (encodeList elems).length)
        (encodeList elems) rfl]
      rfl
  | nil => simp [encodeList, pvars.pvarsList]
  | cons p ps head tail =>
      simp only [encodeList, List.mem_cons, pvars.pvarsList, List.mem_append, ← head, ← tail]
      constructor
      · rintro ⟨T, (rfl | member), occurs⟩
        · exact .inl occurs
        · exact .inr ⟨T, member, occurs⟩
      · rintro (occurs | ⟨T, member, occurs⟩)
        · exact ⟨_, .inl rfl, occurs⟩
        · exact ⟨T, .inr member, occurs⟩

theorem mem_pvars_decode (T : LTerm) (x : String) : x ∈ pvars (decode T) ↔ x ∈ T.freeVars := by
  rw [← mem_freeVars_encode, encode_decode]

/-! ## Principal unification of patterns -/

open Mettapedia.Logic.LP (unifyTotal_sound unifyTotal_mgu unifyTotal_complete
  unifyTotal_relevantIdempotent)

/-- The total unifier of the two encodings, computed by the two-budget run. -/
def unifier (t u : Pattern) : Option (Subst sig) := solveEquations [(encode t, encode u)]

theorem unifier_eq (t u : Pattern) : unifier t u = unifyTotal [(encode t, encode u)] :=
  solveEquations_eq_unifyTotal _

/-- The variables of two patterns, each once. -/
def patternVariables (t u : Pattern) : List String := (pvars t ++ pvars u).dedup

/-- The bindings of the variables among `vs` that `θ` moves. -/
def toBindings (θ : Subst sig) (vs : List String) : Bindings :=
  vs.filterMap fun v => if decode (θ v) = .fvar v then none else some (v, decode (θ v))

/-- Occurs-checked principal unification of two patterns. Each variable the
unifier moves is bound once, to its final value. -/
def unify (t u : Pattern) : Option Bindings :=
  (unifier t u).map fun θ => toBindings θ (patternVariables t u)

theorem lookup_cons (key : String) (value : Pattern) (rest : Bindings) (v : String) :
    Bindings.lookup ((key, value) :: rest) v = if key = v then some value else rest.lookup v := by
  by_cases same : key = v
  · subst same; simp [Bindings.lookup]
  · simp [Bindings.lookup, same]

theorem getD_lookup_toBindings (θ : Subst sig) (vs : List String) (v : String) :
    ((toBindings θ vs).lookup v).getD (.fvar v) = if v ∈ vs then decode (θ v) else .fvar v := by
  induction vs with
  | nil => simp [toBindings, Bindings.lookup]
  | cons w ws ih =>
      by_cases fixed : decode (θ w) = .fvar w
      · have rest : toBindings θ (w :: ws) = toBindings θ ws := by simp [toBindings, fixed]
        rw [rest, ih]
        by_cases same : v = w
        · subst same; simp [fixed]
        · simp [same]
      · have rest : toBindings θ (w :: ws) = (w, decode (θ w)) :: toBindings θ ws := by
          simp [toBindings, fixed]
        rw [rest, lookup_cons]
        by_cases same : w = v
        · subst same; simp
        · simp only [same, if_false, ih, List.mem_cons]
          by_cases inside : v ∈ ws
          · simp [inside]
          · simp [inside, Ne.symm same]

theorem lookup_toBindings_of_fixed (θ : Subst sig) (vs : List String) {x : String}
    (fixed : decode (θ x) = .fvar x) : (toBindings θ vs).lookup x = none := by
  induction vs with
  | nil => simp [toBindings, Bindings.lookup]
  | cons w ws ih =>
      by_cases fixedW : decode (θ w) = .fvar w
      · have rest : toBindings θ (w :: ws) = toBindings θ ws := by simp [toBindings, fixedW]
        rw [rest, ih]
      · have rest : toBindings θ (w :: ws) = (w, decode (θ w)) :: toBindings θ ws := by
          simp [toBindings, fixedW]
        rw [rest, lookup_cons]
        have different : w ≠ x := fun same => fixedW (same ▸ fixed)
        simp [different, ih]

theorem psubst_getD_congr {σ τ : PSubst}
    (agree : ∀ v, (σ v).getD (.fvar v) = (τ v).getD (.fvar v)) (p : Pattern) :
    psubst σ p = psubst τ p := by
  induction p using Pattern.rec (motive_2 := fun ps =>
      psubst.psubstList σ ps = psubst.psubstList τ ps) with
  | bvar n => rfl
  | fvar x => simp only [psubst]; exact agree x
  | apply c args ih => simp only [psubst, ih]
  | lambda nm body ih => simp only [psubst, ih]
  | multiLambda n nms body ih => simp only [psubst, ih]
  | subst body repl ihb ihr => simp only [psubst, ihb, ihr]
  | collection ct elems rest ih => simp only [psubst, ih]
  | nil => rfl
  | cons p ps head tail => simp only [psubst.psubstList, head, tail]

theorem mem_eqVars_pair (t u : Pattern) (x : String) :
    x ∈ eqVars [(encode t, encode u)] ↔ x ∈ pvars t ++ pvars u := by
  simp only [eqVars, Finset.mem_union, Finset.notMem_empty, or_false, List.mem_append]
  rw [mem_freeVars_encode, mem_freeVars_encode]

/-- What `unify` returns, in terms of the total unifier. -/
theorem unify_spec {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    ∃ θ, unifyTotal [(encode t, encode u)] = some θ ∧
      θ.RelevantIdempotent (eqVars [(encode t, encode u)]) ∧
      bs = toBindings θ (patternVariables t u) ∧
      ∀ p, psubst bs.lookup p = psubst (lower θ) p := by
  unfold unify at found
  rw [unifier_eq] at found
  cases total : unifyTotal [(encode t, encode u)] with
  | none => rw [total] at found; cases found
  | some θ =>
      rw [total] at found
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      have relevant := unifyTotal_relevantIdempotent _ θ total
      refine ⟨θ, rfl, relevant, rfl, fun p => psubst_getD_congr (fun v => ?_) p⟩
      rw [getD_lookup_toBindings]
      simp only [lower, Option.getD_some]
      split
      · rfl
      · rename_i outside
        have notVariable : v ∉ eqVars [(encode t, encode u)] := by
          rw [mem_eqVars_pair]
          simpa [patternVariables] using outside
        rw [relevant.fixes v notVariable]
        rfl

/-- **Soundness.** One pass of the bindings makes the two patterns equal. -/
theorem unify_sound {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    psubst bs.lookup t = psubst bs.lookup u := by
  obtain ⟨θ, total, _, _, agree⟩ := unify_spec found
  rw [agree, agree, ← decode_applyTerm_encode, ← decode_applyTerm_encode]
  have unifies := unifyTotal_sound _ θ total
  rw [unifies (encode t, encode u) (List.mem_singleton_self _)]

/-- **Idempotence.** A second pass changes nothing. -/
theorem unify_idempotent {t u : Pattern} {bs : Bindings} (found : unify t u = some bs)
    (p : Pattern) : psubst bs.lookup (psubst bs.lookup p) = psubst bs.lookup p := by
  obtain ⟨θ, _, relevant, _, agree⟩ := unify_spec found
  rw [agree, agree]
  apply encode_injective
  rw [encode_psubst_lower, encode_psubst_lower, relevant.absorbs.applyTerm]

/-- **Most generality.** Every unifier is an instance of the bindings: it
absorbs them. -/
theorem unify_most_general {t u : Pattern} {bs : Bindings} (found : unify t u = some bs)
    (τ : PSubst) (solves : psubst τ t = psubst τ u) (p : Pattern) :
    psubst τ (psubst bs.lookup p) = psubst τ p := by
  obtain ⟨θ, total, relevant, _, agree⟩ := unify_spec found
  have unifies : Unifies (lift τ) [(encode t, encode u)] := by
    intro pair member
    rw [List.mem_singleton] at member
    subst member
    simp only [← encode_psubst, solves]
  have absorbs := Mettapedia.Logic.LP.Subst.absorbs_of_moreGeneral relevant.absorbs
    (unifyTotal_mgu _ θ total (lift τ) unifies)
  rw [agree]
  apply encode_injective
  rw [encode_psubst, encode_psubst_lower, ← Mettapedia.Logic.LP.Subst.applyTerm_comp,
    absorbs.comp_eq, encode_psubst]

/-- **Completeness.** A unifiable pair always gets bindings. -/
theorem unify_complete {t u : Pattern} (solvable : ∃ τ : PSubst, psubst τ t = psubst τ u) :
    ∃ bs, unify t u = some bs := by
  obtain ⟨τ, solves⟩ := solvable
  have unifies : Unifies (lift τ) [(encode t, encode u)] := by
    intro pair member
    rw [List.mem_singleton] at member
    subst member
    simp only [← encode_psubst, solves]
  obtain ⟨θ, total⟩ := unifyTotal_complete ⟨lift τ, unifies⟩
  exact ⟨toBindings θ (patternVariables t u), by simp [unify, unifier_eq, total]⟩

/-- `none` is a genuine failure: no substitution unifies the pair. -/
theorem unify_eq_none_iff (t u : Pattern) :
    unify t u = none ↔ ¬ ∃ τ : PSubst, psubst τ t = psubst τ u := by
  constructor
  · intro failed solvable
    obtain ⟨bs, found⟩ := unify_complete solvable
    rw [failed] at found
    cases found
  · intro unsolvable
    cases result : unify t u with
    | none => rfl
    | some bs => exact absurd ⟨_, unify_sound result⟩ unsolvable

/-- **Relevance.** Bindings are keyed by variables of the two patterns. -/
theorem unify_keys {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    ∀ entry ∈ bs, entry.1 ∈ pvars t ++ pvars u := by
  obtain ⟨θ, _, _, rfl, _⟩ := unify_spec found
  intro entry member
  simp only [toBindings, List.mem_filterMap] at member
  obtain ⟨v, inside, produced⟩ := member
  split at produced
  · cases produced
  · cases produced
    simpa [patternVariables] using inside

/-- **Relevance.** Bound values mention only variables of the two patterns. -/
theorem unify_value_vars {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    ∀ entry ∈ bs, ∀ x ∈ pvars entry.2, x ∈ pvars t ++ pvars u := by
  obtain ⟨θ, _, relevant, rfl, _⟩ := unify_spec found
  intro entry member x occurs
  simp only [toBindings, List.mem_filterMap] at member
  obtain ⟨v, inside, produced⟩ := member
  split at produced
  · cases produced
  · cases produced
    rw [mem_pvars_decode] at occurs
    have inV : v ∈ eqVars [(encode t, encode u)] := by
      rw [mem_eqVars_pair]; simpa [patternVariables] using inside
    exact (mem_eqVars_pair t u x).mp (relevant.range v inV occurs)

/-- **One pass.** Every bound value is already final: none of its variables is
bound. This is what a triangular binding list lacks. -/
theorem unify_value_unbound {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) :
    ∀ entry ∈ bs, ∀ x ∈ pvars entry.2, bs.lookup x = none := by
  obtain ⟨θ, _, relevant, rfl, _⟩ := unify_spec found
  intro entry member x occurs
  simp only [toBindings, List.mem_filterMap] at member
  obtain ⟨v, inside, produced⟩ := member
  split at produced
  · cases produced
  · cases produced
    rw [mem_pvars_decode] at occurs
    apply lookup_toBindings_of_fixed
    rw [relevant.unbound v x occurs]
    rfl

/-- **Applying the unifier is the manuscript's dot.** One pass of the dotted
bindings replaces each variable the unifier binds by the quotation of its
value, and every value is already final, so one pass is the whole
substitution `P·σ̇` of the idempotent most general unifier. -/
theorem applyDot_unify {t u : Pattern} {bs : Bindings} (found : unify t u = some bs) (P : Pattern)
    (fo : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.firstOrder P =
      true) :
    applyDot bs P = psubst (fun x => (bs.lookup x).map nQuote) P ∧
      ∀ x w, bs.lookup x = some w → psubst bs.lookup w = w := by
  refine ⟨Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.applyDot_eq
    bs P fo, ?_⟩
  intro x w lookupX
  have member : (x, w) ∈ bs := by
    unfold Bindings.lookup at lookupX
    cases findX : bs.find? (fun entry => entry.1 == x) with
    | none => rw [findX] at lookupX; cases lookupX
    | some entry =>
        rw [findX] at lookupX
        simp only [Option.map_some, Option.some.injEq] at lookupX
        have inside := List.mem_of_find?_eq_some findX
        have key := List.find?_some findX
        simp only [beq_iff_eq] at key
        obtain ⟨k, value⟩ := entry
        simp only at key lookupX
        subst key lookupX
        exact inside
  have unbound := unify_value_unbound found (x, w) member
  rw [Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_congr
      bs.lookup (fun _ => none) w (fun y occurs => by simpa using unbound y occurs),
    Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_none]

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
