import Mettapedia.GSLT.Contracts.LiveAliasRepair
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores
import Mathlib.Data.List.Forall2

/-! Extending an authored language with a stream of space additions. The
original rows remain in the space: this is its derived literal-root rule
view. Adding a fact, a directional rule, and an equation do different work.
Admission is checked on the assembled language; refusal of this view is not
an assertion that the source program has no answers. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.LiveModuleEdits

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.Contracts.LiveAliasRepair
open DefinitionalEquations

inductive Order where
  | front | back
  deriving DecidableEq

def Order.insert {T : Type*} : Order → T → List T → List T
  | .front, x, xs => x :: xs
  | .back, x, xs => xs ++ [x]

inductive Edit (Data : Type*) where
  | datum (value : Data)
  | rule (r : RewriteRule)
  | equation (e : Equation)

variable {D : Type*}

/-- Rule enumeration follows the selected space order. The presentation of
definitions is in dependency order, not the enumeration order of raw facts. -/
def publish (o : Order) (l : LanguageDef) : Edit D → LanguageDef
  | .datum _ => l
  | .rule r => { l with rewrites := o.insert r l.rewrites }
  | .equation e => { l with equations := l.equations ++ [e] }

def literal (l : LanguageDef) (r : RewriteRule) : Bool :=
  r.typeContext.isEmpty && r.premises.isEmpty &&
    DecidableRelations.isFirstOrder r.left && DecidableRelations.isFirstOrder r.right &&
    l.typeNames.any fun sort =>
      WellSorted.checkHasType l WellSorted.FreeTypeContext.empty [] r.left (.base sort) &&
      WellSorted.checkHasType l WellSorted.FreeTypeContext.empty [] r.right (.base sort)

def admitted (l : LanguageDef) : Bool :=
  checkDefinitional l && l.rewrites.all (literal l)

theorem rule_has_common_sort (l : LanguageDef) (r : RewriteRule) (ok : literal l r = true) :
    ∃ sort ∈ l.typeNames, WellSorted.HasType l WellSorted.FreeTypeContext.empty [] r.left (.base sort) ∧
      WellSorted.HasType l WellSorted.FreeTypeContext.empty [] r.right (.base sort) := by
  simp only [literal, Bool.and_eq_true, List.any_eq_true] at ok
  obtain ⟨s, hs, lhs, rhs⟩ := ok.2
  exact ⟨s, hs, WellSorted.checkHasType_sound lhs, WellSorted.checkHasType_sound rhs⟩

private theorem definitional_of_admitted {l : LanguageDef} (h : admitted l = true) :
    checkDefinitional l = true := by
  simp only [admitted, Bool.and_eq_true] at h
  exact h.1

abbrev Keys (l : LanguageDef) := Fin l.rewrites.length → Pattern

def build (l : LanguageDef) : Keys l :=
  fun i => expand (definitions l) (l.rewrites[i].left)

private def insertKey {T K : Type*} (o : Order) (rs : List T) (r : T)
    (prior : Fin rs.length → K) (newKey : K) : Fin (o.insert r rs).length → K :=
  match o with
  | .front => Fin.cases newKey prior
  | .back => fun i => if h : i.val < rs.length then prior ⟨i.val, h⟩ else newKey

private theorem insertKey_full {T K : Type*} (o : Order) (rs : List T) (r : T) (key : T → K) :
    insertKey o rs r (fun i => key rs[i.val]) (key r) = fun i => key (o.insert r rs)[i.val] := by
  cases o with
  | front =>
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  | back =>
    funext i
    by_cases h : i.val < rs.length
    · simp [insertKey, Order.insert, h, List.getElem_append_left]
    · have pos : i.val = rs.length := by
        have bound := i.isLt
        simp [Order.insert] at bound
        omega
      simp [insertKey, Order.insert, List.getElem_append_right, pos]

private theorem definitions_extend (l : LanguageDef) (e : Equation) (d : Row)
    (valid : checkDefinitional l = true) (read : rowOf? e = some d) :
    definitions { l with equations := l.equations ++ [e] } = definitions l ++ [d] := by
  have paired := List.rel_append (checkDefinitional_sound valid).authored
    (List.Forall₂.cons (rowOf?_sound read) List.Forall₂.nil)
  exact congrArg (fun result : Option (List Row) => result.getD []) (rows?_complete paired)

def posting (l : LanguageDef) (head : String) : List (Fin l.rewrites.length) :=
  (List.finRange l.rewrites.length).filter fun i => !checkAvoids head l.rewrites[i].left

/-- The update algorithm. A datum does not touch the table. A new literal
rule gets one new key. An admitted equation repairs just the constructor
posting for its head; the reference computes that posting from syntax. -/
def update? (o : Order) (l : LanguageDef) (keys : Keys l) :
    (event : Edit D) → Option (Keys (publish o l event))
  | .datum _ => some keys
  | .rule r =>
    if admitted { l with rewrites := o.insert r l.rewrites } then
      some (insertKey o l.rewrites r keys (expand (definitions l) r.left))
    else none
  | .equation e => do
    let d ← rowOf? e
    if admitted { l with equations := l.equations ++ [e] } then
      let lhs := fun i : Fin l.rewrites.length => l.rewrites[i].left
      some (patch keys (fun i => expand (definitions l ++ [d]) (lhs i))
        (posting l d.head))
    else none

theorem update_available_iff (o : Order) (l : LanguageDef) (valid : admitted l = true)
    (keys : Keys l) (e : Edit D) :
    (update? o l keys e).isSome = true ↔ admitted (publish o l e) = true := by
  cases e with
  | datum => simp [update?, publish, valid]
  | rule r =>
    cases good : admitted { l with rewrites := o.insert r l.rewrites } <;> simp [update?, publish, good]
  | equation e =>
    cases good : admitted { l with equations := l.equations ++ [e] } with
    | false => cases he : rowOf? e <;> simp [update?, publish, he, good]
    | true =>
      obtain ⟨d, _, defined⟩ := (checkDefinitional_sound (definitional_of_admitted good)).presents.defined
        e (by change e ∈ l.equations ++ [e]; simp)
      simp [update?, publish, rowOf?_complete defined, good]

theorem update_exact (o : Order) (l : LanguageDef) (valid : admitted l = true)
    (keys : Keys l) (was : keys = build l) (event : Edit D) {out : Keys (publish o l event)}
    (loaded : update? o l keys event = some out) :
    admitted (publish o l event) = true ∧ out = build (publish o l event) := by
  subst keys
  cases event with
  | datum => exact ⟨valid, (Option.some.inj loaded).symm⟩
  | rule r =>
    simp only [update?] at loaded
    split at loaded
    · rename_i h
      refine ⟨h, (Option.some.inj loaded).symm.trans ?_⟩
      exact insertKey_full o l.rewrites r (fun r => expand (definitions l) r.left)
    · cases loaded
  | equation e =>
    cases he : rowOf? e with
    | none => simp [update?, he] at loaded
    | some d =>
      simp only [update?, he] at loaded
      split at loaded
      · rename_i h
        refine ⟨h, (Option.some.inj loaded).symm.trans ?_⟩
        have defs := definitions_extend l e d (definitional_of_admitted valid) he
        change patch (build l) _ _ = fun i => expand (definitions {l with equations := l.equations ++ [e]}) _
        rw [defs]
        exact repair_using (fun i : Fin l.rewrites.length => l.rewrites[i].left) (definitions l) d
          (posting l d.head) (fun i touched => by simp [posting]; exact touched)
      · cases loaded

def resulting (o : Order) (l : LanguageDef) (edits : List (Edit D)) : LanguageDef :=
  edits.foldl (publish o) l

def run? (o : Order) (l : LanguageDef) (keys : Keys l) :
    (edits : List (Edit D)) → Option (Keys (resulting o l edits))
  | [] => some keys
  | event :: rest => do
    let next ← update? o l keys event
    run? o (publish o l event) next rest

theorem run_exact (o : Order) (l : LanguageDef) (valid : admitted l = true)
    (keys : Keys l) (was : keys = build l) (edits : List (Edit D)) {out}
    (loaded : run? o l keys edits = some out) :
    admitted (resulting o l edits) = true ∧ out = build (resulting o l edits) := by
  induction edits generalizing l with
  | nil => exact ⟨valid, (Option.some.inj loaded).symm.trans was⟩
  | cons e rest ih =>
    obtain ⟨next, installed, ran⟩ := Option.bind_eq_some_iff.mp loaded
    obtain ⟨supported, same⟩ := update_exact o l valid keys was e installed
    exact ih _ supported next same ran

def answers (l : LanguageDef) (keys : Keys l) (q : Pattern) : List RewriteRule :=
  Contracts.ScopedAliasDispatch.lookup (expand (definitions l) q)
    (List.ofFn fun i => (keys i, l.rewrites[i]))

/-- Fresh construction of the keys implements ordered modulo-equation dispatch. -/
theorem answers_build (base : BasePremiseEvaluator) (l : LanguageDef) (valid : admitted l = true)
    (q : Pattern) : answers l (build l) q =
      Contracts.ScopedAliasDispatch.moduloRead base l RewriteRule.left q l.rewrites := by
  have cert := checkDefinitional_sound (definitional_of_admitted valid)
  have enumeration : (List.ofFn fun i : Fin l.rewrites.length => (build l i, l.rewrites[i])) =
      Contracts.ScopedAliasDispatch.index (expand (definitions l)) RewriteRule.left l.rewrites := by
    apply List.ext_getElem <;> simp [Contracts.ScopedAliasDispatch.index, build]
  unfold answers
  rw [enumeration]
  exact Contracts.ScopedAliasDispatch.indexed_eq_modulo base cert.acyclic cert.presents cert.noBags
    cert.noSets cert.noAlgebra _ _ _

/-- Source comparison uses the authored equation relation, not equality of
cached keys. This preserves the whole ordered word, even duplicate rules. -/
theorem answers_after_edits (base : BasePremiseEvaluator) (o : Order) (l : LanguageDef)
    (supported : admitted l = true) (edits : List (Edit D)) {out}
    (ran : run? o l (build l) edits = some out) (q : Pattern) :
    let next := resulting o l edits
    answers next out q =
      Contracts.ScopedAliasDispatch.moduloRead base next RewriteRule.left q next.rewrites := by
  obtain ⟨valid, rfl⟩ := run_exact o l supported _ rfl edits ran
  exact answers_build base _ valid q

end Mettapedia.GSLT.LanguageDef.LiveModuleEdits
