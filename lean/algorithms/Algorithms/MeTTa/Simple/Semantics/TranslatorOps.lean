import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.TranslatorOps

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  rewrites : σ → List RewriteRule
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings

def headOfTranslatorArg? : Pattern → Option String
  | .apply head [] =>
      let h := head.trimAscii.toString
      if h.isEmpty then none else some h
  | .fvar v =>
      let h := v.trimAscii.toString
      if h.isEmpty then none else some h
  | _ => none

def addHead (heads : List String) (arg : Pattern) : List String :=
  match headOfTranslatorArg? arg with
  | none => heads
  | some h =>
      if heads.contains h then heads else h :: heads

def removeHead (heads : List String) (arg : Pattern) : List String :=
  match headOfTranslatorArg? arg with
  | none => heads
  | some h => heads.filter (fun x => x != h)

def hasHead (heads : List String) (head : String) : Bool :=
  heads.contains head

mutual
private def renameFVarsWith (tag : String) : Pattern → Pattern
  | .fvar x => .fvar (tag ++ x)
  | .bvar n => .bvar n
  | .apply ctor args =>
      let ctor' :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then ctor else "$" ++ tag ++ name
        else
          ctor
      .apply ctor' (renameFVarsWithList tag args)
  | .lambda body => .lambda (renameFVarsWith tag body)
  | .multiLambda n body => .multiLambda n (renameFVarsWith tag body)
  | .subst body repl => .subst (renameFVarsWith tag body) (renameFVarsWith tag repl)
  | .collection ct elems rest => .collection ct (renameFVarsWithList tag elems) rest

private def renameFVarsWithList (tag : String) : List Pattern → List Pattern
  | [] => []
  | x :: xs => renameFVarsWith tag x :: renameFVarsWithList tag xs
end

private theorem renameFVarsWithList_eq_map (tag : String) (args : List Pattern) :
    renameFVarsWithList tag args = args.map (renameFVarsWith tag) := by
  induction args with
  | nil => simp [renameFVarsWithList]
  | cons x xs ih => simp [renameFVarsWithList, ih]

/-- When `ctor` does not start with "$", `renameFVarsWith` preserves the head. -/
private theorem renameFVarsWith_apply_head_noDollar (tag : String) (ctor : String)
    (args : List Pattern) (hND : ctor.startsWith "$" = false) :
    renameFVarsWith tag (.apply ctor args) =
      .apply ctor (renameFVarsWithList tag args) := by
  simp [renameFVarsWith, hND]

private def unwrapQuote : Pattern → Pattern
  | .apply "quote" [q] => q
  | p => p

def translateCall (I : Interface σ) (s : σ) (enabledHeads : List String)
    (term : Pattern) : List Pattern :=
  match term with
  | .apply head _ =>
      if !hasHead enabledHeads head then
        []
      else
        (I.rewrites s).flatMap fun rule =>
          if rule.premises.isEmpty then
            let tag := s!"__tr::{rule.name}::"
            let leftFresh := renameFVarsWith tag rule.left
            let rightFresh := renameFVarsWith tag rule.right
            match leftFresh with
            | .apply lHead _ =>
                if lHead == head then
                  (I.matchPattern leftFresh term).map
                    (fun (bs : Bindings) => unwrapQuote (I.applyBindings bs rightFresh))
                else
                  []
            | _ => []
          else
            []
  | _ => []

-- ─── Separation theorem ─────────────────────────────────────────────────────

theorem flatMap_eq_nil_of_forall {α β : Type _} (l : List α) (f : α → List β)
    (h : ∀ x ∈ l, f x = []) : l.flatMap f = [] := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.flatMap_cons, h hd List.mem_cons_self,
          ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `translateCall` returns `[]` for `.apply ctor args` when every rule's LHS
    is `.apply h _` with `h ≠ ctor` and `¬h.startsWith "$"`,
    or is a non-`.apply`/non-`.fvar` pattern. -/
theorem translateCall_empty_of_no_head_match
    (I : Interface σ) (s : σ) (enabledHeads : List String)
    (ctor : String) (args : List Pattern)
    (hRules : ∀ r ∈ I.rewrites s,
      (∀ h as, r.left = .apply h as → h ≠ ctor ∧ h.startsWith "$" = false) ∧
      (∀ x, r.left ≠ .fvar x)) :
    translateCall I s enabledHeads (.apply ctor args) = [] := by
  unfold translateCall
  by_cases hH : (!hasHead enabledHeads ctor) = true
  · simp [hH]
  · simp only [Bool.not_eq_true'] at hH
    simp only [hH]
    apply flatMap_eq_nil_of_forall
    intro rule hrule
    obtain ⟨hHead, hNoFvar⟩ := hRules rule hrule
    by_cases hPrem : rule.premises.isEmpty
    · simp only [hPrem, ite_true]
      cases hL : rule.left with
      | apply h as =>
          obtain ⟨hNe, hND⟩ := hHead h as hL
          rw [renameFVarsWith_apply_head_noDollar _ h as hND]
          simp only [BEq.beq]
          split
          · next hEq =>
              have := of_decide_eq_true hEq
              exact absurd this hNe
          · rfl
      | fvar x => exact absurd hL (hNoFvar x)
      | bvar n => simp [renameFVarsWith]
      | lambda body => simp [renameFVarsWith]
      | multiLambda n body => simp [renameFVarsWith]
      | subst body repl => simp [renameFVarsWith]
      | collection ct elems rest => simp [renameFVarsWith]
    · simp at hPrem
      simp [hPrem]

end Algorithms.MeTTa.Simple.Semantics.TranslatorOps
