import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshConnections
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Lexical fresh: fresh names as GSLT freshness premises

A GSLT rule states freshness as a premise `x # P` (`FreshnessCondition`,
`OSLF.MeTTaIL.Syntax`; in elaborated rules `CanonicalPremise.freshness`,
`GSLT.LanguageDef.CanonicalScopedPremise`), checked by `checkFreshness`: the
name is not a free variable of the pattern.

Read a model term as an OSLF pattern whose free variables are its slots
(`toPattern`, through an injective naming `enc` of slots; everything else is
structure).  Then the fresh slot a `let` pattern introduces passes the
freshness premise against the `let`'s value (`let_slot_freshness_premise`),
and a slot the value mentions fails it (`freshness_premise_fails`).  The
apartness is the model's `let_slot_fresh_in_value`: every slot an elaborated
term mentions comes from its environment or is introduced inside it.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

universe u v

variable {S : Type u} {X : Type v}

/-- A model term as an OSLF pattern: each slot is the free variable `enc k`;
other names, symbols and binders become structure. -/
def toPattern (enc : SlotId X → String) : Tm S (BId X) → Pattern
  | .var (.src (.slot k)) => .fvar (enc k)
  | .var _ => .apply "name" []
  | .sym _ => .apply "sym" []
  | .fn _ => .apply "fn" []
  | .pvar _ => .apply "par" []
  | .lam _ _ b => .apply "lam" [toPattern enc b]
  | .app f a => .apply "app" [toPattern enc f, toPattern enc a]
  | .quote c => .apply "quote" [toPattern enc c]
  | .ctx _ _ => .apply "ctx" []
  | .pquote c => .apply "pquote" [toPattern enc c]
  | .letP p w b => .apply "let" [toPattern enc p, toPattern enc w, toPattern enc b]
  | .alt t₁ t₂ => .apply "alt" [toPattern enc t₁, toPattern enc t₂]

/-- **The pattern's free variables are the term's slots.** -/
theorem freeVars_toPattern (enc : SlotId X → String) :
    ∀ t : Tm S (BId X), freeVars (toPattern enc t) = (slotKeys t).map enc
  | .var (.src (.slot k)) => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .var (.src (.par _ _)) => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .var (.src (.code _ _)) => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .var (.inst _ _) => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .sym _ => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .fn _ => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .pvar _ => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .lam _ _ b => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc b]
      simp [slotKeys, Tm.vars]
  | .app f a => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc f, freeVars_toPattern enc a]
      simp [slotKeys, Tm.vars, List.filterMap_append]
  | .quote c => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc c]
      simp [slotKeys, Tm.vars]
  | .ctx _ _ => by simp [toPattern, freeVars, slotKeys, Tm.vars]
  | .pquote c => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc c]
      simp [slotKeys, Tm.vars]
  | .letP p w b => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc p, freeVars_toPattern enc w, freeVars_toPattern enc b]
      simp [slotKeys, Tm.vars, List.filterMap_append]
  | .alt t₁ t₂ => by
      simp only [toPattern, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        freeVars_toPattern enc t₁, freeVars_toPattern enc t₂]
      simp [slotKeys, Tm.vars, List.filterMap_append]

/-- Under an injective naming, the freshness premise for a slot is that the
term does not mention it. -/
theorem checkFreshness_toPattern {enc : SlotId X → String} (henc : Function.Injective enc)
    (k : SlotId X) (t : Tm S (BId X)) :
    checkFreshness ⟨enc k, toPattern enc t⟩ = true ↔ k ∉ slotKeys t := by
  have h : checkFreshness ⟨enc k, toPattern enc t⟩ = !((slotKeys t).map enc).contains (enc k) := by
    simp only [checkFreshness, isFresh, freeVars_toPattern]
  rw [h]
  cases hc : ((slotKeys t).map enc).contains (enc k) with
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_not]
      obtain ⟨k', hk', he⟩ := List.mem_map.1 (List.contains_iff_mem.1 hc)
      exact henc he ▸ hk'
  | false =>
      simp only [Bool.not_false, true_iff]
      intro hk
      have hm := List.contains_iff_mem.2 (List.mem_map.2 ⟨k, hk, rfl⟩ : enc k ∈ (slotKeys t).map enc)
      rw [hc] at hm
      cases hm

variable [DecidableEq X]

/-- **A pattern's fresh slot passes the GSLT freshness premise** against the
`let`'s value, `enc k # ⟦w⟧`: the slot the `let` at `P` introduces is not a free
variable of the value's pattern, unless the environment already held it. -/
theorem let_slot_freshness_premise {enc : SlotId X → String} (henc : Function.Injective enc)
    (cr : List X) (env : IEnv X) (pv : X → Owner) (fr P : Owner) (w : Src S X) {k : SlotId X}
    (hk : k.site = P) (henv : ∀ y, env y ≠ k) (hnot : ¬ rootHead k) :
    checkFreshness ⟨enc k, toPattern enc (elabLFId cr env pv fr (P ++ [1]) w)⟩ = true :=
  (checkFreshness_toPattern henc k _).2 (let_slot_fresh_in_value cr env pv fr P w hk henv hnot)

omit [DecidableEq X] in
/-- **Negative**: a slot that a term mentions fails the premise. -/
theorem freshness_premise_fails {enc : SlotId X → String} (henc : Function.Injective enc)
    (k : SlotId X) (t : Tm S (BId X)) (hk : k ∈ slotKeys t) :
    checkFreshness ⟨enc k, toPattern enc t⟩ = false := by
  cases h : checkFreshness ⟨enc k, toPattern enc t⟩ with
  | false => rfl
  | true => exact absurd hk ((checkFreshness_toPattern henc k t).1 h)

end Mettapedia.GSLT.LanguageDef.TemplateScope
