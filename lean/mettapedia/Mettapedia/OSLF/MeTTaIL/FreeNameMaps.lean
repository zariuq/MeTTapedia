import Mettapedia.OSLF.MeTTaIL.NameSubstitutionLaws

/-!
# Free names mapped through a function

`mapFVars f` renames every free name `n` of a pattern to `f n`, keeping bound levels and collection rests. On patterns
without explicit substitutions:

- substituting one name for another is mapping by the function that updates it (`applySubst_single_eq_mapFVars`);
- maps compose (`mapFVars_mapFVars`), and a map is determined by its values on the free names
  (`mapFVars_congr`);
- maps keep the absence of explicit substitutions (`noExplicitSubst_mapFVars`);
- maps commute with opening a binder at a free name, which is mapped too (`mapFVars_openBVar`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Substitution

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **Free names mapped**: every free name `n` becomes `f n`; bound levels and collection rests are kept. -/
def mapFVars (f : String → String) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar name => .fvar (f name)
  | .apply constructor args => .apply constructor (args.map (mapFVars f))
  | .lambda name body => .lambda name (mapFVars f body)
  | .multiLambda count names body => .multiLambda count names (mapFVars f body)
  | .subst body replacement => .subst (mapFVars f body) (mapFVars f replacement)
  | .collection kind elements rest => .collection kind (elements.map (mapFVars f)) rest
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem noExplicitSubst_mapFVars (f : String → String) (pattern : Pattern) :
    noExplicitSubst (mapFVars f pattern) = noExplicitSubst pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => simp [mapFVars, noExplicitSubst]
  | hfvar _ => simp [mapFVars, noExplicitSubst]
  | happly c args ih =>
    simp only [mapFVars, noExplicitSubst]
    induction args with
    | nil => rfl
    | cons head tail tailIh =>
      simp only [List.map_cons, allNoExplicitSubst]
      rw [ih head List.mem_cons_self, tailIh fun a member => ih a (List.mem_cons_of_mem _ member)]
  | hlambda _ body ih => simp only [mapFVars, noExplicitSubst, ih]
  | hmultiLambda _ _ body ih => simp only [mapFVars, noExplicitSubst, ih]
  | hsubst body replacement _ _ => simp [mapFVars, noExplicitSubst]
  | hcollection kind elements rest ih =>
    simp only [mapFVars, noExplicitSubst]
    induction elements with
    | nil => rfl
    | cons head tail tailIh =>
      simp only [List.map_cons, allNoExplicitSubst]
      rw [ih head List.mem_cons_self, tailIh fun a member => ih a (List.mem_cons_of_mem _ member)]

/-- **Substituting a name is mapping by the update.** -/
theorem applySubst_single_eq_mapFVars (old new : String) (pattern : Pattern) (normal : noExplicitSubst pattern = true) :
    applySubst [(old, .fvar new)] pattern = mapFVars (fun name => if name = old then new else name) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => simp [applySubst, mapFVars]
  | hfvar name => rw [applySubst_fvar_single, mapFVars]
  | happly c args ih =>
    simp only [applySubst, mapFVars]
    congr 1
    exact List.map_congr_left fun a member => ih a member (allNoExplicitSubst_mem normal member)
  | hlambda _ body ih => simp only [applySubst, mapFVars]; congr 1; exact ih normal
  | hmultiLambda _ _ body ih => simp only [applySubst, mapFVars]; congr 1; exact ih normal
  | hsubst body replacement _ _ =>
    have : noExplicitSubst (.subst body replacement) = false := rfl
    rw [this] at normal
    exact absurd normal Bool.false_ne_true
  | hcollection kind elements rest ih =>
    simp only [applySubst, mapFVars]
    congr 1
    exact List.map_congr_left fun a member => ih a member (allNoExplicitSubst_mem normal member)

/-- **Maps compose.** -/
theorem mapFVars_mapFVars (f g : String → String) (pattern : Pattern) :
    mapFVars f (mapFVars g pattern) = mapFVars (f ∘ g) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => simp [mapFVars]
  | hfvar _ => simp [mapFVars]
  | happly c args ih =>
    simp only [mapFVars, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member
  | hlambda _ body ih => simp only [mapFVars, ih]
  | hmultiLambda _ _ body ih => simp only [mapFVars, ih]
  | hsubst body replacement bodyIh replacementIh => simp only [mapFVars, bodyIh, replacementIh]
  | hcollection kind elements rest ih =>
    simp only [mapFVars, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member

/-- **A map is determined by its values on the free names.** -/
theorem mapFVars_congr {f g : String → String} (pattern : Pattern) (agree : ∀ name ∈ freeVars pattern, f name = g name) :
    mapFVars f pattern = mapFVars g pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => simp [mapFVars]
  | hfvar name => simp [mapFVars, agree name (by simp [freeVars])]
  | happly c args ih =>
    simp only [mapFVars]
    congr 1
    refine List.map_congr_left fun a member => ih a member fun name inside => agree name ?_
    simp only [freeVars, List.mem_flatMap]
    exact ⟨a, member, inside⟩
  | hlambda _ body ih =>
    simp only [mapFVars]
    congr 1
    exact ih fun name inside => agree name (by simpa [freeVars] using inside)
  | hmultiLambda _ _ body ih =>
    simp only [mapFVars]
    congr 1
    exact ih fun name inside => agree name (by simpa [freeVars] using inside)
  | hsubst body replacement bodyIh replacementIh =>
    simp only [mapFVars]
    rw [bodyIh fun name inside => agree name (by simp [freeVars, inside]),
      replacementIh fun name inside => agree name (by simp [freeVars, inside])]
  | hcollection kind elements rest ih =>
    simp only [mapFVars]
    congr 1
    refine List.map_congr_left fun a member => ih a member fun name inside => agree name ?_
    simp only [freeVars, List.mem_flatMap]
    exact ⟨a, member, inside⟩

theorem mapFVars_id (pattern : Pattern) : mapFVars (fun name => name) pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => simp [mapFVars]
  | hfvar _ => simp [mapFVars]
  | happly c args ih =>
    simp only [mapFVars]
    congr 1
    exact (List.map_congr_left (g := id) fun a member => ih a member).trans (List.map_id _)
  | hlambda _ body ih => simp only [mapFVars, ih]
  | hmultiLambda _ _ body ih => simp only [mapFVars, ih]
  | hsubst body replacement bodyIh replacementIh => simp only [mapFVars, bodyIh, replacementIh]
  | hcollection kind elements rest ih =>
    simp only [mapFVars]
    congr 1
    exact (List.map_congr_left (g := id) fun a member => ih a member).trans (List.map_id _)

/-- **Mapping free names commutes with opening at a free name**, which is mapped too. -/
theorem mapFVars_openBVar (f : String → String) (name : String) (pattern : Pattern) :
    ∀ k : Nat, mapFVars f (openBVar k (.fvar name) pattern) = openBVar k (.fvar (f name)) (mapFVars f pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar n =>
    intro k
    by_cases same : n = k
    · subst same; simp [openBVar, mapFVars]
    · simp [openBVar, mapFVars, same]
  | hfvar _ => intro k; simp [openBVar, mapFVars]
  | happly c args ih =>
    intro k
    simp only [openBVar, mapFVars, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member k
  | hlambda _ body ih => intro k; simp only [openBVar, mapFVars, ih]
  | hmultiLambda _ _ body ih => intro k; simp only [openBVar, mapFVars, ih]
  | hsubst body replacement bodyIh replacementIh => intro k; simp only [openBVar, mapFVars, bodyIh, replacementIh]
  | hcollection kind elements rest ih =>
    intro k
    simp only [openBVar, mapFVars, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member k

end Mettapedia.OSLF.MeTTaIL.Substitution
