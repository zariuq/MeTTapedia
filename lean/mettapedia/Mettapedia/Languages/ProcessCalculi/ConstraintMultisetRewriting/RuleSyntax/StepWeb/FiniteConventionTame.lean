import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

/-!
# Tameness and hostedness along renaming, alpha-equivalence and COMM

Facts that let the source of the hosting up to alpha-equivalence (`FiniteConventionSteps`) ask nothing beyond
tameness of the bags it steps from.

* `tame_rename`, `tame_canon`: renaming and the canonical renaming keep a process tame.
* `groundPrincipal_values`: the values of a ground principal unifier of two tame patterns are guard-free calculus
  terms. A unifier composed with a homomorphism onto calculus syntax (`toCalculus`), or onto guard-free syntax
  (`Corrected.eraseGuards`), is again a unifier, and the ground principal unifier absorbs it.
* `tame_applyDot`, `bagComm_keeps_tame`: so the dotted continuations of tame inputs are tame, and a COMM step of
  the bag presentation keeps a bag tame.
* `hosted_of_alphaEq`: a tame process alpha-equivalent to a tame hosted part is hosted. The canonical renaming
  keeps the number of variable occurrences and of binders (`length_pvars_canon`, `length_binders_canon`), so the
  common canonical form tells the channel ground and the continuation closed and free of binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot)
open MeTTaOperationsComm (psubst pvars firstOrder PSubst GroundPrincipal applyDot_eq psubst_pFor)
open MeTTaCalculus.Corrected (binders binders_apply bindersFor_cons3 bindersFor_short tame tameList tameFor
  tameList_iff tame_pFor tame_calcTerm calcTerm calcList calcList_iff guardFree guardFreeList guardFreeList_iff
  canon canonList canonFor canonList_eq_map canon_pFor canon_eq_named named canonicalName canonicalName_injective
  AvoidsCanonical levelRename AlphaEq close frame frame_of_guardFree rename rename_apply rename_collection
  pvars_rename binders_rename calcTerm_rename guardFree_rename psubstList_eq_map pvars_apply pvarsList_eq_flatMap
  bindersList_eq_flatMap eraseGuards eraseGuards_psubst eraseGuards_of_guardFree guardFree_eraseGuards
  firstOrder_of_calcTerm freshName freshName_not_mem pvars_pFor)
open FiniteProgram (parts Hosted BagComm pFor_inj binders_of_ground mem_keys_of_lookup)

/-! ## Renaming and the canonical renaming keep tameness -/

theorem tame_rename (g : String → String) (p : Pattern) : tame (rename g p) = tame p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame (rename g q) = tame q) with
  | bvar k => rfl
  | fvar x => rfl
  | apply c args ih =>
      rw [rename_apply]
      by_cases isFor : c = "MFor"
      · simp only [tame, if_pos isFor]
        match args, ih with
        | [t, x, k], ih =>
            simp only [List.map_cons, List.map_nil, tameFor, calcTerm_rename, guardFree_rename,
              ih x (by simp), ih k (by simp)]
        | [], _ => rfl
        | [a], _ => rfl
        | [a, b], _ => rfl
        | a :: b :: d :: e :: rest, _ => rfl
      · simp only [tame, if_neg isFor]
        apply Bool.eq_iff_iff.mpr
        rw [tameList_iff, tameList_iff]
        constructor
        · intro each q member
          rw [← ih q member]
          exact each _ (List.mem_map_of_mem member)
        · intro each q member
          obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
          rw [ih r inArgs]
          exact each r inArgs
  | lambda nm b ih => rfl
  | multiLambda k nms b ih => rfl
  | subst b r ihb ihr => rfl
  | collection ct elems rest ih =>
      rw [rename_collection]
      simp only [tame]
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [tameList_iff, tameList_iff]
      constructor
      · intro each q member
        rw [← ih q member]
        exact each _ (List.mem_map_of_mem member)
      · intro each q member
        obtain ⟨r, inElems, rfl⟩ := List.mem_map.mp member
        rw [ih r inElems]
        exact each r inElems
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem tame_canon (n : ℕ → ℕ → String) (p : Pattern) : ∀ D, tame (canon n D p) = tame p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ D, tame (canon n D q) = tame q) with
  | bvar k => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro D
      simp only [canon]
      by_cases isFor : c = "MFor"
      · simp only [tame, if_pos isFor]
        match args, ih with
        | [t, x, k], ih =>
            simp only [canonFor, canonList, tameFor, calcTerm_rename, guardFree_rename, tame_rename,
              ih x (by simp) D, ih k (by simp) (D + 1)]
        | [], _ => rfl
        | [a], _ => rfl
        | [a, b], _ => rfl
        | a :: b :: d :: e :: rest, _ => rfl
      · simp only [tame, if_neg isFor, canonList_eq_map]
        apply Bool.eq_iff_iff.mpr
        rw [tameList_iff, tameList_iff]
        constructor
        · intro each q member
          rw [← ih q member D]
          exact each _ (List.mem_map_of_mem member)
        · intro each q member
          obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
          rw [ih r inArgs D]
          exact each r inArgs
  | lambda nm b ih => intro _; rfl
  | multiLambda k nms b ih => intro _; rfl
  | subst b r ihb ihr => intro _; rfl
  | collection ct elems rest ih =>
      intro D
      simp only [canon, canonList_eq_map, tame]
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [tameList_iff, tameList_iff]
      constructor
      · intro each q member
        rw [← ih q member D]
        exact each _ (List.mem_map_of_mem member)
      · intro each q member
        obtain ⟨r, inElems, rfl⟩ := List.mem_map.mp member
        rw [ih r inElems D]
        exact each r inElems
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member D
      rcases List.mem_cons.mp member with rfl | later
      · exact head D
      · exact tail q later D

/-- **The parts of a tame process renamed apart are tame.** -/
theorem tame_of_mem_parts_renameApart (P : Pattern) (tameP : tame P = true) :
    ∀ c ∈ parts (renameApart P), tame c = true := by
  intro c member
  rw [parts_renameApart] at member
  obtain ⟨i, small, rfl⟩ := List.mem_iff_getElem.mp member
  rw [List.getElem_mapIdx, tame_canon]
  exact tame_of_mem_parts P _ (List.getElem_mem _) tameP

/-! ## Substitution keeps the calculus fragment -/

theorem calcTerm_psubst {s : PSubst} (values : ∀ x v, s x = some v → calcTerm v = true) (p : Pattern)
    (calcP : calcTerm p = true) : calcTerm (psubst s p) = true := by
  revert calcP
  induction p using Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true → calcTerm (psubst s q) = true) with
  | bvar n => intro h; simp [calcTerm] at h
  | fvar x =>
      intro _
      show calcTerm ((s x).getD (.fvar x)) = true
      cases found : s x with
      | some v => exact values x v found
      | none => rfl
  | apply c args ih =>
      intro calcP
      simp only [calcTerm, calcList_iff] at calcP
      simp only [psubst, psubstList_eq_map, calcTerm, calcList_iff, List.mem_map]
      rintro q ⟨r, inArgs, rfl⟩
      exact ih r inArgs (calcP r inArgs)
  | lambda nm b ih => intro h; simp [calcTerm] at h
  | multiLambda k nms b ih => intro h; simp [calcTerm] at h
  | subst b r ihb ihr => intro h; simp [calcTerm] at h
  | collection ct elems rest ih =>
      intro calcP
      simp only [calcTerm, Bool.and_eq_true, calcList_iff] at calcP
      simp only [psubst, psubstList_eq_map, calcTerm, Bool.and_eq_true, calcList_iff, List.mem_map]
      refine ⟨calcP.1, ?_⟩
      rintro q ⟨r, inElems, rfl⟩
      exact ih r inElems (calcP.2 r inElems)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ
      · exact tail q later calcQ

theorem guardFree_psubst {s : PSubst} (values : ∀ x v, s x = some v → guardFree v = true) (p : Pattern)
    (free : guardFree p = true) : guardFree (psubst s p) = true := by
  revert free
  induction p using Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → guardFree (psubst s q) = true) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show guardFree ((s x).getD (.fvar x)) = true
      cases found : s x with
      | some v => exact values x v found
      | none => rfl
  | apply c args ih =>
      intro free
      simp only [guardFree, Bool.and_eq_true, guardFreeList_iff] at free
      simp only [psubst, psubstList_eq_map, guardFree, Bool.and_eq_true, guardFreeList_iff, List.mem_map]
      refine ⟨free.1, ?_⟩
      rintro q ⟨r, inArgs, rfl⟩
      exact ih r inArgs (free.2 r inArgs)
  | lambda nm b ih =>
      intro free
      simp only [psubst, guardFree] at free ⊢
      exact ih free
  | multiLambda k nms b ih =>
      intro free
      simp only [psubst, guardFree] at free ⊢
      exact ih free
  | subst b r ihb ihr =>
      intro free
      simp only [guardFree, Bool.and_eq_true] at free
      simp only [psubst, guardFree, Bool.and_eq_true]
      exact ⟨ihb free.1, ihr free.2⟩
  | collection ct elems rest ih =>
      intro free
      simp only [guardFree, guardFreeList_iff] at free
      simp only [psubst, psubstList_eq_map, guardFree, guardFreeList_iff, List.mem_map]
      rintro q ⟨r, inElems, rfl⟩
      exact ih r inElems (free r inElems)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

/-- A guard-free calculus term is tame. -/
theorem tame_of_guardFree_calcTerm (p : Pattern) (free : guardFree p = true) (calcP : calcTerm p = true) :
    tame p = true := by
  revert free calcP
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → calcTerm q = true →
      tame q = true) with
  | bvar n => intro _ h; simp [calcTerm] at h
  | fvar x => intro _ _; rfl
  | apply c args ih =>
      intro free calcP
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      simp only [calcTerm, calcList_iff] at calcP
      simp only [tame, if_neg free.1, tameList_iff]
      exact fun q member => ih q member (free.2 q member) (calcP q member)
  | lambda nm b ih => intro _ h; simp [calcTerm] at h
  | multiLambda k nms b ih => intro _ h; simp [calcTerm] at h
  | subst b r ihb ihr => intro _ h; simp [calcTerm] at h
  | collection ct elems rest ih =>
      intro free calcP
      simp only [guardFree, guardFreeList_iff] at free
      simp only [calcTerm, Bool.and_eq_true, calcList_iff] at calcP
      simp only [tame, Bool.and_eq_true, tameList_iff]
      exact ⟨calcP.1, fun q member => ih q member (free q member) (calcP.2 q member)⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ calcQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ calcQ
      · exact tail q later freeQ calcQ

/-- **Substituting guard-free calculus terms keeps a process tame**: guards' patterns stay guard-free calculus
patterns. -/
theorem tame_psubst {s : PSubst} (values : ∀ x v, s x = some v → guardFree v = true ∧ calcTerm v = true)
    (p : Pattern) (tameP : tame p = true) : tame (psubst s p) = true := by
  revert tameP
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true → tame (psubst s q) = true) with
  | bvar n => intro h; simp [tame] at h
  | fvar x =>
      intro _
      show tame ((s x).getD (.fvar x)) = true
      cases found : s x with
      | some v => exact tame_of_guardFree_calcTerm v (values x v found).1 (values x v found).2
      | none => rfl
  | apply c args ih =>
      intro tameP
      by_cases isFor : c = "MFor"
      · subst isFor
        obtain ⟨t, x, k, rfl, calcT, freeT, tameX, tameK⟩ :=
          (MeTTaCalculus.Corrected.tameFor_iff args).mp (by simpa [tame] using tameP)
        show tame (psubst s (pFor t x k)) = true
        rw [psubst_pFor]
        exact tame_pFor.mpr ⟨calcTerm_psubst (fun x v found => (values x v found).2) t calcT,
          guardFree_psubst (fun x v found => (values x v found).1) t freeT,
          ih x (by simp) tameX, ih k (by simp) tameK⟩
      · simp only [tame, if_neg isFor, tameList_iff] at tameP
        simp only [psubst, psubstList_eq_map, tame, if_neg isFor, tameList_iff, List.mem_map]
        rintro q ⟨r, inArgs, rfl⟩
        exact ih r inArgs (tameP r inArgs)
  | lambda nm b ih => intro h; simp [tame] at h
  | multiLambda k nms b ih => intro h; simp [tame] at h
  | subst b r ihb ihr => intro h; simp [tame] at h
  | collection ct elems rest ih =>
      intro tameP
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [psubst, psubstList_eq_map, tame, Bool.and_eq_true, tameList_iff, List.mem_map]
      refine ⟨tameP.1, ?_⟩
      rintro q ⟨r, inElems, rfl⟩
      exact ih r inElems (tameP.2 r inElems)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ
      · exact tail q later tameQ

/-! ## The values of a ground principal unifier of tame patterns -/

mutual
/-- **The calculus image of a pattern**: every node outside calculus syntax becomes a constructor, a collection
loses its rest. A homomorphism for substitution that fixes calculus terms. -/
def toCalculus : Pattern → Pattern
  | .bvar _ => .apply "#code" []
  | .fvar x => .fvar x
  | .apply c args => .apply c (toCalculusList args)
  | .lambda _ body => .apply "#lambda" [toCalculus body]
  | .multiLambda _ _ body => .apply "#multiLambda" [toCalculus body]
  | .subst body repl => .apply "#subst" [toCalculus body, toCalculus repl]
  | .collection ct elems _ => .collection ct (toCalculusList elems) none
/-- The calculus image of a list. -/
def toCalculusList : List Pattern → List Pattern
  | [] => []
  | p :: ps => toCalculus p :: toCalculusList ps
end

theorem toCalculusList_eq_map (ps : List Pattern) : toCalculusList ps = ps.map toCalculus := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [toCalculusList, ih]

theorem calcTerm_toCalculus (p : Pattern) : calcTerm (toCalculus p) = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm (toCalculus q) = true) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [toCalculus, toCalculusList_eq_map, calcTerm, calcList_iff, List.mem_map]
      rintro q ⟨r, inArgs, rfl⟩
      exact ih r inArgs
  | lambda nm b ih => simp [toCalculus, calcTerm, calcList, ih]
  | multiLambda k nms b ih => simp [toCalculus, calcTerm, calcList, ih]
  | subst b r ihb ihr => simp [toCalculus, calcTerm, calcList, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [toCalculus, toCalculusList_eq_map, calcTerm, Bool.and_eq_true, calcList_iff, List.mem_map,
        Option.isNone_none, true_and]
      rintro q ⟨r, inElems, rfl⟩
      exact ih r inElems
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem toCalculus_of_calcTerm (p : Pattern) (calcP : calcTerm p = true) : toCalculus p = p := by
  revert calcP
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true → toCalculus q = q) with
  | bvar n => intro h; simp [calcTerm] at h
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro calcP
      simp only [calcTerm, calcList_iff] at calcP
      simp only [toCalculus, toCalculusList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left fun q member => ih q member (calcP q member)
  | lambda nm b ih => intro h; simp [calcTerm] at h
  | multiLambda k nms b ih => intro h; simp [calcTerm] at h
  | subst b r ihb ihr => intro h; simp [calcTerm] at h
  | collection ct elems rest ih =>
      intro calcP
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at calcP
      obtain ⟨rfl, calcP⟩ := calcP
      simp only [toCalculus, toCalculusList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member (calcP q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ
      · exact tail q later calcQ

theorem toCalculus_psubst (s : PSubst) (p : Pattern) :
    toCalculus (psubst s p) = psubst (fun x => (s x).map toCalculus) (toCalculus p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      toCalculus (psubst s q) = psubst (fun x => (s x).map toCalculus) (toCalculus q)) with
  | bvar n => rfl
  | fvar x => cases h : s x <;> simp [psubst, toCalculus, h]
  | apply c args ih =>
      simp only [psubst, toCalculus, psubstList_eq_map, toCalculusList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member
  | lambda nm body ih => simp [psubst, toCalculus, psubstList_eq_map, ih]
  | multiLambda n nms body ih => simp [psubst, toCalculus, psubstList_eq_map, ih]
  | subst body repl ihb ihr => simp [psubst, toCalculus, psubstList_eq_map, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, toCalculus, psubstList_eq_map, toCalculusList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-- **The values of a ground principal unifier of two tame patterns are guard-free calculus terms.** A unifier
composed with the calculus image, or with the erasure of guards, is again a unifier, and the ground principal
unifier absorbs it. -/
theorem groundPrincipal_values {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (calcT : calcTerm t = true) (calcU : calcTerm u = true) (freeT : guardFree t = true)
    (freeU : guardFree u = true) {v : String} {w : Pattern} (found : bs.lookup v = some w) :
    calcTerm w = true ∧ guardFree w = true := by
  have key := mem_keys_of_lookup gp.keys found
  constructor
  · have imageT := toCalculus_psubst bs.lookup t
    have imageU := toCalculus_psubst bs.lookup u
    rw [toCalculus_of_calcTerm t calcT] at imageT
    rw [toCalculus_of_calcTerm u calcU] at imageU
    have unifies : psubst (fun x => (bs.lookup x).map toCalculus) t =
        psubst (fun x => (bs.lookup x).map toCalculus) u := by
      rw [← imageT, ← imageU, gp.solves]
    have read := gp.principal _ unifies v key w found
    simp only [psubst, found, Option.map_some, Option.getD_some] at read
    rw [← read]
    exact calcTerm_toCalculus w
  · have erasedT := eraseGuards_psubst bs.lookup t
    have erasedU := eraseGuards_psubst bs.lookup u
    rw [eraseGuards_of_guardFree t freeT] at erasedT
    rw [eraseGuards_of_guardFree u freeU] at erasedU
    have unifies : psubst (fun x => (bs.lookup x).map eraseGuards) t =
        psubst (fun x => (bs.lookup x).map eraseGuards) u := by
      rw [← erasedT, ← erasedU, gp.solves]
    have read := gp.principal _ unifies v key w found
    simp only [psubst, found, Option.map_some, Option.getD_some] at read
    rw [← read]
    exact guardFree_eraseGuards w

/-- **The dot of a tame continuation by guard-free calculus values is tame.** -/
theorem tame_applyDot {bs : Bindings} (values : ∀ v w, bs.lookup v = some w → calcTerm w = true ∧ guardFree w = true)
    {A : Pattern} (tameA : tame A = true) : tame (applyDot bs A) = true := by
  rw [applyDot_eq bs A (firstOrder_of_calcTerm A (tame_calcTerm A tameA))]
  apply tame_psubst _ A tameA
  intro x v found
  obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨calcW, freeW⟩ := values x w look
  have quoteNotFor : ("MQuote" != "MFor") = true := by decide
  exact ⟨by simp [nQuote, guardFree, guardFreeList, freeW, quoteNotFor],
    by simp [nQuote, calcTerm, calcList, calcW]⟩

/-- **A COMM step of the bag presentation keeps a bag tame.** -/
theorem bagComm_keeps_tame {M M' : Multiset Pattern} (step : BagComm M M') (tameM : ∀ c ∈ M, tame c = true) :
    ∀ c ∈ M', tame c = true := by
  obtain ⟨t, u, x, A, B, bs, rest, gp, -, -⟩ := step
  obtain ⟨calcT, freeT, -, tameA⟩ := tame_pFor.mp (tameM _ (Multiset.mem_cons_self _ _))
  obtain ⟨calcU, freeU, -, tameB⟩ :=
    tame_pFor.mp (tameM _ (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)))
  have values : ∀ v w, bs.lookup v = some w → calcTerm w = true ∧ guardFree w = true := fun v w found =>
    groundPrincipal_values gp calcT calcU freeT freeU found
  intro c member
  rcases Multiset.mem_add.mp member with dotted | old
  · rcases Multiset.mem_add.mp dotted with fromA | fromB
    · exact tame_of_mem_parts _ c (Multiset.mem_coe.mp fromA) (tame_applyDot values tameA)
    · exact tame_of_mem_parts _ c (Multiset.mem_coe.mp fromB) (tame_applyDot values tameB)
  · exact tameM c (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem old))

/-! ## The canonical renaming keeps the numbers of variables and of binders -/

theorem length_flatMap_map {f : Pattern → List String} {h : Pattern → Pattern} :
    ∀ (l : List Pattern), (∀ q ∈ l, (f (h q)).length = (f q).length) →
      ((l.map h).flatMap f).length = (l.flatMap f).length
  | [], _ => rfl
  | q :: l, same => by
      simp only [List.map_cons, List.flatMap_cons, List.length_append]
      rw [same q (by simp), length_flatMap_map l fun r member => same r (by simp [member])]

theorem length_pvars_canon (n : ℕ → ℕ → String) (p : Pattern) :
    ∀ D, (pvars (canon n D p)).length = (pvars p).length := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ D,
      (pvars (canon n D q)).length = (pvars q).length) with
  | bvar k => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro D
      simp only [canon]
      rw [pvars_apply, pvars_apply, pvarsList_eq_flatMap, pvarsList_eq_flatMap]
      split_ifs with isFor
      · match args, ih with
        | [], _ => simp [canonFor]
        | [a], ih =>
            simp only [canonFor, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih a (by simp) D]
        | [a, b], ih =>
            simp only [canonFor, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
              ih a (by simp) D, ih b (by simp) D]
        | t :: x :: k :: rest, ih =>
            simp only [canonFor, canonList_eq_map, List.flatMap_cons, List.length_append, pvars_rename,
              List.length_map, ih x (by simp) D, ih k (by simp) (D + 1),
              length_flatMap_map (f := pvars) (h := canon n D) rest fun q member => ih q (by simp [member]) D]
      · rw [canonList_eq_map]
        exact length_flatMap_map (f := pvars) (h := canon n D) args fun q member => ih q member D
  | lambda nm b ih => intro _; rfl
  | multiLambda k nms b ih => intro _; rfl
  | subst b r ihb ihr => intro _; rfl
  | collection ct elems rest ih =>
      intro D
      simp only [canon, canonList_eq_map, pvars, pvarsList_eq_flatMap]
      exact length_flatMap_map (f := pvars) (h := canon n D) elems fun q member => ih q member D
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member D
      rcases List.mem_cons.mp member with rfl | later
      · exact head D
      · exact tail q later D

theorem length_binders_canon (n : ℕ → ℕ → String) (p : Pattern) :
    ∀ D, (binders (canon n D p)).length = (binders p).length := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ D,
      (binders (canon n D q)).length = (binders q).length) with
  | bvar k => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro D
      simp only [canon]
      rw [binders_apply, binders_apply]
      split_ifs with isFor
      · match args, ih with
        | [], _ => simp [canonFor, MeTTaCalculus.Corrected.bindersFor]
        | [a], ih =>
            simp only [canonFor]
            rw [bindersFor_short _ (by simp), bindersFor_short _ (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ih a (by simp) D]
        | [a, b], ih =>
            simp only [canonFor]
            rw [bindersFor_short _ (by simp), bindersFor_short _ (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
              ih a (by simp) D, ih b (by simp) D]
        | t :: x :: k :: rest, ih =>
            simp only [canonFor, canonList_eq_map]
            rw [bindersFor_cons3, bindersFor_cons3]
            simp only [List.length_append, pvars_rename, binders_rename, List.length_map,
              ih x (by simp) D, ih k (by simp) (D + 1),
              length_flatMap_map (f := binders) (h := canon n D) rest fun q member => ih q (by simp [member]) D]
      · rw [canonList_eq_map]
        exact length_flatMap_map (f := binders) (h := canon n D) args fun q member => ih q member D
  | lambda nm b ih => intro _; rfl
  | multiLambda k nms b ih => intro _; rfl
  | subst b r ihb ihr => intro _; rfl
  | collection ct elems rest ih =>
      intro D
      simp only [canon, canonList_eq_map, binders, bindersList_eq_flatMap]
      exact length_flatMap_map (f := binders) (h := canon n D) elems fun q member => ih q member D
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member D
      rcases List.mem_cons.mp member with rfl | later
      · exact head D
      · exact tail q later D

/-! ## Alpha-equivalence keeps hostedness, on tame processes -/

/-- **A tame process alpha-equivalent to a tame hosted part is hosted.** Their common canonical form has the
channel without variables and the continuation closed and free of binders; the canonical renaming keeps the
numbers of variable occurrences and of binders, and renames only bound variables, to names outside the process. -/
theorem hosted_of_alphaEq {c c' : Pattern} (tameC : tame c = true) (tameC' : tame c' = true) (hosted : Hosted c)
    (same : AlphaEq c c') : Hosted c' := by
  let n := canonicalName (pvars c ++ pvars c')
  have fresh₁ : AvoidsCanonical n (pvars c) := fun v occurs L i eq =>
    freshName_not_mem (pvars c ++ pvars c') (Nat.pair L i) (by
      rw [show freshName (pvars c ++ pvars c') (Nat.pair L i) = v from eq]
      exact List.mem_append_left _ occurs)
  have fresh₂ : AvoidsCanonical n (pvars c') := fun v occurs L i eq =>
    freshName_not_mem (pvars c ++ pvars c') (Nat.pair L i) (by
      rw [show freshName (pvars c ++ pvars c') (Nat.pair L i) = v from eq]
      exact List.mem_append_right _ occurs)
  have meet : canon n 0 c = canon n 0 c' := by
    rw [canon_eq_named n _ tameC fresh₁, canon_eq_named n _ tameC' fresh₂]
    exact congrArg (named n 0) same
  have fo' : firstOrder c' = true := firstOrder_of_calcTerm c' (tame_calcTerm c' tameC')
  rcases hosted.2 with ground | ⟨t, x, A, rfl, groundX, closed, noBinders⟩
  · rw [canon_of_binders_nil n c 0 (binders_of_ground ground)] at meet
    refine ⟨fo', .inl (List.eq_nil_of_length_eq_zero ?_)⟩
    rw [← length_pvars_canon n c' 0, ← meet, ground]
    rfl
  · obtain ⟨t', x', A', rfl⟩ := input_of_canon meet.symm
    rw [canon_hosted_input n 0 hosted, canon_pFor] at meet
    obtain ⟨patterns, channels, bodies⟩ := pFor_inj meet
    obtain ⟨-, freeT, -, -⟩ := tame_pFor.mp tameC
    obtain ⟨-, freeT', -, -⟩ := tame_pFor.mp tameC'
    rw [frame_of_guardFree t freeT, frame_of_guardFree t' freeT'] at patterns bodies
    have groundX' : pvars x' = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← length_pvars_canon n x' 0, ← channels, groundX]
      rfl
    have noBinders' : binders A' = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← length_binders_canon n A' 1]
      have counted := congrArg (fun p => (binders p).length) bodies
      simp only [binders_rename, List.length_map, noBinders] at counted
      exact counted.symm
    rw [canon_of_binders_nil n A' 1 noBinders'] at bodies
    refine ⟨fo', .inr ⟨t', x', A', rfl, groundX', fun v inA => ?_, noBinders'⟩⟩
    by_contra outside
    have image : levelRename n 0 (pvars t') v ∈ pvars (rename (levelRename n 0 (pvars t)) A) := by
      rw [bodies, pvars_rename]
      exact List.mem_map_of_mem inA
    rw [pvars_rename] at image
    obtain ⟨w, inA₀, sameName⟩ := List.mem_map.mp image
    have inT : w ∈ pvars t := closed w inA₀
    simp only [levelRename, inT, if_true, outside, if_false] at sameName
    exact fresh₂ v (by rw [pvars_pFor]; exact List.mem_append_right _ inA) 0 _ sameName

#print axioms tame_rename
#print axioms tame_canon
#print axioms tame_of_mem_parts_renameApart
#print axioms calcTerm_psubst
#print axioms guardFree_psubst
#print axioms tame_of_guardFree_calcTerm
#print axioms tame_psubst
#print axioms calcTerm_toCalculus
#print axioms toCalculus_of_calcTerm
#print axioms toCalculus_psubst
#print axioms groundPrincipal_values
#print axioms tame_applyDot
#print axioms bagComm_keeps_tame
#print axioms length_pvars_canon
#print axioms length_binders_canon
#print axioms hosted_of_alphaEq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
