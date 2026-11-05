import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReduction

/-!
# The manuscript's alpha-equivalence is the closed form, on tame processes

`alpha_alphaEq` shows that the manuscript's renaming rule, closed under
equivalence and under every constructor position except a guard's pattern,
preserves the closed form. This module proves the converse for *tame*
processes: calculus syntax in which every guard has a pattern, a channel and a
continuation, and every pattern is guard-free (`alpha_of_alphaEq`). On tame
processes the two relations coincide (`alpha_iff_alphaEq`).

The proof renames every bound variable to a canonical name chosen by the depth
of its guard and its position in the guard's frame (`canon`). The renaming is
a chain of instances of the manuscript's rule, applied from the innermost guard
outward (`alpha_canon`), and the canonical process is a function of the closed
form alone (`canon_eq_named`).

Tameness is needed: a process may contain a code, which the closed form
cannot tell apart from a bound occurrence, so two processes can have the same
closed form without being related by renaming (`alphaEq_not_alpha_with_code`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst psubst_congr psubst_comp pcomp)

/-! ## Tame processes -/

mutual
/-- Calculus syntax whose guards have exactly three arguments and a
guard-free calculus pattern. -/
def tame : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => true
  | .apply c args => if c = "MFor" then tameFor args else tameList args
  | .lambda _ _ => false
  | .multiLambda _ _ _ => false
  | .subst _ _ => false
  | .collection _ elems rest => rest.isNone && tameList elems
def tameList : List Pattern → Bool
  | [] => true
  | p :: ps => tame p && tameList ps
def tameFor : List Pattern → Bool
  | [t, x, k] => calcTerm t && guardFree t && tame x && tame k
  | _ => false
end

theorem tameList_iff (ps : List Pattern) : tameList ps = true ↔ ∀ p ∈ ps, tame p = true := by
  induction ps with
  | nil => simp [tameList]
  | cons p ps ih => simp [tameList, ih]

theorem tameFor_iff (args : List Pattern) :
    tameFor args = true ↔ ∃ t x k, args = [t, x, k] ∧ calcTerm t = true ∧ guardFree t = true ∧
      tame x = true ∧ tame k = true := by
  constructor
  · intro h
    match args, h with
    | [t, x, k], h =>
        simp only [tameFor, Bool.and_eq_true] at h
        exact ⟨t, x, k, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · rintro ⟨t, x, k, rfl, h1, h2, h3, h4⟩
    simp [tameFor, h1, h2, h3, h4]

/-- A tame guard. -/
theorem tame_pFor {t x k : Pattern} :
    tame (pFor t x k) = true ↔ calcTerm t = true ∧ guardFree t = true ∧ tame x = true ∧ tame k = true := by
  simp [pFor, tame, tameFor, and_assoc]

theorem tame_calcTerm (p : Pattern) (tameP : tame p = true) : calcTerm p = true := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true → calcTerm q = true) with
  | bvar n => simp [tame] at tameP
  | fvar x => rfl
  | apply c args ih =>
      simp only [calcTerm, calcList_iff]
      simp only [tame] at tameP
      split at tameP
      · obtain ⟨t, x, k, rfl, calcT, _, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        intro q member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact calcT
        · exact ih q (by simp) tameX
        · exact ih q (by simp) tameK
      · exact fun q member => ih q member ((tameList_iff args).mp tameP q member)
  | lambda nm body ih => simp [tame] at tameP
  | multiLambda n nms body ih => simp [tame] at tameP
  | subst body repl ihb ihr => simp [tame] at tameP
  | collection ct elems rest ih =>
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [calcTerm, Bool.and_eq_true, calcList_iff]
      exact ⟨tameP.1, fun q member => ih q member (tameP.2 q member)⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ
      · exact tail q later tameQ

/-! ## Renaming, structurally -/

theorem rename_fvar (g : String → String) (x : String) : rename g (.fvar x) = .fvar (g x) := rfl

theorem rename_apply (g : String → String) (c : String) (args : List Pattern) :
    rename g (.apply c args) = .apply c (args.map (rename g)) := by
  show Pattern.apply c (psubst.psubstList _ args) = _
  rw [psubstList_eq_map]
  rfl

theorem rename_collection (g : String → String) (ct : CollType) (elems : List Pattern)
    (rest : Option String) :
    rename g (.collection ct elems rest) = .collection ct (elems.map (rename g)) rest := by
  show Pattern.collection ct (psubst.psubstList _ elems) rest = _
  rw [psubstList_eq_map]
  rfl

theorem rename_pFor (g : String → String) (t x k : Pattern) :
    rename g (pFor t x k) = pFor (rename g t) (rename g x) (rename g k) := by
  simp [pFor, rename_apply]

theorem rename_rename (f g : String → String) (p : Pattern) :
    rename f (rename g p) = rename (fun v => f (g v)) p := by
  unfold rename
  rw [psubst_comp]
  apply psubst_congr
  intro x _
  simp [pcomp, psubst]

theorem rename_id (p : Pattern) : rename (fun v => v) p = p :=
  rename_of_fixed _ p fun _ _ => rfl

/-- Renaming renames the bound variables of inner guards. -/
theorem binders_rename (g : String → String) (p : Pattern) :
    binders (rename g p) = (binders p).map g := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      binders (rename g q) = (binders q).map g) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      rw [rename_apply, binders_apply, binders_apply]
      by_cases guard : c = "MFor"
      · simp only [guard, if_true]
        by_cases short : args.length < 3
        · rw [bindersFor_short _ (by simpa using short), bindersFor_short _ short, List.flatMap_map,
            List.map_flatMap]
          exact List.flatMap_congr fun q member => ih q member
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              simp only [List.map_cons]
              rw [bindersFor_cons3, bindersFor_cons3, pvars_rename, ih x (by simp), ih k (by simp),
                List.flatMap_map]
              simp only [List.map_append, List.map_flatMap]
              congr 1
              exact List.flatMap_congr fun q member => ih q (by simp [member])
      · simp only [guard, if_false, List.flatMap_map, List.map_flatMap]
        exact List.flatMap_congr fun q member => ih q member
  | lambda nm body ih => simpa [rename, psubst, binders] using ih
  | multiLambda n nms body ih => simpa [rename, psubst, binders] using ih
  | subst body repl ihb ihr =>
      simp only [rename, psubst, binders, List.map_append] at ihb ihr ⊢
      rw [ihb, ihr]
  | collection ct elems rest ih =>
      rw [rename_collection]
      simp only [binders, bindersList_eq_flatMap, List.flatMap_map, List.map_flatMap]
      exact List.flatMap_congr fun q member => ih q member
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem calcTerm_rename (g : String → String) (p : Pattern) : calcTerm (rename g p) = calcTerm p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm (rename g q) = calcTerm q) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      rw [rename_apply]
      simp only [calcTerm]
      have each : ∀ ps : List Pattern, (∀ q ∈ ps, calcTerm (rename g q) = calcTerm q) →
          calcList (ps.map (rename g)) = calcList ps := by
        intro ps hps
        induction ps with
        | nil => rfl
        | cons p ps ihp =>
            simp only [List.map_cons, calcList, hps p (List.mem_cons_self ..),
              ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
      exact each args ih
  | lambda nm body ih => rfl
  | multiLambda n nms body ih => rfl
  | subst body repl ihb ihr => rfl
  | collection ct elems rest ih =>
      rw [rename_collection]
      simp only [calcTerm]
      have each : ∀ ps : List Pattern, (∀ q ∈ ps, calcTerm (rename g q) = calcTerm q) →
          calcList (ps.map (rename g)) = calcList ps := by
        intro ps hps
        induction ps with
        | nil => rfl
        | cons p ps ihp =>
            simp only [List.map_cons, calcList, hps p (List.mem_cons_self ..),
              ihp fun q m => hps q (List.mem_cons_of_mem _ m)]
      rw [each elems ih]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-! ## Canonical names -/

/-- Rename a frame `l` at depth `D` to canonical names. -/
def levelRename (n : ℕ → ℕ → String) (D : ℕ) (l : List String) (v : String) : String :=
  if v ∈ l then n D (l.idxOf v) else v

mutual
/-- Rename every bound variable to the canonical name of its guard's depth
and its position in the guard's frame. Free variables stay. -/
def canon (n : ℕ → ℕ → String) (D : ℕ) : Pattern → Pattern
  | .bvar k => .bvar k
  | .fvar x => .fvar x
  | .apply c args => .apply c (if c = "MFor" then canonFor n D args else canonList n D args)
  | .lambda nm b => .lambda nm b
  | .multiLambda k nms b => .multiLambda k nms b
  | .subst b r => .subst b r
  | .collection ct elems rest => .collection ct (canonList n D elems) rest
def canonList (n : ℕ → ℕ → String) (D : ℕ) : List Pattern → List Pattern
  | [] => []
  | p :: ps => canon n D p :: canonList n D ps
def canonFor (n : ℕ → ℕ → String) (D : ℕ) : List Pattern → List Pattern
  | [] => []
  | [p] => [canon n D p]
  | [p, q] => [canon n D p, canon n D q]
  | t :: x :: k :: rest =>
      rename (levelRename n D (frame t)) t :: canon n D x ::
        rename (levelRename n D (frame t)) (canon n (D + 1) k) :: canonList n D rest
end

theorem canonList_eq_map (n : ℕ → ℕ → String) (D : ℕ) (ps : List Pattern) :
    canonList n D ps = ps.map (canon n D) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [canonList, ih]

theorem canon_pFor (n : ℕ → ℕ → String) (D : ℕ) (t x k : Pattern) :
    canon n D (pFor t x k) =
      pFor (rename (levelRename n D (frame t)) t) (canon n D x)
        (rename (levelRename n D (frame t)) (canon n (D + 1) k)) := by
  simp [pFor, canon, canonFor, canonList]

mutual
/-- Read a closed form back with canonical names: a code bound `r` guards
out, below `D` guards, names the guard at depth `D - 1 - r`. -/
def named (n : ℕ → ℕ → String) (D : ℕ) : Pattern → Pattern
  | .bvar c =>
      if (Nat.unpair c).1 < D then .fvar (n (D - 1 - (Nat.unpair c).1) (Nat.unpair c).2) else .bvar c
  | .fvar x => .fvar x
  | .apply c args => .apply c (if c = "MFor" then namedFor n D args else namedList n D args)
  | .lambda nm b => .lambda nm (named n D b)
  | .multiLambda k nms b => .multiLambda k nms (named n D b)
  | .subst b r => .subst (named n D b) (named n D r)
  | .collection ct elems rest => .collection ct (namedList n D elems) rest
def namedList (n : ℕ → ℕ → String) (D : ℕ) : List Pattern → List Pattern
  | [] => []
  | p :: ps => named n D p :: namedList n D ps
def namedFor (n : ℕ → ℕ → String) (D : ℕ) : List Pattern → List Pattern
  | [] => []
  | [p] => [named n D p]
  | [p, q] => [named n D p, named n D q]
  | t :: x :: k :: rest =>
      named n (D + 1) t :: named n D x :: named n (D + 1) k :: namedList n D rest
end

theorem namedList_eq_map (n : ℕ → ℕ → String) (D : ℕ) (ps : List Pattern) :
    namedList n D ps = ps.map (named n D) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [namedList, ih]

theorem named_pFor (n : ℕ → ℕ → String) (D : ℕ) (t x k : Pattern) :
    named n D (pFor t x k) = pFor (named n (D + 1) t) (named n D x) (named n (D + 1) k) := by
  simp [pFor, named, namedFor, namedList]

/-- The canonical name of a variable bound in an environment. -/
def envName (n : ℕ → ℕ → String) (env : List (List String)) (v : String) : String :=
  match lookupBound env v with
  | some found => n (env.length - 1 - found.1) found.2
  | none => v

theorem envName_cons_mem (n : ℕ → ℕ → String) {f : List String} {env : List (List String)}
    {v : String} (member : v ∈ f) : envName n (f :: env) v = n env.length (f.idxOf v) := by
  simp [envName, lookupBound, member]

theorem envName_cons_not_mem (n : ℕ → ℕ → String) {f : List String} {env : List (List String)}
    {v : String} (outside : v ∉ f) : envName n (f :: env) v = envName n env v := by
  unfold envName
  simp only [lookupBound, outside, if_false]
  cases lookupBound env v with
  | none => rfl
  | some found =>
      simp only [Option.map_some, List.length_cons]
      congr 1
      omega

/-- A closed guard-free pattern, read back at depth `D + 1`, is its frame
renamed to the canonical names of depth `D`. -/
theorem named_closeIn_pattern (n : ℕ → ℕ → String) (D : ℕ) (l : List String) (t : Pattern)
    (calcT : calcTerm t = true) (free : guardFree t = true) (inside : ∀ v ∈ pvars t, v ∈ l) :
    named n (D + 1) (closeIn [l] t) = rename (fun v => n D (l.idxOf v)) t := by
  induction t using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      guardFree q = true → (∀ v ∈ pvars q, v ∈ l) →
      named n (D + 1) (closeIn [l] q) = rename (fun v => n D (l.idxOf v)) q) with
  | bvar k => simp [calcTerm] at calcT
  | fvar v =>
      have member := inside v (by simp [pvars])
      simp [closeIn, lookupBound_single_mem member, boundCode, named, rename_fvar]
  | apply c args ih =>
      have notGuard : c ≠ "MFor" := by
        intro same; subst same; simp [guardFree] at free
      rw [closeIn_apply, if_neg notGuard, rename_apply]
      simp only [named, if_neg notGuard, namedList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [calcTerm, calcList_iff] at calcT
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      exact ih q member (calcT q member) (free.2 q member) fun v occurs =>
        inside v (mem_pvars_apply_of member occurs)
  | lambda nm body ih => simp [calcTerm] at calcT
  | multiLambda k nms body ih => simp [calcTerm] at calcT
  | subst body repl ihb ihr => simp [calcTerm] at calcT
  | collection ct elems rest ih =>
      rw [rename_collection]
      simp only [closeIn, closeList_eq_map, named, namedList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      simp only [calcTerm, Bool.and_eq_true, calcList_iff] at calcT
      simp only [guardFree, guardFreeList_iff] at free
      exact ih q member (calcT.2 q member) (free q member) fun v occurs =>
        inside v (mem_pvars_collection_of member occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ freeQ insideQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ freeQ insideQ
      · exact tail q later calcQ freeQ insideQ

/-- No canonical name is among `names`. -/
def AvoidsCanonical (n : ℕ → ℕ → String) (names : List String) : Prop :=
  ∀ v ∈ names, ∀ L i, n L i ≠ v

theorem lookupBound_canonical {n : ℕ → ℕ → String} {env : List (List String)}
    (clean : ∀ f ∈ env, AvoidsCanonical n f) (L i : ℕ) : lookupBound env (n L i) = none :=
  lookupBound_none_of_not_mem fun f member inside => clean f member _ inside L i rfl

/-- **Canonical renaming reads the closed form.** Below an environment of
frames free of canonical names, renaming the bound variables canonically and
then the environment's variables gives the closed form read back. -/
theorem named_closeIn (n : ℕ → ℕ → String) (p : Pattern) (tameP : tame p = true) :
    ∀ env : List (List String), (∀ f ∈ env, AvoidsCanonical n f) → AvoidsCanonical n (pvars p) →
      rename (envName n env) (canon n env.length p) = named n env.length (closeIn env p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true →
      ∀ env : List (List String), (∀ f ∈ env, AvoidsCanonical n f) → AvoidsCanonical n (pvars q) →
        rename (envName n env) (canon n env.length q) = named n env.length (closeIn env q)) with
  | bvar k => simp [tame] at tameP
  | fvar v =>
      intro env _ _
      cases found : lookupBound env v with
      | none => simp [canon, rename_fvar, envName, found, closeIn, named]
      | some position =>
          have small := lookupBound_lt found
          simp [canon, rename_fvar, envName, found, closeIn, boundCode, named, small]
  | apply c args ih =>
      intro env clean fresh
      by_cases guard : c = "MFor"
      · subst guard
        simp only [tame, if_true] at tameP
        obtain ⟨t, x, k, rfl, calcT, freeT, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        have freshT : AvoidsCanonical n (pvars t) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        have freshX : AvoidsCanonical n (pvars x) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        have freshK : AvoidsCanonical n (pvars k) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        have frameClean : AvoidsCanonical n (frame t) := fun v member =>
          freshT v (frame_subset t v member)
        change rename (envName n env) (canon n env.length (pFor t x k)) =
          named n env.length (closeIn env (pFor t x k))
        rw [canon_pFor, rename_pFor, closeIn_pFor, named_pFor]
        congr 1
        · -- the pattern
          rw [rename_rename, named_closeIn_pattern n env.length (frame t) t calcT freeT
            (by rw [frame_of_guardFree t freeT]; exact fun v h => h)]
          apply rename_congr
          intro v occurs
          have member : v ∈ frame t := by rw [frame_of_guardFree t freeT]; exact occurs
          simp [levelRename, member, envName, lookupBound_canonical clean]
        · exact ih x (by simp) tameX env clean freshX
        · -- the continuation
          rw [rename_rename]
          have step := ih k (by simp) tameK (frame t :: env)
            (fun f member => by
              rcases List.mem_cons.mp member with rfl | later
              · exact frameClean
              · exact clean f later) freshK
          simp only [List.length_cons] at step
          rw [← step]
          congr 1
          funext v
          by_cases member : v ∈ frame t
          · rw [envName_cons_mem n member]
            simp [levelRename, member, envName, lookupBound_canonical clean]
          · rw [envName_cons_not_mem n member]
            simp [levelRename, member]
      · rw [closeIn_apply, if_neg guard]
        simp only [canon, if_neg guard, canonList_eq_map, named, namedList_eq_map, rename_apply,
          List.map_map]
        simp only [tame, if_neg guard, tameList_iff] at tameP
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (tameP q member) env clean fun v occurs =>
          fresh v (mem_pvars_apply_of member occurs)
  | lambda nm body ih => simp [tame] at tameP
  | multiLambda k nms body ih => simp [tame] at tameP
  | subst body repl ihb ihr => simp [tame] at tameP
  | collection ct elems rest ih =>
      intro env clean fresh
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [canon, canonList_eq_map, rename_collection, closeIn, closeList_eq_map, named,
        namedList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member (tameP.2 q member) env clean fun v occurs =>
        fresh v (mem_pvars_collection_of member occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ env clean freshQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ env clean freshQ
      · exact tail q later tameQ env clean freshQ

/-- **The canonical process is a function of the closed form.** -/
theorem canon_eq_named (n : ℕ → ℕ → String) (p : Pattern) (tameP : tame p = true)
    (fresh : AvoidsCanonical n (pvars p)) : canon n 0 p = named n 0 (close p) := by
  have := named_closeIn n p tameP [] (by simp) fresh
  simp only [List.length_nil] at this
  show canon n 0 p = named n 0 (closeIn [] p)
  rw [← this]
  exact (rename_of_fixed _ _ fun v _ => by simp [envName, lookupBound]).symm

/-! ## Canonical renaming is a chain of alpha steps -/

theorem pvars_canon (n : ℕ → ℕ → String) (p : Pattern) (tameP : tame p = true) :
    ∀ D, ∀ w ∈ pvars (canon n D p), w ∈ pvars p ∨ ∃ L i, D ≤ L ∧ w = n L i := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true →
      ∀ D, ∀ w ∈ pvars (canon n D q), w ∈ pvars q ∨ ∃ L i, D ≤ L ∧ w = n L i) with
  | bvar k => simp [tame] at tameP
  | fvar v => intro D w occurs; exact .inl (by simpa [canon] using occurs)
  | apply c args ih =>
      intro D w occurs
      by_cases guard : c = "MFor"
      · subst guard
        simp only [tame, if_true] at tameP
        obtain ⟨t, x, k, rfl, _, freeT, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        change w ∈ pvars (canon n D (pFor t x k)) at occurs
        rw [canon_pFor, pvars_pFor, List.mem_append, List.mem_append, pvars_rename, pvars_rename] at occurs
        rcases occurs with (inT | inX) | inK
        · obtain ⟨v, vIn, rfl⟩ := List.mem_map.mp inT
          have member : v ∈ frame t := by rw [frame_of_guardFree t freeT]; exact vIn
          exact .inr ⟨D, (frame t).idxOf v, le_rfl, by simp [levelRename, member]⟩
        · rcases ih x (by simp) tameX D w inX with own | named
          · exact .inl (mem_pvars_apply_of (by simp) own)
          · exact .inr named
        · obtain ⟨v, vIn, rfl⟩ := List.mem_map.mp inK
          by_cases member : v ∈ frame t
          · exact .inr ⟨D, (frame t).idxOf v, le_rfl, by simp [levelRename, member]⟩
          · simp only [levelRename, member, if_false]
            rcases ih k (by simp) tameK (D + 1) v vIn with own | ⟨L, i, deeper, rfl⟩
            · exact .inl (mem_pvars_apply_of (by simp) own)
            · exact .inr ⟨L, i, by omega, rfl⟩
      · simp only [tame, if_neg guard, tameList_iff] at tameP
        simp only [canon, if_neg guard, canonList_eq_map, pvars_apply, pvarsList_eq_flatMap,
          List.flatMap_map, List.mem_flatMap] at occurs
        obtain ⟨q, member, inQ⟩ := occurs
        rcases ih q member (tameP q member) D w inQ with own | named
        · exact .inl (mem_pvars_apply_of member own)
        · exact .inr named
  | lambda nm body ih => simp [tame] at tameP
  | multiLambda k nms body ih => simp [tame] at tameP
  | subst body repl ihb ihr => simp [tame] at tameP
  | collection ct elems rest ih =>
      intro D w occurs
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [canon, canonList_eq_map, pvars, pvarsList_eq_flatMap, List.flatMap_map,
        List.mem_flatMap] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      rcases ih q member (tameP.2 q member) D w inQ with own | named
      · exact .inl (mem_pvars_collection_of member own)
      · exact .inr named
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ D w occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ D w occurs
      · exact tail q later tameQ D w occurs

theorem binders_canon (n : ℕ → ℕ → String) (p : Pattern) (tameP : tame p = true) :
    ∀ D, ∀ w ∈ binders (canon n D p), ∃ L i, D ≤ L ∧ w = n L i := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true →
      ∀ D, ∀ w ∈ binders (canon n D q), ∃ L i, D ≤ L ∧ w = n L i) with
  | bvar k => simp [tame] at tameP
  | fvar v => intro D w occurs; simp [canon, binders] at occurs
  | apply c args ih =>
      intro D w occurs
      by_cases guard : c = "MFor"
      · subst guard
        simp only [tame, if_true] at tameP
        obtain ⟨t, x, k, rfl, _, freeT, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        change w ∈ binders (canon n D (pFor t x k)) at occurs
        rw [canon_pFor] at occurs
        simp only [pFor, binders_apply, if_true] at occurs
        rw [bindersFor_cons3] at occurs
        simp only [List.flatMap_nil, List.append_nil, List.mem_append] at occurs
        rcases occurs with (inT | inX) | inK
        · rw [pvars_rename] at inT
          obtain ⟨v, vIn, rfl⟩ := List.mem_map.mp inT
          have member : v ∈ frame t := by rw [frame_of_guardFree t freeT]; exact vIn
          exact ⟨D, (frame t).idxOf v, le_rfl, by simp [levelRename, member]⟩
        · exact ih x (by simp) tameX D w inX
        · rw [binders_rename] at inK
          obtain ⟨v, vIn, rfl⟩ := List.mem_map.mp inK
          by_cases member : v ∈ frame t
          · exact ⟨D, (frame t).idxOf v, le_rfl, by simp [levelRename, member]⟩
          · simp only [levelRename, member, if_false]
            obtain ⟨L, i, deeper, rfl⟩ := ih k (by simp) tameK (D + 1) v vIn
            exact ⟨L, i, by omega, rfl⟩
      · simp only [tame, if_neg guard, tameList_iff] at tameP
        simp only [canon, if_neg guard, canonList_eq_map, binders_apply, List.flatMap_map,
          List.mem_flatMap] at occurs
        obtain ⟨q, member, inQ⟩ := occurs
        exact ih q member (tameP q member) D w inQ
  | lambda nm body ih => simp [tame] at tameP
  | multiLambda k nms body ih => simp [tame] at tameP
  | subst body repl ihb ihr => simp [tame] at tameP
  | collection ct elems rest ih =>
      intro D w occurs
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [canon, canonList_eq_map, binders, bindersList_eq_flatMap, List.flatMap_map,
        List.mem_flatMap] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      exact ih q member (tameP.2 q member) D w inQ
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ D w occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ D w occurs
      · exact tail q later tameQ D w occurs

/-- Rename the variables `vs` of a frame, one at a time, by instances of the
manuscript's rule. -/
theorem alpha_rename_frame (n : ℕ → ℕ → String)
    (inj : ∀ L i L' i', n L i = n L' i' → L = L' ∧ i = i') (D : ℕ) (t X K : Pattern)
    (free : guardFree t = true) (freshT : AvoidsCanonical n (pvars t))
    (bodyNames : ∀ w ∈ pvars K, (∀ L i, n L i ≠ w) ∨ ∃ L i, D < L ∧ w = n L i)
    (bodyBinders : ∀ w ∈ binders K, ∃ L i, D < L ∧ w = n L i) :
    ∀ vs : List String, vs.Nodup → (∀ v ∈ vs, v ∈ frame t) →
      Alpha (pFor t X K)
        (pFor (rename (fun v => if v ∈ vs then levelRename n D (frame t) v else v) t) X
          (rename (fun v => if v ∈ vs then levelRename n D (frame t) v else v) K)) := by
  have frameIs : frame t = pvars t := frame_of_guardFree t free
  intro vs
  induction vs with
  | nil =>
      intro _ _
      simp only [List.not_mem_nil, if_false]
      rw [rename_id, rename_id]
      exact .refl _
  | cons y vs ih =>
      intro nodup inside
      have yOut : y ∉ vs := (List.nodup_cons.mp nodup).1
      have yFrame : y ∈ frame t := inside y (List.mem_cons_self ..)
      have yT : y ∈ pvars t := frame_subset t y yFrame
      have yClean : ∀ L i, n L i ≠ y := freshT y yT
      have before := ih (List.nodup_cons.mp nodup).2 fun v member => inside v (List.mem_cons_of_mem _ member)
      let h : String → String := fun v => if v ∈ vs then levelRename n D (frame t) v else v
      let z := n D ((frame t).idxOf y)
      have hy : h y = y := by simp [h, yOut]
      -- a renamed variable is canonical at depth `D`
      have renamedCanon : ∀ w, w ∈ vs → h w = n D ((frame t).idxOf w) := by
        intro w member
        have wFrame : w ∈ frame t := inside w (List.mem_cons_of_mem _ member)
        simp [h, member, levelRename, wFrame]
      have notZ : ∀ w, w ∈ frame t → h w = z → w = y := by
        intro w wFrame same
        by_cases member : w ∈ vs
        · rw [renamedCanon w member] at same
          have := (inj _ _ _ _ same).2
          exact (List.idxOf_inj wFrame).mp this
        · simp only [h, member, if_false] at same
          exact absurd same.symm (freshT w (frame_subset t w wFrame) D _)
      have rule := AlphaRule.rename (rename h t) X (rename h K) y z
        (by rw [pvars_rename]; exact List.mem_map.mpr ⟨y, yT, hy⟩)
        (by
          rw [pvars_rename]
          intro inside'
          obtain ⟨w, wIn, same⟩ := List.mem_map.mp inside'
          have wFrame : w ∈ frame t := by rw [frameIs]; exact wIn
          exact yOut (notZ w wFrame same ▸ (by
            by_cases member : w ∈ vs
            · exact member
            · exfalso
              simp only [h, member, if_false] at same
              exact freshT w wIn D _ same.symm)))
        (by
          rw [pvars_rename]
          intro inside'
          obtain ⟨w, wIn, same⟩ := List.mem_map.mp inside'
          by_cases member : w ∈ vs
          · have wFrame : w ∈ frame t := inside w (List.mem_cons_of_mem _ member)
            exact yOut (notZ w wFrame same ▸ member)
          · simp only [h, member, if_false] at same
            rcases bodyNames w wIn with clean | ⟨L, i, deeper, rfl⟩
            · exact clean D _ same.symm
            · have := (inj _ _ _ _ same).1
              omega)
        (by
          rw [binders_rename]
          intro inside'
          obtain ⟨w, wIn, same⟩ := List.mem_map.mp inside'
          obtain ⟨L, i, _, rfl⟩ := bodyBinders w wIn
          have notVs : n L i ∉ vs := fun member =>
            freshT _ (frame_subset t _ (inside _ (List.mem_cons_of_mem _ member))) L i rfl
          simp only [h, notVs, if_false] at same
          exact yClean L i same)
        (by rw [guardFree_rename]; exact free)
      have swapped : ∀ p : Pattern, rename (swapTo y z) (rename h p) =
          rename (fun v => if v ∈ y :: vs then levelRename n D (frame t) v else v) p := by
        intro p
        rw [rename_rename]
        congr 1
        funext v
        by_cases member : v ∈ vs
        · have vy : v ≠ y := fun same => yOut (same ▸ member)
          rw [renamedCanon v member]
          have different : n D ((frame t).idxOf v) ≠ y := yClean D _
          have vFrame : v ∈ frame t := inside v (List.mem_cons_of_mem _ member)
          simp [swapTo, different, member, levelRename, vFrame]
        · by_cases same : v = y
          · subst same
            simp [h, member, swapTo, z, levelRename, yFrame]
          · simp [h, member, swapTo, same]
      rw [swapped t, swapped K] at rule
      exact .trans before (.rule rule)

theorem alpha_apply_map (c : String) (notGuard : c ≠ "MFor") (f : Pattern → Pattern) :
    ∀ (before args : List Pattern), (∀ a ∈ args, Alpha a (f a)) →
      Alpha (.apply c (before ++ args)) (.apply c (before ++ args.map f)) := by
  intro before args
  induction args generalizing before with
  | nil => intro _; simpa using Alpha.refl (.apply c before)
  | cons a args ih =>
      intro each
      have first := Alpha.apply c before args (fun h => notGuard h.1) (each a (List.mem_cons_self ..))
      have rest := ih (before ++ [f a]) fun b member => each b (List.mem_cons_of_mem _ member)
      simp only [List.append_assoc, List.singleton_append] at rest
      exact .trans first (by simpa using rest)

theorem alpha_collection_map (ct : CollType) (rest : Option String) (f : Pattern → Pattern) :
    ∀ (before elems : List Pattern), (∀ a ∈ elems, Alpha a (f a)) →
      Alpha (.collection ct (before ++ elems) rest) (.collection ct (before ++ elems.map f) rest) := by
  intro before elems
  induction elems generalizing before with
  | nil => intro _; simpa using Alpha.refl (.collection ct before rest)
  | cons a elems ih =>
      intro each
      have first := Alpha.collection ct before elems rest (each a (List.mem_cons_self ..))
      have later := ih (before ++ [f a]) fun b member => each b (List.mem_cons_of_mem _ member)
      simp only [List.append_assoc, List.singleton_append] at later
      exact .trans first (by simpa using later)

/-- **Canonical renaming is alpha.** -/
theorem alpha_canon (n : ℕ → ℕ → String) (inj : ∀ L i L' i', n L i = n L' i' → L = L' ∧ i = i')
    (p : Pattern) (tameP : tame p = true) :
    ∀ D, AvoidsCanonical n (pvars p) → Alpha p (canon n D p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true →
      ∀ D, AvoidsCanonical n (pvars q) → Alpha q (canon n D q)) with
  | bvar k => simp [tame] at tameP
  | fvar v => intro D _; exact .refl _
  | apply c args ih =>
      intro D fresh
      by_cases guard : c = "MFor"
      · subst guard
        simp only [tame, if_true] at tameP
        obtain ⟨t, x, k, rfl, calcT, freeT, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        have freshT : AvoidsCanonical n (pvars t) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        have freshX : AvoidsCanonical n (pvars x) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        have freshK : AvoidsCanonical n (pvars k) := fun v occurs =>
          fresh v (mem_pvars_apply_of (by simp) occurs)
        change Alpha (pFor t x k) (canon n D (pFor t x k))
        rw [canon_pFor]
        have channel : Alpha (pFor t x k) (pFor t (canon n D x) k) :=
          Alpha.apply "MFor" [t] [k] (by simp) (ih x (by simp) tameX D freshX)
        have body : Alpha (pFor t (canon n D x) k) (pFor t (canon n D x) (canon n (D + 1) k)) :=
          Alpha.apply "MFor" [t, canon n D x] [] (by simp) (ih k (by simp) tameK (D + 1) freshK)
        have frameNodup := List.nodup_dedup (frame t)
        have rename := alpha_rename_frame n inj D t (canon n D x) (canon n (D + 1) k) freeT freshT
          (fun w occurs => by
            rcases pvars_canon n k tameK (D + 1) w occurs with own | ⟨L, i, deeper, rfl⟩
            · exact .inl fun L i same => freshK w own L i same
            · exact .inr ⟨L, i, by omega, rfl⟩)
          (fun w occurs => by
            obtain ⟨L, i, deeper, rfl⟩ := binders_canon n k tameK (D + 1) w occurs
            exact ⟨L, i, by omega, rfl⟩)
          (frame t).dedup frameNodup (fun v member => List.mem_dedup.mp member)
        have whole : (fun v => if v ∈ (frame t).dedup then levelRename n D (frame t) v else v) =
            levelRename n D (frame t) := by
          funext v
          by_cases member : v ∈ frame t
          · simp [List.mem_dedup, member]
          · simp [List.mem_dedup, member, levelRename]
        rw [whole] at rename
        exact .trans channel (.trans body rename)
      · simp only [tame, if_neg guard, tameList_iff] at tameP
        simp only [canon, if_neg guard, canonList_eq_map]
        have := alpha_apply_map c guard (canon n D) [] args fun a member =>
          ih a member (tameP a member) D fun v occurs => fresh v (mem_pvars_apply_of member occurs)
        simpa using this
  | lambda nm body ih => simp [tame] at tameP
  | multiLambda k nms body ih => simp [tame] at tameP
  | subst body repl ihb ihr => simp [tame] at tameP
  | collection ct elems rest ih =>
      intro D fresh
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [canon, canonList_eq_map]
      have := alpha_collection_map ct rest (canon n D) [] elems fun a member =>
        ih a member (tameP.2 a member) D fun v occurs => fresh v (mem_pvars_collection_of member occurs)
      simpa using this
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ D freshQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ D freshQ
      · exact tail q later tameQ D freshQ

/-! ## The converse inclusion -/

/-- Canonical names fresh for `avoid`: one per depth and frame position. -/
def canonicalName (avoid : List String) (L i : ℕ) : String := freshName avoid (Nat.pair L i)

theorem canonicalName_injective (avoid : List String) :
    ∀ L i L' i', canonicalName avoid L i = canonicalName avoid L' i' → L = L' ∧ i = i' := by
  intro L i L' i' same
  exact Nat.pair_eq_pair.mp (freshName_injective avoid same)

/-- **Converse alpha inclusion.** Tame processes with equal closed forms are
related by the manuscript's renaming rule, closed under equivalence and
contexts. -/
theorem alpha_of_alphaEq {p q : Pattern} (tameP : tame p = true) (tameQ : tame q = true)
    (same : AlphaEq p q) : Alpha p q := by
  let n := canonicalName (pvars p ++ pvars q)
  have inj := canonicalName_injective (pvars p ++ pvars q)
  have freshP : AvoidsCanonical n (pvars p) := fun v occurs L i eq =>
    freshName_not_mem (pvars p ++ pvars q) (Nat.pair L i) (by
      rw [show freshName (pvars p ++ pvars q) (Nat.pair L i) = v from eq]
      exact List.mem_append_left _ occurs)
  have freshQ : AvoidsCanonical n (pvars q) := fun v occurs L i eq =>
    freshName_not_mem (pvars p ++ pvars q) (Nat.pair L i) (by
      rw [show freshName (pvars p ++ pvars q) (Nat.pair L i) = v from eq]
      exact List.mem_append_right _ occurs)
  have toP := alpha_canon n inj p tameP 0 freshP
  have toQ := alpha_canon n inj q tameQ 0 freshQ
  have meet : canon n 0 p = canon n 0 q := by
    rw [canon_eq_named n p tameP freshP, canon_eq_named n q tameQ freshQ]
    exact congrArg (named n 0) same
  rw [meet] at toP
  exact .trans toP (.symm toQ)

/-- **On tame processes, the manuscript's alpha-equivalence is equality of
closed forms.** -/
theorem alpha_iff_alphaEq {p q : Pattern} (tameP : tame p = true) (tameQ : tame q = true) :
    Alpha p q ↔ AlphaEq p q :=
  ⟨alpha_alphaEq, alpha_of_alphaEq tameP tameQ⟩

/-! ## Tameness is needed -/

theorem calcList_append (before after : List Pattern) :
    calcList (before ++ after) = (calcList before && calcList after) := by
  induction before with
  | nil => simp [calcList]
  | cons p ps ih => simp [calcList, ih, Bool.and_assoc]

/-- The renaming rule and its closure keep calculus syntax calculus syntax. -/
theorem alpha_calcTerm {p q : Pattern} (alpha : Alpha p q) : calcTerm p = calcTerm q := by
  induction alpha with
  | rule rule =>
      cases rule with
      | rename t x k y z _ _ _ _ _ =>
          simp only [pFor, calcTerm, calcList, calcTerm_rename]
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | apply c before after _ _ ih =>
      simp only [calcTerm, calcList_append, calcList, ih]
  | collection ct before after rest _ ih =>
      simp only [calcTerm, calcList_append, calcList, ih]

/-- A guard whose continuation is a code at the guard's own frame. -/
def codeContinuation : Pattern := pFor (.fvar "x") demoChan (.bvar (Nat.pair 0 0))

/-- The same guard with a bound occurrence in place of the code. -/
def boundContinuation : Pattern := pFor (.fvar "x") demoChan (.fvar "x")

/-- **Separating control.** The closed form cannot tell a code from a bound
occurrence, so outside tame processes equal closed forms do not imply the
manuscript's alpha-equivalence. -/
theorem alphaEq_not_alpha_with_code :
    AlphaEq boundContinuation codeContinuation ∧ ¬ Alpha boundContinuation codeContinuation ∧
      tame boundContinuation = true ∧ tame codeContinuation = false := by
  refine ⟨by decide +kernel, fun alpha => ?_, by decide +kernel, by decide +kernel⟩
  have := alpha_calcTerm alpha
  revert this
  decide +kernel

/-- Positive control: the canary and its renamed variant are tame, so their
alpha-equivalence follows from their closed forms alone. -/
theorem canary_alpha_of_closed_forms :
    Alpha demoCommSource (par (pFor (.fvar "a1") demoChan (.fvar "a1")) (pFor pZero demoChan (.fvar "a"))) :=
  alpha_of_alphaEq (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
