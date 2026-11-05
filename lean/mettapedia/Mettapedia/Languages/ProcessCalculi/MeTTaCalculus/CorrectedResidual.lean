import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedAlpha

/-!
# Completeness with residual variables, up to renaming

On the closing fragment the unifier grounds every pattern variable a
continuation reads, and the executable step reproduces each relational
reduct up to alpha (`cstep_complete`). Outside it a read variable may stay
unbound: it is a *residual* name.

With the manuscript's dot an unbound variable is not quoted, and which one
stays unbound depends on how a most general unifier is oriented: for
`for(X <- @0)X | for(Y <- @0)Y` one orientation reads `@Y | Y`, the other
`X | @X`. No renaming relates either reading to the other's
(`manuscript_dot_not_up_to_renaming`).

With the *uniform dot*, the dot of a principal binding list that names every
pattern variable (`uniform`), every pattern variable is quoted, and the
reduct is determined up to renaming of residual names:

* `principal_renaming`: two principal unifiers, of a pair of patterns and of
  its renaming apart, agree up to a renaming of their residual variables that
  is injective on them;
* `cstep_complete_residual`: every relational step of the uniform dot on
  guard-free calculus patterns is matched by an executable reduct `Q'` and a
  renaming `ρ` that fixes every free name of the source, is injective on the
  fresh names of `Q'`, and makes `ρ Q'` alpha-equivalent to the relational
  reduct.

The renaming need not be injective on all names of `Q'`: the relational
rule may pick a residual name that also occurs free in the surrounding
process, which the executable, whose fresh names avoid the whole process,
never does (`residual_meets_context`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst psubst_congr psubst_comp pcomp firstOrder applyDot_eq lookup_eq_none_of_keys)

/-! ## Substitution facts -/

theorem mem_pvars_psubst (s : PSubst) (T : Pattern) (x : String) :
    x ∈ pvars (psubst s T) ↔ ∃ w ∈ pvars T, x ∈ pvars ((s w).getD (.fvar w)) := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      (x ∈ pvars (psubst s q) ↔ ∃ w ∈ pvars q, x ∈ pvars ((s w).getD (.fvar w)))) with
  | bvar n => simp [psubst, pvars]
  | fvar y => simp [psubst, pvars]
  | apply c args ih =>
      simp only [psubst, pvars, psubstList_eq_map, pvarsList_eq_flatMap, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨r, ⟨q, member, rfl⟩, inR⟩
        obtain ⟨w, wIn, xIn⟩ := (ih q member).mp inR
        exact ⟨w, ⟨q, member, wIn⟩, xIn⟩
      · rintro ⟨w, ⟨q, member, wIn⟩, xIn⟩
        exact ⟨_, ⟨q, member, rfl⟩, (ih q member).mpr ⟨w, wIn, xIn⟩⟩
  | lambda nm body ih => simpa [psubst, pvars] using ih
  | multiLambda n nms body ih => simpa [psubst, pvars] using ih
  | subst body repl ihb ihr =>
      simp only [psubst, pvars, List.mem_append, ihb, ihr]
      constructor
      · rintro (⟨w, wIn, xIn⟩ | ⟨w, wIn, xIn⟩)
        · exact ⟨w, .inl wIn, xIn⟩
        · exact ⟨w, .inr wIn, xIn⟩
      · rintro ⟨w, (wIn | wIn), xIn⟩
        · exact .inl ⟨w, wIn, xIn⟩
        · exact .inr ⟨w, wIn, xIn⟩
  | collection ct elems rest ih =>
      simp only [psubst, pvars, psubstList_eq_map, pvarsList_eq_flatMap, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨r, ⟨q, member, rfl⟩, inR⟩
        obtain ⟨w, wIn, xIn⟩ := (ih q member).mp inR
        exact ⟨w, ⟨q, member, wIn⟩, xIn⟩
      · rintro ⟨w, ⟨q, member, wIn⟩, xIn⟩
        exact ⟨_, ⟨q, member, rfl⟩, (ih q member).mpr ⟨w, wIn, xIn⟩⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem map_eq_self {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ a ∈ l, f a = a
  | [], _, _, member => by cases member
  | b :: l, same, a, member => by
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | later
      · exact same.1
      · exact map_eq_self same.2 a later

/-- A substitution that fixes a pattern fixes each of its variables. -/
theorem psubst_eq_self_vars {s : PSubst} {T : Pattern} (fixes : psubst s T = T) :
    ∀ w ∈ pvars T, (s w).getD (.fvar w) = .fvar w := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, psubst s q = q →
      ∀ w ∈ pvars q, (s w).getD (.fvar w) = .fvar w) with
  | bvar n => intro w occurs; simp [pvars] at occurs
  | fvar y =>
      intro w occurs
      simp only [pvars, List.mem_singleton] at occurs
      subst occurs
      exact fixes
  | apply c args ih =>
      intro w occurs
      simp only [psubst, psubstList_eq_map, Pattern.apply.injEq, true_and] at fixes
      rw [pvars_apply, pvarsList_eq_flatMap] at occurs
      obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp occurs
      exact ih q member (map_eq_self fixes q member) w inQ
  | lambda nm body ih =>
      intro w occurs
      simp only [psubst, Pattern.lambda.injEq, true_and] at fixes
      exact ih fixes w (by simpa [pvars] using occurs)
  | multiLambda n nms body ih =>
      intro w occurs
      simp only [psubst, Pattern.multiLambda.injEq, true_and] at fixes
      exact ih fixes w (by simpa [pvars] using occurs)
  | subst body repl ihb ihr =>
      intro w occurs
      simp only [psubst, Pattern.subst.injEq] at fixes
      simp only [pvars, List.mem_append] at occurs
      rcases occurs with h | h
      · exact ihb fixes.1 w h
      · exact ihr fixes.2 w h
  | collection ct elems rest ih =>
      intro w occurs
      simp only [psubst, psubstList_eq_map, Pattern.collection.injEq, true_and, and_true] at fixes
      simp only [pvars, pvarsList_eq_flatMap, List.mem_flatMap] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      exact ih q member (map_eq_self fixes q member) w inQ
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member fixesQ w occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head fixesQ w occurs
      · exact tail q later fixesQ w occurs

/-- A substitution instance that is a variable is an instance of a variable. -/
theorem psubst_eq_fvar {s : PSubst} {T : Pattern} {w : String} (eq : psubst s T = .fvar w) :
    ∃ n, T = .fvar n ∧ (s n).getD (.fvar n) = .fvar w := by
  cases T with
  | fvar n => exact ⟨n, rfl, eq⟩
  | bvar n => simp [psubst] at eq
  | apply c args => simp [psubst] at eq
  | lambda nm body => simp [psubst] at eq
  | multiLambda n nms body => simp [psubst] at eq
  | subst body repl => simp [psubst] at eq
  | collection ct elems rest => simp [psubst] at eq

theorem pcomp_getD (outer inner : PSubst) (w : String) :
    ((pcomp outer inner) w).getD (.fvar w) = psubst outer ((inner w).getD (.fvar w)) := by
  unfold pcomp
  cases inner w <;> rfl

theorem mem_of_lookup_eq_some {bs : Bindings} {x : String} {w : Pattern} (found : bs.lookup x = some w) :
    (x, w) ∈ bs := by
  unfold Bindings.lookup at found
  cases findX : bs.find? (fun entry => entry.1 == x) with
  | none => rw [findX] at found; cases found
  | some entry =>
      rw [findX] at found
      simp only [Option.map_some, Option.some.injEq] at found
      have inside := List.mem_of_find?_eq_some findX
      have key := List.find?_some findX
      simp only [beq_iff_eq] at key
      obtain ⟨k, value⟩ := entry
      simp only at key found
      subst key found
      exact inside

/-- The variables bound by inner guards occur in the process. -/
theorem binders_subset_pvars (A : Pattern) : ∀ w ∈ binders A, w ∈ pvars A := by
  induction A using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ w ∈ binders q, w ∈ pvars q) with
  | bvar n => intro w h; simp [binders] at h
  | fvar x => intro w h; simp [binders] at h
  | apply c args ih =>
      intro w h
      rw [binders_apply] at h
      split at h
      · by_cases short : args.length < 3
        · rw [bindersFor_short _ short] at h
          obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp h
          exact mem_pvars_apply_of member (ih q member w inQ)
        · match args, short with
          | [_], s => simp at s
          | [_, _], s => simp at s
          | t :: x :: k :: rest, _ =>
              rw [bindersFor_cons3] at h
              simp only [List.mem_append] at h
              rcases h with ((inT | inX) | inK) | inRest
              · exact mem_pvars_apply_of (by simp) inT
              · exact mem_pvars_apply_of (by simp) (ih x (by simp) w inX)
              · exact mem_pvars_apply_of (by simp) (ih k (by simp) w inK)
              · obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp inRest
                exact mem_pvars_apply_of (by simp [member]) (ih q (by simp [member]) w inQ)
      · obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp h
        exact mem_pvars_apply_of member (ih q member w inQ)
  | lambda nm body ih => intro w h; simpa [pvars] using ih w (by simpa [binders] using h)
  | multiLambda n nms body ih => intro w h; simpa [pvars] using ih w (by simpa [binders] using h)
  | subst body repl ihb ihr =>
      intro w h
      simp only [binders, List.mem_append] at h
      simp only [pvars, List.mem_append]
      rcases h with h | h
      · exact .inl (ihb w h)
      · exact .inr (ihr w h)
  | collection ct elems rest ih =>
      intro w h
      simp only [binders, bindersList_eq_flatMap, List.mem_flatMap] at h
      obtain ⟨q, member, inQ⟩ := h
      exact mem_pvars_collection_of member (ih q member w inQ)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member w h
      rcases List.mem_cons.mp member with rfl | later
      · exact head w h
      · exact tail q later w h

/-- A guard-free process whose variables an environment does not bind is closed. -/
theorem closeIn_guardFree_unbound (g : Pattern) (free : guardFree g = true) :
    ∀ env : List (List String), (∀ w ∈ pvars g, lookupBound env w = none) → closeIn env g = g := by
  induction g using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true →
      ∀ env : List (List String), (∀ w ∈ pvars q, lookupBound env w = none) → closeIn env q = q) with
  | bvar n => intro env _; rfl
  | fvar x => intro env unbound; simp [closeIn, unbound x (by simp [pvars])]
  | apply c args ih =>
      intro env unbound
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      rw [closeIn_apply, if_neg free.1]
      conv_rhs => rw [← List.map_id args]
      exact congrArg _ (List.map_congr_left fun q member =>
        ih q member (free.2 q member) env fun w occurs => unbound w (mem_pvars_apply_of member occurs))
  | lambda nm body ih =>
      intro env unbound
      simp [closeIn, ih free env fun w occurs => unbound w (by simpa [pvars] using occurs)]
  | multiLambda n nms body ih =>
      intro env unbound
      simp [closeIn, ih free env fun w occurs => unbound w (by simpa [pvars] using occurs)]
  | subst body repl ihb ihr =>
      intro env unbound
      simp only [guardFree, Bool.and_eq_true] at free
      simp [closeIn, ihb free.1 env fun w occurs => unbound w (by simp [pvars, occurs]),
        ihr free.2 env fun w occurs => unbound w (by simp [pvars, occurs])]
  | collection ct elems rest ih =>
      intro env unbound
      simp only [guardFree, guardFreeList_iff] at free
      simp only [closeIn, closeList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member =>
        ih q member (free q member) env fun w occurs => unbound w (mem_pvars_collection_of member occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ env unbound
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ env unbound
      · exact tail q later freeQ env unbound

/-! ## Principal unifiers of guard-free patterns -/

/-- The values of a principal unifier mention only variables of the two patterns. -/
theorem principal_value_vars {t u : Pattern} {bs : Bindings} (principal : Principal t u bs) :
    ∀ v ∈ pvars t ++ pvars u, ∀ z ∈ pvars (psubst bs.lookup (.fvar v)), z ∈ pvars t ++ pvars u := by
  intro v vIn z zIn
  obtain ⟨σ₀, found⟩ := unify_complete ⟨bs.lookup, principal.solves⟩
  have general := principal.general σ₀.lookup (unify_sound found) (.fvar v)
  by_contra outside
  have none₀ : σ₀.lookup z = none := lookup_eq_none_of_keys (unify_keys found) outside
  have survives : z ∈ pvars (psubst σ₀.lookup (psubst bs.lookup (.fvar v))) :=
    (mem_pvars_psubst _ _ _).mpr ⟨z, zIn, by simp [none₀, pvars]⟩
  rw [general] at survives
  simp only [psubst] at survives
  cases h : σ₀.lookup v with
  | none =>
      rw [h] at survives
      simp only [Option.getD_none, pvars, List.mem_singleton] at survives
      exact outside (survives ▸ vIn)
  | some w =>
      rw [h] at survives
      exact outside (unify_value_vars found (v, w) (mem_of_lookup_eq_some h) z survives)

mutual
/-- Rename the guard constructor: a homomorphism onto guard-free patterns. -/
def eraseGuards : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply (if c = "MFor" then "MFor#" else c) (eraseGuardsList args)
  | .lambda nm b => .lambda nm (eraseGuards b)
  | .multiLambda k nms b => .multiLambda k nms (eraseGuards b)
  | .subst b r => .subst (eraseGuards b) (eraseGuards r)
  | .collection ct elems rest => .collection ct (eraseGuardsList elems) rest
def eraseGuardsList : List Pattern → List Pattern
  | [] => []
  | p :: ps => eraseGuards p :: eraseGuardsList ps
end

theorem eraseGuardsList_eq_map (ps : List Pattern) : eraseGuardsList ps = ps.map eraseGuards := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [eraseGuardsList, ih]

theorem guardFree_eraseGuards (T : Pattern) : guardFree (eraseGuards T) = true := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree (eraseGuards q) = true) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [eraseGuards, eraseGuardsList_eq_map, guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq,
        guardFreeList_iff, List.mem_map]
      refine ⟨by split <;> simp_all, ?_⟩
      rintro _ ⟨q, member, rfl⟩
      exact ih q member
  | lambda nm body ih => simpa [eraseGuards, guardFree] using ih
  | multiLambda n nms body ih => simpa [eraseGuards, guardFree] using ih
  | subst body repl ihb ihr => simp [eraseGuards, guardFree, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [eraseGuards, eraseGuardsList_eq_map, guardFree, guardFreeList_iff, List.mem_map]
      rintro _ ⟨q, member, rfl⟩
      exact ih q member
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem eraseGuards_of_guardFree (T : Pattern) (free : guardFree T = true) : eraseGuards T = T := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → eraseGuards q = q) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      simp only [eraseGuards, if_neg free.1, eraseGuardsList_eq_map]
      conv_rhs => rw [← List.map_id args]
      exact congrArg _ (List.map_congr_left fun q member => ih q member (free.2 q member))
  | lambda nm body ih => simp [eraseGuards, ih free]
  | multiLambda n nms body ih => simp [eraseGuards, ih free]
  | subst body repl ihb ihr =>
      simp only [guardFree, Bool.and_eq_true] at free
      simp [eraseGuards, ihb free.1, ihr free.2]
  | collection ct elems rest ih =>
      simp only [guardFree, guardFreeList_iff] at free
      simp only [eraseGuards, eraseGuardsList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member (free q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

theorem eraseGuards_psubst (s : PSubst) (T : Pattern) :
    eraseGuards (psubst s T) = psubst (fun x => (s x).map eraseGuards) (eraseGuards T) := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      eraseGuards (psubst s q) = psubst (fun x => (s x).map eraseGuards) (eraseGuards q)) with
  | bvar n => rfl
  | fvar x => cases h : s x <;> simp [psubst, eraseGuards, h]
  | apply c args ih =>
      simp only [psubst, eraseGuards, psubstList_eq_map, eraseGuardsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member
  | lambda nm body ih => simp [psubst, eraseGuards, ih]
  | multiLambda n nms body ih => simp [psubst, eraseGuards, ih]
  | subst body repl ihb ihr => simp [psubst, eraseGuards, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, eraseGuards, psubstList_eq_map, eraseGuardsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem guardFree_of_psubst (s : PSubst) (T : Pattern) (free : guardFree (psubst s T) = true) :
    guardFree T = true := by
  induction T using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      guardFree (psubst s q) = true → guardFree q = true) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      simp only [psubst, psubstList_eq_map, guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq,
        guardFreeList_iff, List.mem_map] at free ⊢
      exact ⟨free.1, fun q member => ih q member (free.2 _ ⟨q, member, rfl⟩)⟩
  | lambda nm body ih => exact ih (by simpa [psubst, guardFree] using free)
  | multiLambda n nms body ih => exact ih (by simpa [psubst, guardFree] using free)
  | subst body repl ihb ihr =>
      simp only [psubst, guardFree, Bool.and_eq_true] at free ⊢
      exact ⟨ihb free.1, ihr free.2⟩
  | collection ct elems rest ih =>
      simp only [psubst, psubstList_eq_map, guardFree, guardFreeList_iff, List.mem_map] at free ⊢
      exact fun q member => ih q member (free _ ⟨q, member, rfl⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

/-- The values of a principal unifier of guard-free patterns are guard-free:
erasing the guard constructor of a unifier's values gives another unifier,
which absorbs the principal one. -/
theorem principal_value_guardFree {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (freeT : guardFree t = true) (freeU : guardFree u = true) (v : String) :
    guardFree (psubst bs.lookup (.fvar v)) = true := by
  let τ : PSubst := fun x => some (eraseGuards (psubst bs.lookup (.fvar x)))
  have agree : ∀ p, psubst τ p = psubst (fun x => (bs.lookup x).map eraseGuards) p := fun p =>
    psubst_getD_congr (fun x => by cases h : bs.lookup x <;> simp [τ, psubst, h, eraseGuards]) p
  have erasedT := eraseGuards_psubst bs.lookup t
  have erasedU := eraseGuards_psubst bs.lookup u
  rw [eraseGuards_of_guardFree t freeT] at erasedT
  rw [eraseGuards_of_guardFree u freeU] at erasedU
  have unifies : psubst τ t = psubst τ u := by
    rw [agree, agree, ← erasedT, ← erasedU, principal.solves]
  apply guardFree_of_psubst τ
  rw [principal.general τ unifies (.fvar v)]
  simp [τ, psubst, guardFree_eraseGuards]

/-! ## Principal unifiers agree up to renaming -/

/-- The variable a renaming sends to `w`, if any. -/
def preimage (vs : List String) (ρo : String → String) (w : String) : String :=
  match vs.find? (fun v => ρo v = w) with
  | some v => v
  | none => w

theorem preimage_apply {vs : List String} {ρo : String → String}
    (inj : ∀ a ∈ vs, ∀ b ∈ vs, ρo a = ρo b → a = b) {v : String} (member : v ∈ vs) :
    preimage vs ρo (ρo v) = v := by
  unfold preimage
  cases found : vs.find? (fun v' => decide (ρo v' = ρo v)) with
  | none =>
      exfalso
      have := List.find?_eq_none.mp found v member
      simp at this
  | some v' =>
      simp only
      have same := List.find?_some found
      simp only [decide_eq_true_eq] at same
      exact inj v' (List.mem_of_find?_eq_some found) v member same

/-- **Principal unifiers are unique up to renaming residual variables.** A
principal unifier of two patterns and a principal unifier of their renaming
by `ρo`, injective on their variables, read each variable alike up to one
renaming `ρ` of the residual variables. `ρ` moves only names of the renamed
patterns and is injective on the variables of the renamed unifier's values. -/
theorem principal_renaming {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (ρo : String → String) (inj : ∀ a ∈ pvars t ++ pvars u, ∀ b ∈ pvars t ++ pvars u, ρo a = ρo b → a = b)
    {σ : Bindings} (opened : Principal (rename ρo t) (rename ρo u) σ) :
    ∃ ρ : String → String,
      (∀ w, w ∉ pvars (rename ρo t) ++ pvars (rename ρo u) → ρ w = w) ∧
      (∀ v ∈ pvars t ++ pvars u,
        psubst bs.lookup (.fvar v) = rename ρ (psubst σ.lookup (.fvar (ρo v)))) ∧
      (∀ v ∈ pvars t ++ pvars u, ∀ v' ∈ pvars t ++ pvars u,
        ∀ a ∈ pvars (psubst σ.lookup (.fvar (ρo v))), ∀ b ∈ pvars (psubst σ.lookup (.fvar (ρo v'))),
          ρ a = ρ b → a = b) := by
  have mapped : ∀ v ∈ pvars t ++ pvars u, ρo v ∈ pvars (rename ρo t) ++ pvars (rename ρo u) := by
    intro v vIn
    rw [pvars_rename, pvars_rename, ← List.map_append]
    exact List.mem_map_of_mem vIn
  let θ : String → Pattern := fun v => psubst σ.lookup (.fvar (ρo v))
  let τ' : PSubst := fun w =>
    if w ∈ pvars (rename ρo t) ++ pvars (rename ρo u) then
      some (psubst bs.lookup (.fvar (preimage (pvars t ++ pvars u) ρo w)))
    else none
  let θh : PSubst := fun w => if w ∈ pvars t ++ pvars u then some (θ w) else none
  have τ'Opened : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t ++ pvars u) →
      psubst τ' (rename ρo p) = psubst bs.lookup p := by
    intro p inside
    rw [psubst_rename]
    apply psubst_getD_congr_on
    intro v occurs
    have vIn := inside v occurs
    simp only [τ', psubst, if_pos (mapped v vIn), Option.getD_some, preimage_apply inj vIn]
  have τ'Solves : psubst τ' (rename ρo t) = psubst τ' (rename ρo u) := by
    rw [τ'Opened t (fun v h => List.mem_append_left _ h), τ'Opened u (fun v h => List.mem_append_right _ h)]
    exact principal.solves
  have θhSource : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t ++ pvars u) →
      psubst θh p = psubst σ.lookup (rename ρo p) := by
    intro p inside
    rw [psubst_rename]
    apply psubst_getD_congr_on
    intro v occurs
    simp only [θh, θ, psubst, if_pos (inside v occurs), Option.getD_some]
  have θhSolves : psubst θh t = psubst θh u := by
    rw [θhSource t (fun v h => List.mem_append_left _ h), θhSource u (fun v h => List.mem_append_right _ h)]
    exact opened.solves
  have back : ∀ v ∈ pvars t ++ pvars u, psubst τ' (θ v) = psubst bs.lookup (.fvar v) := by
    intro v vIn
    rw [show θ v = psubst σ.lookup (.fvar (ρo v)) from rfl, opened.general τ' τ'Solves (.fvar (ρo v))]
    simp only [τ', psubst, if_pos (mapped v vIn), Option.getD_some, preimage_apply inj vIn]
  have forth : ∀ v ∈ pvars t ++ pvars u, psubst θh (psubst bs.lookup (.fvar v)) = θ v := by
    intro v vIn
    rw [principal.general θh θhSolves (.fvar v)]
    simp only [θh, psubst, if_pos vIn, Option.getD_some]
  have valueVars : ∀ v ∈ pvars t ++ pvars u, ∀ w ∈ pvars (θ v),
      w ∈ pvars (rename ρo t) ++ pvars (rename ρo u) := fun v vIn w wIn =>
    principal_value_vars opened (ρo v) (mapped v vIn) w wIn
  have toVar : ∀ v ∈ pvars t ++ pvars u, ∀ w ∈ pvars (θ v),
      ∃ n, psubst τ' (.fvar w) = .fvar n ∧ psubst θh (.fvar n) = .fvar w := by
    intro v vIn w wIn
    have fixes : psubst (pcomp θh τ') (θ v) = θ v := by
      rw [← psubst_comp, back v vIn, forth v vIn]
    have := psubst_eq_self_vars fixes w wIn
    rw [pcomp_getD] at this
    obtain ⟨n, nEq, nBack⟩ := psubst_eq_fvar this
    exact ⟨n, nEq, nBack⟩
  let ρ : String → String := fun w =>
    if w ∈ pvars (rename ρo t) ++ pvars (rename ρo u) then
      (match psubst τ' (.fvar w) with
        | .fvar n => n
        | _ => w)
    else w
  have ρOf : ∀ v ∈ pvars t ++ pvars u, ∀ w ∈ pvars (θ v), ∀ n, psubst τ' (.fvar w) = .fvar n → ρ w = n := by
    intro v vIn w wIn n nEq
    simp only [ρ, if_pos (valueVars v vIn w wIn), nEq]
  refine ⟨ρ, fun w outside => by simp only [ρ, if_neg outside], ?_, ?_⟩
  · intro v vIn
    rw [← back v vIn]
    unfold rename
    apply psubst_getD_congr_on
    intro w wIn
    obtain ⟨n, nEq, _⟩ := toVar v vIn w wIn
    simp only [Option.getD_some]
    show psubst τ' (.fvar w) = .fvar (ρ w)
    rw [nEq, ρOf v vIn w wIn n nEq]
  · intro v vIn v' v'In a aIn b bIn same
    obtain ⟨na, naEq, naBack⟩ := toVar v vIn a aIn
    obtain ⟨nb, nbEq, nbBack⟩ := toVar v' v'In b bIn
    rw [ρOf v vIn a aIn na naEq, ρOf v' v'In b bIn nb nbEq] at same
    subst same
    rw [naBack] at nbBack
    exact Pattern.fvar.inj nbBack

/-! ## Opening, substituting and closing with residual values -/

/-- Substituting guard-free values for a frame's variables commutes with
closing, when no inner guard binds a variable of the values: substitute and
close, or close, open the frame with names, and substitute the names. -/
theorem psubst_open_closeIn_residual (names l res : List String) (long : l.length ≤ names.length)
    (θ θ' : PSubst) (A : Pattern) (inCalc : calcTerm A = true) :
    (∀ v ∈ l, v ∉ binders A) → (∀ w ∈ res, w ∉ binders A) →
      ∀ inner : List (List String), (∀ f ∈ inner, ∀ v ∈ l, v ∉ f) → (∀ f ∈ inner, ∀ w ∈ res, w ∉ f) →
      (∀ v ∈ pvars A, v ∈ l → ∃ g, θ v = some g ∧ guardFree g = true ∧ (∀ w ∈ pvars g, w ∈ res) ∧
        θ' (nameOf names l v) = some g) →
      (∀ v ∈ pvars A, v ∉ l → θ v = none) →
      (∀ x ∈ pvars (closeIn (inner ++ [l]) A), (θ' x).getD (.fvar x) = .fvar x) →
      psubst θ' (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar)
          (closeIn (inner ++ [l]) A)) = closeIn inner (psubst θ A) := by
  induction A using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      (∀ v ∈ l, v ∉ binders q) → (∀ w ∈ res, w ∉ binders q) →
      ∀ inner : List (List String), (∀ f ∈ inner, ∀ v ∈ l, v ∉ f) → (∀ f ∈ inner, ∀ w ∈ res, w ∉ f) →
      (∀ v ∈ pvars q, v ∈ l → ∃ g, θ v = some g ∧ guardFree g = true ∧ (∀ w ∈ pvars g, w ∈ res) ∧
        θ' (nameOf names l v) = some g) →
      (∀ v ∈ pvars q, v ∉ l → θ v = none) →
      (∀ x ∈ pvars (closeIn (inner ++ [l]) q), (θ' x).getD (.fvar x) = .fvar x) →
      psubst θ' (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar)
          (closeIn (inner ++ [l]) q)) = closeIn inner (psubst θ q)) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar v =>
      intro _ _ inner innerOk innerRes inL outL closedNone
      cases eqInner : lookupBound inner v with
      | some found =>
          have small := lookupBound_lt eqInner
          have whole : lookupBound (inner ++ [l]) v = some found := by rw [lookupBound_append, eqInner]
          obtain ⟨f, fIn, vIn⟩ := lookupBound_some_mem eqInner
          have notL : v ∉ l := fun member => innerOk f fIn v member vIn
          have θv : θ v = none := outL v (by simp [pvars]) notL
          simp only [closeIn, whole, instantiateAt_code, if_neg (Nat.ne_of_lt small)]
          simp [psubst, boundCode, θv, closeIn, eqInner]
      | none =>
          by_cases member : v ∈ l
          · obtain ⟨g, θv, freeG, resG, θ'v⟩ := inL v (by simp [pvars]) member
            have whole : lookupBound (inner ++ [l]) v = some (inner.length, l.idxOf v) := by
              rw [lookupBound_append, eqInner, lookupBound_single_mem member]; simp
            simp only [closeIn, whole, instantiateAt_code, if_true, names_getElem?_nameOf long member,
              Option.map_some, Option.getD_some]
            simp only [psubst, θ'v, θv, Option.getD_some]
            exact (closeIn_guardFree_unbound g freeG inner fun w wIn =>
              lookupBound_none_of_not_mem fun f fIn => innerRes f fIn w (resG w wIn)).symm
          · have whole : lookupBound (inner ++ [l]) v = none := by
              rw [lookupBound_append, eqInner, lookupBound_single_not_mem member]; simp
            have θv : θ v = none := outL v (by simp [pvars]) member
            have θ'v : (θ' v).getD (.fvar v) = .fvar v := closedNone v (by simp [closeIn, whole, pvars])
            simp only [closeIn, whole, instantiateAt, psubst, θv, Option.getD_none, eqInner]
            exact θ'v
  | apply c args ih =>
      intro kept keptRes inner innerOk innerRes inL outL closedNone
      simp only [calcTerm, calcList_iff] at inCalc
      have inLQ : ∀ q ∈ args, ∀ v ∈ pvars q, v ∈ l →
          ∃ g, θ v = some g ∧ guardFree g = true ∧ (∀ w ∈ pvars g, w ∈ res) ∧
            θ' (nameOf names l v) = some g :=
        fun q member v occurs => inL v (mem_pvars_apply_of member occurs)
      have outLQ : ∀ q ∈ args, ∀ v ∈ pvars q, v ∉ l → θ v = none :=
        fun q member v occurs => outL v (mem_pvars_apply_of member occurs)
      rw [closeIn_apply] at closedNone
      rw [closeIn_apply, instantiateAt_apply]
      simp only [psubst, psubstList_eq_map]
      rw [closeIn_apply, binders_apply] at *
      by_cases guard : c = "MFor"
      · subst guard
        simp only [if_true] at closedNone kept keptRes ⊢
        by_cases short : args.length < 3
        · rw [bindersFor_short _ short] at kept keptRes
          rcases closeFor_cases (inner ++ [l]) args with ⟨_, eq⟩ | ⟨_, _, _, _, rfl, _⟩
          · rw [eq] at closedNone ⊢
            rw [instantiateFor_short _ _ _ (by simpa using short)]
            rcases closeFor_cases inner (args.map (psubst θ)) with ⟨_, eq'⟩ | ⟨_, _, _, _, same, _⟩
            · rw [eq']
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro q member
              exact ih q member (inCalc q member)
                (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩))
                (fun w win bound => keptRes w win (List.mem_flatMap.mpr ⟨q, member, bound⟩))
                inner innerOk innerRes (inLQ q member) (outLQ q member)
                (fun x occurs => closedNone x (mem_pvars_apply_of (List.mem_map_of_mem member) occurs))
            · have := congrArg List.length same; simp at this; omega
          · exact absurd short (by simp)
        · match args, short with
          | [_], h => simp at h
          | [_, _], h => simp at h
          | t :: x :: k :: rest, _ =>
              rw [bindersFor_cons3] at kept keptRes
              simp only [List.mem_append, not_or] at kept keptRes
              rw [closeFor_cons3] at closedNone ⊢
              rw [instantiateFor_cons3]
              simp only [List.map_cons]
              rw [closeFor_cons3]
              have tFixed : psubst θ t = t := psubst_of_none θ t fun v occurs =>
                outL v (mem_pvars_apply_of (by simp) occurs)
                  (fun vin => (kept v vin).1.1.1 occurs)
              have tcFixed : psubst θ' (closeIn [frame t] t) = closeIn [frame t] t :=
                Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.psubst_of_pvars_nil
                  θ' _ (pvars_closed_pattern t)
              rw [tFixed, tcFixed]
              have closedAt : ∀ q y, q ∈ (closeIn [frame t] t :: closeIn (inner ++ [l]) x ::
                  closeIn (frame t :: (inner ++ [l])) k :: rest.map (closeIn (inner ++ [l]))) →
                  y ∈ pvars q → (θ' y).getD (.fvar y) = .fvar y :=
                fun q y member occurs => closedNone y (mem_pvars_apply_of member occurs)
              congr 1
              refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
              refine List.cons_eq_cons.mpr ⟨ih x (by simp) (inCalc x (by simp))
                (fun v vin => (kept v vin).1.1.2) (fun w win => (keptRes w win).1.1.2) inner innerOk innerRes
                (inLQ x (by simp)) (outLQ x (by simp))
                (fun y occurs => closedAt _ y (by simp) occurs), ?_⟩
              refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
              · have step := ih k (by simp) (inCalc k (by simp)) (fun v vin => (kept v vin).1.2)
                  (fun w win => (keptRes w win).1.2)
                  (frame t :: inner) (by
                    intro f member v vin
                    rcases List.mem_cons.mp member with rfl | later
                    · exact fun m => (kept v vin).1.1.1 (frame_subset t v m)
                    · exact innerOk f later v vin)
                  (by
                    intro f member w win
                    rcases List.mem_cons.mp member with rfl | later
                    · exact fun m => (keptRes w win).1.1.1 (frame_subset t w m)
                    · exact innerRes f later w win)
                  (inLQ k (by simp)) (outLQ k (by simp)) (fun y occurs => closedAt _ y (by simp) occurs)
                simpa using step
              · simp only [List.map_map]
                apply List.map_congr_left
                intro q member
                exact ih q (by simp [member]) (inCalc q (by simp [member]))
                  (fun v vin bound => (kept v vin).2 (List.mem_flatMap.mpr ⟨q, member, bound⟩))
                  (fun w win bound => (keptRes w win).2 (List.mem_flatMap.mpr ⟨q, member, bound⟩))
                  inner innerOk innerRes (inLQ q (by simp [member])) (outLQ q (by simp [member]))
                  (fun y occurs => closedAt _ y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_map_of_mem member)))) occurs)
      · simp only [guard, if_false] at closedNone kept keptRes ⊢
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro q member
        exact ih q member (inCalc q member)
          (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩))
          (fun w win bound => keptRes w win (List.mem_flatMap.mpr ⟨q, member, bound⟩))
          inner innerOk innerRes (inLQ q member) (outLQ q member)
          (fun x occurs => closedNone x (mem_pvars_apply_of (List.mem_map_of_mem member) occurs))
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      intro kept keptRes inner innerOk innerRes inL outL closedNone
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map] at closedNone
      simp only [binders, bindersList_eq_flatMap] at kept keptRes
      simp only [closeIn, closeList_eq_map, instantiateAt, instantiateList_eq_map, psubst,
        psubstList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q member
      exact ih q member (inCalc q member)
        (fun v vin bound => kept v vin (List.mem_flatMap.mpr ⟨q, member, bound⟩))
        (fun w win bound => keptRes w win (List.mem_flatMap.mpr ⟨q, member, bound⟩))
        inner innerOk innerRes
        (fun v occurs => inL v (mem_pvars_collection_of member occurs))
        (fun v occurs => outL v (mem_pvars_collection_of member occurs))
        (fun x occurs => closedNone x (mem_pvars_collection_of (List.mem_map_of_mem member) occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ keptQ keptResQ inner innerOk innerRes inLQ outLQ closedQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ keptQ keptResQ inner innerOk innerRes inLQ outLQ closedQ
      · exact tail q later calcQ keptQ keptResQ inner innerOk innerRes inLQ outLQ closedQ

/-- The names an opened body mentions: its own free names, and the names of
the frame's variables. -/
theorem pvars_instantiate_closeIn (names l : List String) (long : l.length ≤ names.length)
    (A : Pattern) (inCalc : calcTerm A = true) :
    ∀ inner : List (List String), ∀ x ∈ pvars (instantiateAt inner.length (fun i => names[i]?.map Pattern.fvar)
        (closeIn (inner ++ [l]) A)), x ∈ pvars (closeIn (inner ++ [l]) A) ∨ ∃ v ∈ l, x = nameOf names l v := by
  induction A using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, calcTerm q = true →
      ∀ inner : List (List String), ∀ x ∈ pvars (instantiateAt inner.length
          (fun i => names[i]?.map Pattern.fvar) (closeIn (inner ++ [l]) q)),
        x ∈ pvars (closeIn (inner ++ [l]) q) ∨ ∃ v ∈ l, x = nameOf names l v) with
  | bvar n => simp [calcTerm] at inCalc
  | fvar v =>
      intro inner x occurs
      cases eqInner : lookupBound inner v with
      | some found =>
          have small := lookupBound_lt eqInner
          have whole : lookupBound (inner ++ [l]) v = some found := by rw [lookupBound_append, eqInner]
          simp only [closeIn, whole, instantiateAt_code, if_neg (Nat.ne_of_lt small)] at occurs
          simp [boundCode, pvars] at occurs
      | none =>
          by_cases member : v ∈ l
          · have whole : lookupBound (inner ++ [l]) v = some (inner.length, l.idxOf v) := by
              rw [lookupBound_append, eqInner, lookupBound_single_mem member]; simp
            simp only [closeIn, whole, instantiateAt_code, if_true, names_getElem?_nameOf long member,
              Option.map_some, Option.getD_some, pvars, List.mem_singleton] at occurs
            exact .inr ⟨v, member, occurs⟩
          · have whole : lookupBound (inner ++ [l]) v = none := by
              rw [lookupBound_append, eqInner, lookupBound_single_not_mem member]; simp
            simp only [closeIn, whole, instantiateAt] at occurs
            exact .inl (by simpa [closeIn, whole] using occurs)
  | apply c args ih =>
      intro inner x occurs
      simp only [calcTerm, calcList_iff] at inCalc
      rw [closeIn_apply, instantiateAt_apply] at occurs
      rw [closeIn_apply]
      by_cases guard : c = "MFor"
      · subst guard
        simp only [if_true] at occurs ⊢
        rcases closeFor_cases (inner ++ [l]) args with ⟨short, eq⟩ | ⟨t, y, k, rest, rfl, eq⟩
        · rw [eq] at occurs ⊢
          rw [instantiateFor_short _ _ _ (by simpa using short), pvars_apply, pvarsList_eq_flatMap] at occurs
          obtain ⟨r, rIn, xIn⟩ := List.mem_flatMap.mp occurs
          obtain ⟨r', r'In, rfl⟩ := List.mem_map.mp rIn
          obtain ⟨q, member, rfl⟩ := List.mem_map.mp r'In
          rcases ih q member (inCalc q member) inner x xIn with own | named
          · exact .inl (mem_pvars_apply_of (List.mem_map_of_mem member) own)
          · exact .inr named
        · rw [eq] at occurs ⊢
          rw [instantiateFor_cons3, pvars_apply, pvarsList_eq_flatMap] at occurs
          obtain ⟨r, rIn, xIn⟩ := List.mem_flatMap.mp occurs
          simp only [List.mem_cons, List.mem_map] at rIn
          rcases rIn with rfl | rfl | rfl | ⟨r', ⟨q, member, rfl⟩, rfl⟩
          · rw [pvars_closed_pattern] at xIn; cases xIn
          · rcases ih y (by simp) (inCalc y (by simp)) inner x xIn with own | named
            · exact .inl (mem_pvars_apply_of (by simp) own)
            · exact .inr named
          · have step := ih k (by simp) (inCalc k (by simp)) (frame t :: inner) x (by simpa using xIn)
            rcases step with own | named
            · exact .inl (mem_pvars_apply_of (q := closeIn (frame t :: (inner ++ [l])) k) (by simp)
                (by simpa using own))
            · exact .inr named
          · rcases ih q (by simp [member]) (inCalc q (by simp [member])) inner x xIn with own | named
            · exact .inl (mem_pvars_apply_of (q := closeIn (inner ++ [l]) q)
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_map_of_mem member)))) own)
            · exact .inr named
      · simp only [guard, if_false] at occurs ⊢
        rw [pvars_apply, pvarsList_eq_flatMap] at occurs
        obtain ⟨r, rIn, xIn⟩ := List.mem_flatMap.mp occurs
        obtain ⟨r', r'In, rfl⟩ := List.mem_map.mp rIn
        obtain ⟨q, member, rfl⟩ := List.mem_map.mp r'In
        rcases ih q member (inCalc q member) inner x xIn with own | named
        · exact .inl (mem_pvars_apply_of (List.mem_map_of_mem member) own)
        · exact .inr named
  | lambda nm body ih => simp [calcTerm] at inCalc
  | multiLambda n nms body ih => simp [calcTerm] at inCalc
  | subst body repl ihb ihr => simp [calcTerm] at inCalc
  | collection ct elems rest ih =>
      intro inner x occurs
      simp only [calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none, calcList_iff] at inCalc
      obtain ⟨rfl, inCalc⟩ := inCalc
      simp only [closeIn, closeList_eq_map, instantiateAt, instantiateList_eq_map, pvars,
        pvarsList_eq_flatMap, List.mem_flatMap, List.mem_map] at occurs ⊢
      obtain ⟨r, ⟨r', ⟨q, member, rfl⟩, rfl⟩, xIn⟩ := occurs
      rcases ih q member (inCalc q member) inner x xIn with own | named
      · exact .inl ⟨_, ⟨q, member, rfl⟩, own⟩
      · exact .inr named
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member calcQ inner x occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact head calcQ inner x occurs
      · exact tail q later calcQ inner x occurs

/-! ## Completeness with residual variables -/

theorem rename_par (g : String → String) (p q : Pattern) :
    rename g (par p q) = par (rename g p) (rename g q) := by
  simp [par, pPar, rename_collection]

theorem rename_pReflect (g : String → String) (x p : Pattern) :
    rename g (pReflect x p) = pReflect (rename g x) (rename g p) := by
  simp [pReflect, rename_apply]

/-- **COMM completeness with residual variables.** A COMM of the uniform dot
on guard-free calculus patterns is matched by the executable COMM up to a
renaming of residual names: the renaming fixes every name to avoid, and it is
injective on the executable reduct's other names, its fresh residual names. -/
theorem commClosed_complete_residual (avoid : List String) (t u x A B : Pattern) (bs : Bindings)
    (principal : Principal t u bs) (admitted : uniformCalc t A u B bs)
    (fresh : ∀ z ∈ pvars (close (par (pFor t x A) (pFor u x B))), z ∈ avoid) :
    ∃ Q' ∈ commClosed avoid (close (pFor t x A)) (close (pFor u x B)), ∃ ρ : String → String,
      (∀ z ∈ avoid, ρ z = z) ∧
      (∀ a ∈ pvars Q', ∀ b ∈ pvars Q', a ∉ avoid → b ∉ avoid → ρ a = ρ b → a = b) ∧
      AlphaEq (rename ρ Q') (par (applyDot bs A) (applyDot bs B)) := by
  obtain ⟨⟨apart, complete⟩, freeT, freeU, calcT, calcU, calcA, calcB⟩ := admitted
  have closeT : close (pFor t x A) = pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A) :=
    closeIn_pFor [] t x A
  have closeU : close (pFor u x B) = pFor (closeIn [frame u] u) (close x) (closeIn [frame u] B) :=
    closeIn_pFor [] u x B
  have closeWhole : close (par (pFor t x A) (pFor u x B)) =
      par (pFor (closeIn [frame t] t) (close x) (closeIn [frame t] A))
        (pFor (closeIn [frame u] u) (close x) (closeIn [frame u] B)) := by
    unfold close; rw [closeIn_par]; exact congrArg₂ par closeT closeU
  rw [closeT, closeU]
  obtain ⟨openT, longT⟩ := opened_pattern avoid 0 t calcT freeT
  obtain ⟨openU, longU⟩ := opened_pattern avoid (codeCount (closeIn [frame t] t)) u calcU freeU
  have frameT : frame t = pvars t := frame_of_guardFree t freeT
  have frameU : frame u = pvars u := frame_of_guardFree u freeU
  let L := freshNames avoid 0 (codeCount (closeIn [frame t] t))
  let R := freshNames avoid (codeCount (closeIn [frame t] t)) (codeCount (closeIn [frame u] u))
  let gL := nameOf L (frame t)
  let gR := nameOf R (frame u)
  have injL : ∀ a ∈ pvars t, ∀ b ∈ pvars t, gL a = gL b → a = b := by
    rw [← frameT]; exact nameOf_injOn (freshNames_nodup _ _ _) longT
  have injR : ∀ a ∈ pvars u, ∀ b ∈ pvars u, gR a = gR b → a = b := by
    rw [← frameU]; exact nameOf_injOn (freshNames_nodup _ _ _) longU
  have inL : ∀ a ∈ pvars t, gL a ∈ L := fun a member => nameOf_mem longT (by rw [frameT]; exact member)
  have inR : ∀ b ∈ pvars u, gR b ∈ R := fun b member => nameOf_mem longU (by rw [frameU]; exact member)
  have apartLR : ∀ a ∈ pvars t, ∀ b ∈ pvars u, gL a ≠ gR b := fun a ha b hb same =>
    freshNames_disjoint (inL a ha) (same ▸ inR b hb)
  obtain ⟨σ, found⟩ := unify_opened_exists principal gL gR injL injR apartLR
  have principalσ := unify_principal found
  let ρo : String → String := fun w => if w ∈ pvars t then gL w else gR w
  have ρt : rename ρo t = rename gL t := rename_congr fun w member => by simp [ρo, member]
  have ρu : rename ρo u = rename gR u := rename_congr fun w member => by
    have : w ∉ pvars t := fun inT => apart.patterns w inT member
    simp [ρo, this]
  have openedPrincipal : Principal (rename ρo t) (rename ρo u) σ := by rw [ρt, ρu]; exact principalσ
  have injO : ∀ a ∈ pvars t ++ pvars u, ∀ b ∈ pvars t ++ pvars u, ρo a = ρo b → a = b := by
    intro a aIn b bIn same
    by_cases aT : a ∈ pvars t <;> by_cases bT : b ∈ pvars t
    · simp only [ρo, aT, bT, if_true] at same; exact injL a aT b bT same
    · have bU : b ∈ pvars u := (List.mem_append.mp bIn).resolve_left bT
      simp only [ρo, aT, bT, if_true, if_false] at same
      exact absurd same (apartLR a aT b bU)
    · have aU : a ∈ pvars u := (List.mem_append.mp aIn).resolve_left aT
      simp only [ρo, aT, bT, if_true, if_false] at same
      exact absurd same.symm (apartLR b bT a aU)
    · have aU : a ∈ pvars u := (List.mem_append.mp aIn).resolve_left aT
      have bU : b ∈ pvars u := (List.mem_append.mp bIn).resolve_left bT
      simp only [ρo, aT, bT, if_false] at same; exact injR a aU b bU same
  obtain ⟨ρ, ρFixes, ρReads, ρInj⟩ := principal_renaming principal ρo injO openedPrincipal
  have vsEq : pvars (openPattern L (closeIn [frame t] t)) ++ pvars (openPattern R (closeIn [frame u] u)) =
      pvars (rename ρo t) ++ pvars (rename ρo u) := by rw [openT, openU, ρt, ρu]
  let S := completeBindings (pvars (openPattern L (closeIn [frame t] t)) ++
    pvars (openPattern R (closeIn [frame u] u))) σ
  have opensIn : ∀ w ∈ pvars (rename ρo t) ++ pvars (rename ρo u), w ∈ L ∨ w ∈ R := by
    intro w member
    rw [ρt, ρu, pvars_rename, pvars_rename] at member
    rcases List.mem_append.mp member with inT | inU
    · obtain ⟨a, aIn, rfl⟩ := List.mem_map.mp inT; exact .inl (inL a aIn)
    · obtain ⟨b, bIn, rfl⟩ := List.mem_map.mp inU; exact .inr (inR b bIn)
  have avoidOutside : ∀ z ∈ avoid, z ∉ pvars (rename ρo t) ++ pvars (rename ρo u) := by
    intro z member inside
    rcases opensIn z inside with h | h
    · exact freshNames_fresh h member
    · exact freshNames_fresh h member
  have ρAvoid : ∀ z ∈ avoid, ρ z = z := fun z member => ρFixes z (avoidOutside z member)
  have SReads : ∀ v ∈ pvars t ++ pvars u, S.lookup (ρo v) = some (psubst σ.lookup (.fvar (ρo v))) := by
    intro v vIn
    have mapped : ρo v ∈ pvars (openPattern L (closeIn [frame t] t)) ++
        pvars (openPattern R (closeIn [frame u] u)) := by
      rw [vsEq, pvars_rename, pvars_rename, ← List.map_append]; exact List.mem_map_of_mem vIn
    rw [lookup_completeBindings]
    cases h : σ.lookup (ρo v) with
    | some value => simp [psubst, h]
    | none =>
        simp only
        rw [if_pos mapped]
        simp [psubst, h]
  have SOutside : ∀ z, z ∉ pvars (rename ρo t) ++ pvars (rename ρo u) → S.lookup z = none := by
    intro z outside
    have σNone : σ.lookup z = none := lookup_eq_none_of_keys openedPrincipal.keys outside
    rw [lookup_completeBindings, σNone]
    exact if_neg (by rw [vsEq]; exact outside)
  have inWhole : ∀ z, z ∈ pvars (closeIn [frame t] A) ∨ z ∈ pvars (closeIn [frame u] B) → z ∈ avoid := by
    intro z occurs
    apply fresh
    rw [closeWhole, pvars_par, pvars_pFor, pvars_pFor]
    rcases occurs with h | h <;> simp [h]
  have valueFree : ∀ v, guardFree (psubst bs.lookup (.fvar v)) = true :=
    principal_value_guardFree principal freeT freeU
  have resA : ∀ w ∈ pvars t ++ pvars u, w ∉ binders A := by
    intro w member bound
    rcases List.mem_append.mp member with inT | inU
    · exact apart.leftKept w inT bound
    · exact apart.rightOutside w inU (binders_subset_pvars A w bound)
  have resB : ∀ w ∈ pvars t ++ pvars u, w ∉ binders B := by
    intro w member bound
    rcases List.mem_append.mp member with inT | inU
    · exact apart.leftOutside w inT (binders_subset_pvars B w bound)
    · exact apart.rightKept w inU bound
  have foA : firstOrder (openWith L (closeIn [frame t] A)) = true :=
    firstOrder_instantiateAt _ (fun i v eq => by
      cases h : L[i]? with
      | none => simp [h] at eq
      | some n => simp only [h, Option.map_some, Option.some.injEq] at eq; subst eq; rfl)
      _ (firstOrder_closeIn A calcA _) 0
  have foB : firstOrder (openWith R (closeIn [frame u] B)) = true :=
    firstOrder_instantiateAt _ (fun i v eq => by
      cases h : R[i]? with
      | none => simp [h] at eq
      | some n => simp only [h, Option.map_some, Option.some.injEq] at eq; subst eq; rfl)
      _ (firstOrder_closeIn B calcB _) 0
  -- the value each side quotes for a pattern variable
  have quoted : ∀ v ∈ pvars t ++ pvars u, ∃ b, bs.lookup v = some b ∧
      pcomp (fun x => some (.fvar (ρ x))) (dotOf S) (ρo v) = some (nQuote b) ∧
      guardFree (nQuote b) = true ∧ ∀ w ∈ pvars (nQuote b), w ∈ pvars t ++ pvars u := by
    intro v vIn
    obtain ⟨b, bLookup⟩ := Option.isSome_iff_exists.mp (complete v vIn)
    have bValue : psubst bs.lookup (.fvar v) = b := by simp [psubst, bLookup]
    refine ⟨b, bLookup, ?_, ?_, ?_⟩
    · simp only [pcomp, dotOf, SReads v vIn, Option.map_some]
      congr 1
      show nQuote (rename ρ (psubst σ.lookup (.fvar (ρo v)))) = nQuote b
      rw [← ρReads v vIn, bValue]
    · have := valueFree v
      rw [bValue] at this
      simp [nQuote, guardFree, guardFreeList, this]
    · intro w wIn
      rw [pvars_nQuote] at wIn
      exact principal_value_vars principal v vIn w (bValue ▸ wIn)
  have bodyA : rename ρ (applyDot S (openWith L (closeIn [frame t] A))) = close (applyDot bs A) := by
    rw [applyDot_eq S _ foA, applyDot_eq bs A (firstOrder_of_calcTerm A calcA)]
    unfold rename
    rw [psubst_comp]
    have := psubst_open_closeIn_residual L (frame t) (pvars t ++ pvars u) longT (dotOf bs)
      (pcomp (fun x => some (.fvar (ρ x))) (dotOf S)) A calcA
      (by rw [frameT]; exact apart.leftKept) resA [] (by simp) (by simp)
      (by
        intro v occurs member
        rw [frameT] at member
        have vIn : v ∈ pvars t ++ pvars u := List.mem_append_left _ member
        obtain ⟨b, bLookup, reads, freeB, varsB⟩ := quoted v vIn
        have ρov : ρo v = nameOf L (frame t) v := by simp only [ρo, if_pos member]; rfl
        rw [ρov] at reads
        exact ⟨nQuote b, by simp [dotOf, bLookup], freeB, varsB, reads⟩)
      (by
        intro v occurs notFrame
        rw [frameT] at notFrame
        have notU : v ∉ pvars u := fun inU => apart.rightOutside v inU occurs
        show (bs.lookup v).map nQuote = none
        rw [lookup_eq_none_of_keys (x := v) principal.keys (by simp [notFrame, notU])]
        rfl)
      (by
        intro z occurs
        have zAvoid := inWhole z (.inl (by simpa using occurs))
        rw [pcomp_getD]
        simp [dotOf, SOutside z (avoidOutside z zAvoid), psubst, ρAvoid z zAvoid])
    simp only [List.length_nil, List.nil_append] at this
    exact this
  have bodyB : rename ρ (applyDot S (openWith R (closeIn [frame u] B))) = close (applyDot bs B) := by
    rw [applyDot_eq S _ foB, applyDot_eq bs B (firstOrder_of_calcTerm B calcB)]
    unfold rename
    rw [psubst_comp]
    have := psubst_open_closeIn_residual R (frame u) (pvars t ++ pvars u) longU (dotOf bs)
      (pcomp (fun x => some (.fvar (ρ x))) (dotOf S)) B calcB
      (by rw [frameU]; exact apart.rightKept) resB [] (by simp) (by simp)
      (by
        intro v occurs member
        rw [frameU] at member
        have vIn : v ∈ pvars t ++ pvars u := List.mem_append_right _ member
        obtain ⟨b, bLookup, reads, freeB, varsB⟩ := quoted v vIn
        have notT : v ∉ pvars t := fun inT => apart.patterns v inT member
        have ρov : ρo v = nameOf R (frame u) v := by simp only [ρo, if_neg notT]; rfl
        rw [ρov] at reads
        exact ⟨nQuote b, by simp [dotOf, bLookup], freeB, varsB, reads⟩)
      (by
        intro v occurs notFrame
        rw [frameU] at notFrame
        have notT : v ∉ pvars t := fun inT => apart.leftOutside v inT occurs
        show (bs.lookup v).map nQuote = none
        rw [lookup_eq_none_of_keys (x := v) principal.keys (by simp [notFrame, notT])]
        rfl)
      (by
        intro z occurs
        have zAvoid := inWhole z (.inr (by simpa using occurs))
        rw [pcomp_getD]
        simp [dotOf, SOutside z (avoidOutside z zAvoid), psubst, ρAvoid z zAvoid])
    simp only [List.length_nil, List.nil_append] at this
    exact this
  -- the fresh names of the executable reduct are residual names
  have freshIn : ∀ a, a ∈ pvars (applyDot S (openWith L (closeIn [frame t] A))) ++
      pvars (applyDot S (openWith R (closeIn [frame u] B))) → a ∉ avoid →
      ∃ v ∈ pvars t ++ pvars u, a ∈ pvars (psubst σ.lookup (.fvar (ρo v))) := by
    intro a aIn aOut
    rcases List.mem_append.mp aIn with inA | inB
    · rw [applyDot_eq S _ foA, mem_pvars_psubst] at inA
      obtain ⟨w, wIn, aW⟩ := inA
      rcases pvars_instantiate_closeIn L (frame t) longT A calcA [] w wIn with own | ⟨v, vFrame, rfl⟩
      · have wAvoid := inWhole w (.inl (by simpa using own))
        simp [SOutside w (avoidOutside w wAvoid), pvars] at aW
        exact absurd (aW ▸ wAvoid) aOut
      · have vT : v ∈ pvars t := by rw [← frameT]; exact vFrame
        have ρov : ρo v = nameOf L (frame t) v := by simp only [ρo, if_pos vT]; rfl
        have lookupS := SReads v (List.mem_append_left _ vT)
        rw [ρov] at lookupS
        simp only [lookupS, Option.map_some, Option.getD_some, pvars_nQuote] at aW
        exact ⟨v, List.mem_append_left _ vT, by rw [ρov]; exact aW⟩
    · rw [applyDot_eq S _ foB, mem_pvars_psubst] at inB
      obtain ⟨w, wIn, aW⟩ := inB
      rcases pvars_instantiate_closeIn R (frame u) longU B calcB [] w wIn with own | ⟨v, vFrame, rfl⟩
      · have wAvoid := inWhole w (.inr (by simpa using own))
        simp [SOutside w (avoidOutside w wAvoid), pvars] at aW
        exact absurd (aW ▸ wAvoid) aOut
      · have vU : v ∈ pvars u := by rw [← frameU]; exact vFrame
        have notT : v ∉ pvars t := fun inT => apart.patterns v inT vU
        have ρov : ρo v = nameOf R (frame u) v := by simp only [ρo, if_neg notT]; rfl
        have lookupS := SReads v (List.mem_append_right _ vU)
        rw [ρov] at lookupS
        simp only [lookupS, Option.map_some, Option.getD_some, pvars_nQuote] at aW
        exact ⟨v, List.mem_append_right _ vU, by rw [ρov]; exact aW⟩
  refine ⟨par (applyDot S (openWith L (closeIn [frame t] A))) (applyDot S (openWith R (closeIn [frame u] B))),
    ?_, ρ, ρAvoid, ?_, ?_⟩
  · have found' : unify (openPattern (freshNames avoid 0 (codeCount (closeIn [frame t] t)))
          (closeIn [frame t] t)) (openPattern (freshNames avoid (codeCount (closeIn [frame t] t))
          (codeCount (closeIn [frame u] u))) (closeIn [frame u] u)) = some σ := by
      rw [openT, openU]; exact found
    simp [commClosed, asGuard_pFor, guardFree_closeIn, freeT, freeU, found']
    rfl
  · intro a aIn b bIn aOut bOut same
    rw [pvars_par] at aIn bIn
    obtain ⟨v, vIn, aV⟩ := freshIn a aIn aOut
    obtain ⟨v', v'In, bV⟩ := freshIn b bIn bOut
    exact ρInj v vIn v' v'In a aV b bV same
  · unfold AlphaEq
    rw [rename_par, bodyA, bodyB]
    unfold close
    rw [← closeIn_par]
    exact close_close _

/-- **Completeness with residual variables.** Every relational step of the
uniform dot on guard-free calculus patterns is matched by a step of the
closed form, up to a renaming that fixes every name to avoid and is
injective on the fresh names of the executable reduct. -/
theorem stepClosed_complete_residual {P Q : Pattern} (step : Step uniformCalc P Q) :
    ∀ avoid : List String, (∀ z ∈ pvars (close P), z ∈ avoid) →
      ∃ Q' ∈ stepClosed avoid (close P), ∃ ρ : String → String, (∀ z ∈ avoid, ρ z = z) ∧
        (∀ a ∈ pvars Q', ∀ b ∈ pvars Q', a ∉ avoid → b ∉ avoid → ρ a = ρ b → a = b) ∧
        AlphaEq (rename ρ Q') Q := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro avoid fresh
      obtain ⟨Q', member, rest⟩ := commClosed_complete_residual avoid t u x A B bs principal admitted fresh
      refine ⟨Q', ?_, rest⟩
      unfold close
      rw [closeIn_par, stepClosed_par]
      exact List.mem_append_left _ member
  | parallel R _ ih =>
      intro avoid fresh
      have freshR : ∀ z ∈ pvars (close R), z ∈ avoid := fun z occurs => fresh z (by
        unfold close at occurs ⊢; rw [closeIn_par, pvars_par]; exact List.mem_append_right _ occurs)
      obtain ⟨Q₁, member, ρ, ρAvoid, ρInj, alpha⟩ := ih avoid fun z occurs => fresh z (by
        unfold close; rw [closeIn_par, pvars_par]; exact List.mem_append_left _ occurs)
      refine ⟨par Q₁ (close R), ?_, ρ, ρAvoid, ?_, ?_⟩
      · unfold close at member ⊢
        rw [closeIn_par, stepClosed_par]
        exact List.mem_append_right _ (List.mem_map_of_mem member)
      · intro a aIn b bIn aOut bOut same
        rw [pvars_par] at aIn bIn
        have aQ : a ∈ pvars Q₁ := (List.mem_append.mp aIn).resolve_right fun h => aOut (freshR a h)
        have bQ : b ∈ pvars Q₁ := (List.mem_append.mp bIn).resolve_right fun h => bOut (freshR b h)
        exact ρInj a aQ b bQ aOut bOut same
      · rw [rename_par, rename_of_fixed ρ (close R) fun z occurs => ρAvoid z (freshR z occurs)]
        exact AlphaEq.par alpha (alphaEq_close R)
  | congruence before _ after ih =>
      intro avoid fresh
      have same : close _ = close _ := before
      obtain ⟨Q₁, member, ρ, ρAvoid, ρInj, alpha⟩ := ih avoid (by rw [← same]; exact fresh)
      exact ⟨Q₁, by rw [same]; exact member, ρ, ρAvoid, ρInj, alpha.trans after⟩
  | reflect x _ ih =>
      intro avoid fresh
      have freshX : ∀ z ∈ pvars (close x), z ∈ avoid := fun z occurs => fresh z (by
        unfold close at occurs ⊢; rw [closeIn_pReflect, pvars_pReflect]; exact List.mem_append_left _ occurs)
      obtain ⟨Q₁, member, ρ, ρAvoid, ρInj, alpha⟩ := ih avoid fun z occurs => fresh z (by
        unfold close; rw [closeIn_pReflect, pvars_pReflect]; exact List.mem_append_right _ occurs)
      refine ⟨pFor (tProc Q₁) (close x) pZero, ?_, ρ, ρAvoid, ?_, ?_⟩
      · unfold close at member ⊢
        rw [closeIn_pReflect, stepClosed_reflect]
        exact List.mem_map_of_mem member
      · intro a aIn b bIn aOut bOut same
        have shape : pvars (pFor (tProc Q₁) (close x) pZero) = pvars Q₁ ++ pvars (close x) := by
          simp [pvars_pFor, tProc, pZero, pvars, pvars.pvarsList]
        rw [shape, List.mem_append] at aIn bIn
        have aQ : a ∈ pvars Q₁ := aIn.resolve_right fun h => aOut (freshX a h)
        have bQ : b ∈ pvars Q₁ := bIn.resolve_right fun h => bOut (freshX b h)
        exact ρInj a aQ b bQ aOut bOut same
      · rw [rename_pFor, rename_of_fixed ρ (close x) fun z occurs => ρAvoid z (freshX z occurs)]
        have zero : rename ρ pZero = pZero := rfl
        have proc : rename ρ (tProc Q₁) = tProc (rename ρ Q₁) := by simp [tProc, rename_apply]
        rw [zero, proc]
        exact alphaEq_listener alpha (alphaEq_close x)

/-- **Completeness of the corrected step with residual variables**, up to
renaming residual names: the renaming fixes every free name of the source and
is injective on the reduct's fresh names. -/
theorem cstep_complete_residual {P Q : Pattern} (step : Step uniformCalc P Q) :
    ∃ Q' ∈ cstep P, ∃ ρ : String → String, (∀ z ∈ pvars (close P), ρ z = z) ∧
      (∀ a ∈ pvars Q', ∀ b ∈ pvars Q', a ∉ pvars (close P) → b ∉ pvars (close P) → ρ a = ρ b → a = b) ∧
      AlphaEq (rename ρ Q') Q :=
  stepClosed_complete_residual step (pvars (close P)) fun _ occurs => occurs

/-! ## Controls -/

namespace ResidualControls

def X : Pattern := .fvar "X"
def Y : Pattern := .fvar "Y"

theorem closeIn_nil_fvar (n : String) : closeIn [] (.fvar n) = .fvar n := rfl

theorem par_injective {a b c d : Pattern} (same : par a b = par c d) : a = c ∧ b = d := by
  simpa [par, pPar] using same

theorem principal_XY : Principal X Y [("X", Y)] := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro τ solves p
  rw [psubst_comp]
  apply psubst_getD_congr_on
  intro v _
  by_cases h : v = "X"
  · subst h
    simp only [X, Y, psubst] at solves
    simp [pcomp, Bindings.lookup, psubst, Y, solves]
  · have h' : ("X" = v) = False := by simp [Ne.symm h]
    simp [pcomp, Bindings.lookup, h']

theorem principal_YX : Principal X Y [("Y", X)] := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro τ solves p
  rw [psubst_comp]
  apply psubst_getD_congr_on
  intro v _
  by_cases h : v = "Y"
  · subst h
    simp only [X, Y, psubst] at solves
    simp [pcomp, Bindings.lookup, psubst, X, solves]
  · have h' : ("Y" = v) = False := by simp [Ne.symm h]
    simp [pcomp, Bindings.lookup, h']

/-- `for(X <- @0)X | for(Y <- @0)Y`: each input reads its own pattern variable,
and the two variables unify with each other. -/
def twoNames : Proc := par (pFor X demoChan X) (pFor Y demoChan Y)

theorem twoNames_apart : Apart X X Y Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- With the orientation `{Y ↦ X}` the manuscript's dot reads `X | @X`. -/
theorem manuscript_dot_reduct : Step conventional twoNames (par X (nQuote X)) := by
  have step := Step.comm (admit := conventional) X Y demoChan X Y [("Y", X)] principal_YX twoNames_apart
  have reduct : par (applyDot [("Y", X)] X) (applyDot [("Y", X)] Y) = par X (nQuote X) := by decide +kernel
  rw [reduct] at step
  exact step

theorem cstep_twoNames : cstep twoNames = [par (nQuote (.fvar "##")) (nQuote (.fvar "##"))] := by
  decide +kernel

/-- **The manuscript's dot is not determined up to renaming.** The reduct
`X | @X` of the orientation `{Y ↦ X}` is a relational step, and no renaming
of the executable reduct is alpha-equivalent to it: one of its continuations
is not quoted. -/
theorem manuscript_dot_not_up_to_renaming :
    Step conventional twoNames (par X (nQuote X)) ∧
      ∀ Q' ∈ cstep twoNames, ∀ ρ : String → String, ¬ AlphaEq (rename ρ Q') (par X (nQuote X)) := by
  refine ⟨manuscript_dot_reduct, ?_⟩
  intro Q' member ρ alpha
  rw [cstep_twoNames, List.mem_singleton] at member
  subst member
  unfold AlphaEq close at alpha
  rw [rename_par, closeIn_par, closeIn_par] at alpha
  have first := (par_injective alpha).1
  rw [show rename ρ (nQuote (.fvar "##")) = nQuote (.fvar (ρ "##")) from by simp [nQuote, rename_apply, rename_fvar],
    closeIn_nQuote, closeIn_nil_fvar, show X = Pattern.fvar "X" from rfl, closeIn_nil_fvar] at first
  simp [nQuote] at first

/-- With the uniform dot the same source reads `@Y | @Y`, the executable
reduct with its residual name renamed. -/
theorem uniform_dot_up_to_renaming :
    Step uniformCalc twoNames (par (nQuote Y) (nQuote Y)) ∧
      ∃ Q' ∈ cstep twoNames, AlphaEq (rename (fun w => if w = "##" then "Y" else w) Q') (par (nQuote Y) (nQuote Y)) := by
  refine ⟨?_, _, by rw [cstep_twoNames]; exact List.mem_singleton_self _, by decide +kernel⟩
  have step := Step.comm (admit := uniformCalc) X Y demoChan X Y _ (principal_completeBindings principal_XY)
    ⟨⟨twoNames_apart, complete_completeBindings X Y _⟩, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  have reduct : par (applyDot (completeBindings (pvars X ++ pvars Y) [("X", Y)]) X)
      (applyDot (completeBindings (pvars X ++ pvars Y) [("X", Y)]) Y) = par (nQuote Y) (nQuote Y) := by
    decide +kernel
  rw [reduct] at step
  exact step

/-- `(for(X <- @0)X | for(Y <- @0)0) | Y`: the surrounding process has a free
name `Y`, which is also the second input's pattern variable. -/
def contextSource : Proc := par (par (pFor X demoChan X) (pFor Y demoChan pZero)) Y

/-- The relational reduct that reads the residual name as `Y`. -/
def contextReduct : Proc := par (par (nQuote Y) pZero) Y

theorem context_step : Step uniformCalc contextSource contextReduct := by
  have apart : Apart X X Y pZero := by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  have step := Step.comm (admit := uniformCalc) X Y demoChan X pZero _ (principal_completeBindings principal_XY)
    ⟨⟨apart, complete_completeBindings X Y _⟩, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  have reduct : par (applyDot (completeBindings (pvars X ++ pvars Y) [("X", Y)]) X)
      (applyDot (completeBindings (pvars X ++ pvars Y) [("X", Y)]) pZero) = par (nQuote Y) pZero := by
    decide +kernel
  rw [reduct] at step
  exact .parallel Y step

theorem cstep_contextSource : cstep contextSource = [par (par (nQuote (.fvar "###")) pZero) Y] := by
  decide +kernel

/-- **A residual name can meet a free name of the context.** The relational
rule may read the residual name as the surrounding process's free `Y`; the
executable reads a fresh name. A renaming that fixes the free names relates
the two, and no renaming injective on the executable reduct's names does. -/
theorem residual_meets_context :
    Step uniformCalc contextSource contextReduct ∧
      (∃ Q' ∈ cstep contextSource, ∃ ρ : String → String, ρ "Y" = "Y" ∧
        AlphaEq (rename ρ Q') contextReduct) ∧
      ∀ Q' ∈ cstep contextSource, ∀ ρ : String → String,
        (∀ a ∈ pvars Q', ∀ b ∈ pvars Q', ρ a = ρ b → a = b) → ¬ AlphaEq (rename ρ Q') contextReduct := by
  refine ⟨context_step, ⟨_, by rw [cstep_contextSource]; exact List.mem_singleton_self _,
    fun w => if w = "###" then "Y" else w, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro Q' member ρ inj alpha
  rw [cstep_contextSource, List.mem_singleton] at member
  subst member
  unfold AlphaEq close at alpha
  have left : closeIn [] (rename ρ (par (par (nQuote (.fvar "###")) pZero) Y)) =
      par (par (nQuote (.fvar (ρ "###"))) pZero) (.fvar (ρ "Y")) := by
    rw [rename_par, rename_par,
      show rename ρ (nQuote (.fvar "###")) = nQuote (.fvar (ρ "###")) from by
        simp [nQuote, rename_apply, rename_fvar],
      show rename ρ pZero = pZero from rfl, show rename ρ Y = .fvar (ρ "Y") from rfl,
      closeIn_par, closeIn_par, closeIn_nQuote, closeIn_nil_fvar, closeIn_pZero, closeIn_nil_fvar]
  have right : closeIn [] contextReduct = par (par (nQuote (.fvar "Y")) pZero) (.fvar "Y") := by decide +kernel
  rw [left, right] at alpha
  obtain ⟨inner, second⟩ := par_injective alpha
  have first := (par_injective inner).1
  simp only [nQuote, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, and_true, true_and] at first
  simp only [Pattern.fvar.injEq] at second
  have collide := inj "###" (by decide +kernel) "Y" (by decide +kernel) (by rw [first, second])
  exact absurd collide (by decide)

end ResidualControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
