import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSound

/-!
# The unifier decides within its fuel

`unifyTerms` is fuelled: it answers a unifier, a clash, or "out of fuel". `UnifyingSound`
proves what a unifier it returns is. This module proves that with the fuel `unify` gives it
never runs out, on an idempotent substitution, whatever the two terms are.

The descent of `unifyTerms` goes into an expression once for each level, and the bindings
made on the way can deepen the terms it has still to visit: after `$x` is bound to
`(g (g a))`, a later `$x` is three levels deep. So the depth of the two terms at the start
is no bound. What is bounded is this. Let `S` be the subterms of the two resolved terms the
unification starts from. Throughout the run, every term that lies below a resolved member
of `S` is itself a resolved member of `S` (`Covers`): binding `$x` to `t` replaces `$x` in
every member at once, and what is new below a member then lies below `t`, which was a
resolved member already and does not contain `$x` (the occurs check). The terms the descent
is inside of, one for each level, are resolved members of `S` each properly below the one
before (`Chain`), hence distinct members. So the descent is never deeper than `S` is long,
and `S` is as long as the two resolved terms are large.

* `Below`, `subterms`, `length_subterms`: proper subterms; the list of a term's subterms is
  as long as the term is large.
* `below_single`: what lies below a term after one variable is replaced.
* `covers_bindVar`: binding a variable keeps `Covers`.
* `Chain.length_lt`: a chain inside `S` is shorter than `S`.
* `decides_aux`: the descent, with its chain; `unifyTerms_decides`, `unify_decides`.

Positive and negative examples: `Controls.deepened_by_a_binding_decides` (the second
argument is met three levels deeper than it is written, and the unifier still decides);
`Controls.short_of_fuel` (with fuel 2 the same unification runs out: the bound is used);
`Controls.cyclic_binding_runs_out` (with `$x` bound to `(g $x)`, which is not idempotent,
`unify` runs out on `$x` against `$x`: the hypothesis is used).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.Languages.ProcessCalculi

/-! ## Proper subterms -/

/-- `u` lies properly below `t`. -/
inductive Below : Atom → Atom → Prop
  | child {u : Atom} {items : List Atom} : u ∈ items → Below u (.expression items)
  | deeper {u v : Atom} {items : List Atom} : v ∈ items → Below u v →
      Below u (.expression items)

theorem Below.size {u t : Atom} (below : Below u t) : atomSize u < atomSize t := by
  induction below with
  | child member => exact atomSize_lt_of_mem member
  | deeper member _ ih => exact Nat.lt_trans ih (atomSize_lt_of_mem member)

theorem Below.trans {u v t : Atom} (first : Below u v) (second : Below v t) : Below u t := by
  induction second with
  | child member => exact .deeper member first
  | deeper member _ ih => exact .deeper member ih

theorem applySubstList_eq_map (σ : Subst) (items : List Atom) :
    applySubst.applySubstList σ items = items.map (applySubst σ) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [applySubst.applySubstList, ih]

theorem applySubst_expression (σ : Subst) (items : List Atom) :
    applySubst σ (.expression items) = .expression (items.map (applySubst σ)) := by
  simp [applySubst, applySubstList_eq_map]

/-- Substitution keeps "properly below". -/
theorem Below.subst (σ : Subst) {u t : Atom} (below : Below u t) :
    Below (applySubst σ u) (applySubst σ t) := by
  induction below with
  | child member =>
      rw [applySubst_expression]
      exact .child (List.mem_map_of_mem member)
  | deeper member _ ih =>
      rw [applySubst_expression]
      exact .deeper (List.mem_map_of_mem member) ih

theorem Below.freeVars {u t : Atom} (below : Below u t) :
    ∀ name ∈ atomFreeVars u, name ∈ atomFreeVars t := by
  induction below with
  | child member => exact fun name inItem => mem_freeVars_expression.mpr ⟨_, member, inItem⟩
  | deeper member _ ih =>
      exact fun name inItem => mem_freeVars_expression.mpr ⟨_, member, ih name inItem⟩

/-- Replacing a variable that does not occur changes nothing. -/
theorem applySubst_single_absent {name : String} {replacement term : Atom}
    (absent : name ∉ atomFreeVars term) : applySubst [(name, replacement)] term = term := by
  apply resolve_of_unbound
  intro other inTerm
  have different : other ≠ name := fun equal => absent (equal ▸ inTerm)
  simp [MORK.Subst.lookup, Ne.symm different]

/-- **What lies below a term after one variable is replaced** is the image of something
below the term, or lies below the replacement. -/
theorem below_single {name : String} {replacement : Atom} {u image : Atom}
    (below : Below u image) :
    ∀ t : Atom, applySubst [(name, replacement)] t = image →
      (∃ origin, Below origin t ∧ u = applySubst [(name, replacement)] origin) ∨
        Below u replacement := by
  induction below with
  | @child items member =>
      intro t same
      cases t with
      | var other =>
          by_cases bound : other = name
          · subst bound
            have replaced : replacement = .expression items := by
              simpa [applySubst, MORK.Subst.lookup] using same
            exact .inr (replaced ▸ .child member)
          · simp [applySubst, MORK.Subst.lookup, Ne.symm bound] at same
      | symbol _ => simp [applySubst] at same
      | grounded _ => simp [applySubst] at same
      | expression originals =>
          rw [applySubst_expression] at same
          cases same
          obtain ⟨origin, inOriginals, rfl⟩ := List.mem_map.mp member
          exact .inl ⟨origin, .child inOriginals, rfl⟩
  | @deeper v items member inner ih =>
      intro t same
      cases t with
      | var other =>
          by_cases bound : other = name
          · subst bound
            have replaced : replacement = .expression items := by
              simpa [applySubst, MORK.Subst.lookup] using same
            exact .inr (replaced ▸ .deeper member inner)
          · simp [applySubst, MORK.Subst.lookup, Ne.symm bound] at same
      | symbol _ => simp [applySubst] at same
      | grounded _ => simp [applySubst] at same
      | expression originals =>
          rw [applySubst_expression] at same
          cases same
          obtain ⟨item, inOriginals, rfl⟩ := List.mem_map.mp member
          rcases ih item rfl with ⟨origin, belowItem, rfl⟩ | inReplacement
          · exact .inl ⟨origin, .deeper inOriginals belowItem, rfl⟩
          · exact .inr inReplacement

/-! ## The subterms of a term, as a list -/

/-- Every subterm of a term, the term itself first. -/
def subterms : Atom → List Atom
  | .expression items => .expression items :: subtermsList items
  | term => [term]
where
  subtermsList : List Atom → List Atom
    | [] => []
    | first :: rest => subterms first ++ subtermsList rest

theorem length_subterms : ∀ term : Atom, (subterms term).length = atomSize term
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      simp only [subterms, List.length_cons, atomSize]
      congr 1
      exact list items
where
  list : ∀ items : List Atom, (subterms.subtermsList items).length = atomSize.listSize items
    | [] => rfl
    | first :: rest => by
        simp only [subterms.subtermsList, List.length_append, atomSize.listSize,
          length_subterms first, list rest]

theorem self_mem_subterms (term : Atom) : term ∈ subterms term := by
  cases term <;> simp [subterms]

theorem mem_subtermsList {u item : Atom} {items : List Atom} (member : item ∈ items)
    (inside : u ∈ subterms item) : u ∈ subterms.subtermsList items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      simp only [subterms.subtermsList, List.mem_append]
      rcases List.mem_cons.mp member with same | later
      · subst same; exact .inl inside
      · exact .inr (ih later)

theorem below_mem_subterms {u t : Atom} (below : Below u t) : u ∈ subterms t := by
  induction below with
  | child member =>
      simp only [subterms, List.mem_cons]
      exact .inr (mem_subtermsList member (self_mem_subterms _))
  | deeper member _ ih =>
      simp only [subterms, List.mem_cons]
      exact .inr (mem_subtermsList member ih)

theorem mem_subterms_cases : ∀ {t u : Atom}, u ∈ subterms t → u = t ∨ Below u t
  | .var _, u, member => by simp [subterms] at member; exact .inl member
  | .symbol _, u, member => by simp [subterms] at member; exact .inl member
  | .grounded _, u, member => by simp [subterms] at member; exact .inl member
  | .expression items, u, member => by
      simp only [subterms, List.mem_cons] at member
      rcases member with same | inside
      · exact .inl same
      · exact .inr (list items inside)
where
  list : ∀ (items : List Atom) {u : Atom}, u ∈ subterms.subtermsList items →
      Below u (.expression items)
    | [], _, inside => by cases inside
    | first :: rest, u, inside => by
        simp only [subterms.subtermsList, List.mem_append] at inside
        rcases inside with inFirst | inRest
        · rcases mem_subterms_cases inFirst with same | below
          · exact same ▸ .child List.mem_cons_self
          · exact .deeper List.mem_cons_self below
        · have later := list rest inRest
          cases later with
          | child member => exact .child (List.mem_cons_of_mem _ member)
          | deeper member below => exact .deeper (List.mem_cons_of_mem _ member) below

/-! ## What the bindings keep -/

/-- Every term that lies below a resolved member of `S` is a resolved member of `S`. -/
def Covers (bindings : Subst) (S : List Atom) : Prop :=
  ∀ s ∈ S, ∀ u, Below u (resolve bindings s) → ∃ s' ∈ S, resolve bindings s' = u

/-- **Binding a variable keeps the cover.** The variable is unbound, its value is a resolved
member and does not contain it. -/
theorem covers_bindVar {bindings : Subst} {S : List Atom} {name : String} {value : Atom}
    (covers : Covers bindings S) (free : bindings.lookup name = none)
    (member : ∃ s ∈ S, resolve bindings s = value) (absent : name ∉ atomFreeVars value) :
    Covers (bindVar bindings name value) S := by
  intro s inS u below
  rw [resolve_bindVar free] at below
  rcases below_single below (resolve bindings s) rfl with ⟨origin, belowOrigin, rfl⟩ | inValue
  · obtain ⟨s', inS', same⟩ := covers s inS origin belowOrigin
    exact ⟨s', inS', by rw [resolve_bindVar free, same]⟩
  · obtain ⟨holder, inHolder, held⟩ := member
    obtain ⟨s', inS', same⟩ := covers holder inHolder u (held ▸ inValue)
    refine ⟨s', inS', ?_⟩
    rw [resolve_bindVar free, same]
    exact applySubst_single_absent fun inU => absent (inValue.freeVars name inU)

/-! ## The terms the descent is inside of -/

/-- The members the descent is inside of, the innermost first: each resolved member lies
properly below the next, and the current member below the first. -/
def Chain (bindings : Subst) : List Atom → Atom → Prop
  | [], _ => True
  | outer :: older, s =>
      Below (resolve bindings s) (resolve bindings outer) ∧ Chain bindings older outer

theorem Chain.refine {earlier later : Subst} (refines : Refines earlier later) :
    ∀ {outers : List Atom} {s : Atom}, Chain earlier outers s → Chain later outers s
  | [], _, _ => trivial
  | outer :: older, s, ⟨below, rest⟩ => by
      refine ⟨?_, Chain.refine refines rest⟩
      have moved := below.subst later
      rwa [show applySubst later (resolve earlier s) = resolve later s from refines s,
        show applySubst later (resolve earlier outer) = resolve later outer from refines outer]
        at moved

theorem Chain.larger {bindings : Subst} : ∀ {outers : List Atom} {s : Atom},
    Chain bindings outers s → ∀ outer ∈ outers,
      atomSize (resolve bindings s) < atomSize (resolve bindings outer)
  | [], _, _, _, member => by cases member
  | first :: older, s, ⟨below, rest⟩, outer, member => by
      rcases List.mem_cons.mp member with same | later
      · subst same; exact below.size
      · exact Nat.lt_trans below.size (Chain.larger rest outer later)

theorem Chain.nodup {bindings : Subst} : ∀ {outers : List Atom} {s : Atom},
    Chain bindings outers s → (s :: outers).Nodup
  | [], _, _ => List.nodup_singleton _
  | first :: older, s, chain => by
      refine List.nodup_cons.mpr ⟨fun member => ?_, Chain.nodup chain.2⟩
      exact Nat.lt_irrefl _ (Chain.larger chain s member)

/-- **A chain inside `S` is shorter than `S`.** -/
theorem Chain.length_lt {bindings : Subst} {S outers : List Atom} {s : Atom}
    (chain : Chain bindings outers s) (inS : s ∈ S) (outersIn : ∀ outer ∈ outers, outer ∈ S) :
    outers.length < S.length := by
  have subset : s :: outers ⊆ S := by
    intro item member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ inS
    · exact outersIn item later
  have bound := (List.subperm_of_subset chain.nodup subset).length_le
  simp only [List.length_cons] at bound
  omega

/-! ## The descent -/

/-- `unifyTerms` sees only the resolved terms. -/
theorem unifyTerms_congr (fuel : Nat) (bindings : Subst) {left left' right right' : Atom}
    (sameLeft : resolve bindings left = resolve bindings left')
    (sameRight : resolve bindings right = resolve bindings right') :
    unifyTerms fuel bindings left right = unifyTerms fuel bindings left' right' := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [unifyTerms, sameLeft, sameRight]

/-- **The descent with its chain.** Inside the members `outers`, with fuel for the members
of `S` not yet entered, `unifyTerms` does not run out, and a unifier it returns keeps the
cover. -/
theorem decides_aux (S : List Atom) :
    ∀ (fuel : Nat) (bindings : Subst) (sl sr : Atom) (outers : List Atom),
      Idempotent bindings → Covers bindings S → sl ∈ S → sr ∈ S →
      (∀ outer ∈ outers, outer ∈ S) → Chain bindings outers sl →
      S.length ≤ fuel + outers.length →
      unifyTerms fuel bindings sl sr ≠ .exhausted ∧
        ∀ bound, unifyTerms fuel bindings sl sr = .ok bound → Covers bound S := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindings sl sr outers _ _ inLeft _ outersIn chain enough
      have short := chain.length_lt inLeft outersIn
      omega
  | succ fuel ih =>
      intro bindings sl sr outers idempotent covers inLeft inRight outersIn chain enough
      have key : ∀ outcome, unifyTerms (fuel + 1) bindings sl sr = outcome →
          outcome ≠ .exhausted ∧ ∀ bound, outcome = .ok bound → Covers bound S := by
        intro outcome unified
        -- binding the resolved variable of one side to the resolved other side
        have coverLeft : ∀ (name : String) (term : Atom), resolve bindings sl = .var name →
            resolve bindings sr = term → name ∉ atomFreeVars term →
            Covers (bindVar bindings name term) S := by
          intro name term leftVar rightTerm absent
          exact covers_bindVar covers
            (unbound_resolve idempotent sl name (by rw [leftVar]; simp [MORK.atomFreeVars]))
            ⟨sr, inRight, rightTerm⟩ absent
        have coverRight : ∀ (name : String) (term : Atom), resolve bindings sr = .var name →
            resolve bindings sl = term → name ∉ atomFreeVars term →
            Covers (bindVar bindings name term) S := by
          intro name term rightVar leftTerm absent
          exact covers_bindVar covers
            (unbound_resolve idempotent sr name (by rw [rightVar]; simp [MORK.atomFreeVars]))
            ⟨sl, inLeft, leftTerm⟩ absent
        have lists : ∀ (leftItems rightItems : List Atom),
            resolve bindings sl = .expression leftItems →
            resolve bindings sr = .expression rightItems →
            ∀ (items others : List Atom) (current : Subst), Idempotent current →
              Refines bindings current → Covers current S →
              (∀ item ∈ items, item ∈ leftItems) → (∀ other ∈ others, other ∈ rightItems) →
              unifyLists (unifyTerms fuel) current items others ≠ .exhausted ∧
                ∀ bound, unifyLists (unifyTerms fuel) current items others = .ok bound →
                  Covers bound S := by
          intro leftItems rightItems leftShape rightShape items
          induction items with
          | nil =>
              intro others current _ _ currentCovers _ _
              cases others with
              | nil =>
                  refine ⟨by simp [unifyLists], fun bound same => ?_⟩
                  simp only [unifyLists, Unified.ok.injEq] at same
                  exact same ▸ currentCovers
              | cons _ _ => exact ⟨by simp [unifyLists], fun bound same => by simp [unifyLists] at same⟩
          | cons first rest restIh =>
              intro others current currentIdempotent currentRefines currentCovers itemsIn othersIn
              cases others with
              | nil => exact ⟨by simp [unifyLists], fun bound same => by simp [unifyLists] at same⟩
              | cons other remaining =>
                  -- the members the two items are resolved forms of
                  obtain ⟨sf, inSf, isFirst⟩ := covers sl inLeft first
                    (leftShape ▸ .child (itemsIn first List.mem_cons_self))
                  obtain ⟨so, inSo, isOther⟩ := covers sr inRight other
                    (rightShape ▸ .child (othersIn other List.mem_cons_self))
                  have firstNow : resolve current first = resolve current sf := by
                    rw [← isFirst]; exact currentRefines sf
                  have otherNow : resolve current other = resolve current so := by
                    rw [← isOther]; exact currentRefines so
                  have inside : Chain current (sl :: outers) sf := by
                    refine ⟨?_, chain.refine currentRefines⟩
                    have below : Below first (.expression leftItems) :=
                      .child (itemsIn first List.mem_cons_self)
                    have moved := below.subst current
                    rwa [show applySubst current first = resolve current sf from firstNow,
                      show applySubst current (.expression leftItems) = resolve current sl from by
                        rw [← leftShape]; exact currentRefines sl] at moved
                  obtain ⟨decides, keeps⟩ := ih current sf so (sl :: outers) currentIdempotent
                    currentCovers inSf inSo
                    (fun outer member => by
                      rcases List.mem_cons.mp member with same | later
                      · exact same ▸ inLeft
                      · exact outersIn outer later)
                    inside (by simp only [List.length_cons]; omega)
                  rw [← unifyTerms_congr fuel current firstNow otherNow] at decides keeps
                  simp only [unifyLists]
                  cases step : unifyTerms fuel current first other with
                  | clash => exact ⟨by simp, fun bound same => by simp at same⟩
                  | exhausted => exact absurd step decides
                  | ok middle =>
                      simp only [Unified.ok_andThen]
                      obtain ⟨middleIdempotent, middleRefines, _⟩ :=
                        unifyTerms_sound fuel current middle first other currentIdempotent step
                      exact restIh remaining middle middleIdempotent
                        (currentRefines.trans middleRefines) (keeps middle step)
                        (fun item member => itemsIn item (List.mem_cons_of_mem _ member))
                        (fun item member => othersIn item (List.mem_cons_of_mem _ member))
        unfold unifyTerms at unified
        generalize leftEq : resolve bindings sl = resolvedLeft at unified
        generalize rightEq : resolve bindings sr = resolvedRight at unified
        cases resolvedLeft with
        | var name =>
            cases resolvedRight with
            | var other =>
                simp only at unified
                subst unified
                by_cases same : name = other
                · simp only [same, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true,
                    Unified.ok.injEq, true_and]
                  exact fun bound equal => equal ▸ covers
                · simp only [same, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true,
                    Unified.ok.injEq, true_and]
                  exact fun bound equal => equal ▸
                    coverLeft name (.var other) leftEq rightEq
                      (by simpa [MORK.atomFreeVars] using same)
            | symbol _ | grounded _ | expression _ =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by simp at same⟩
                · rename_i notIn
                  refine ⟨by simp, fun bound same => ?_⟩
                  simp only [Unified.ok.injEq] at same
                  exact same ▸ coverLeft name _ leftEq rightEq (by simpa [occurs] using notIn)
        | symbol name =>
            cases resolvedRight with
            | var other =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by simp at same⟩
                · rename_i notIn
                  refine ⟨by simp, fun bound same => ?_⟩
                  simp only [Unified.ok.injEq] at same
                  exact same ▸ coverRight other _ rightEq leftEq (by simpa [occurs] using notIn)
            | symbol other =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by
                    simp only [Unified.ok.injEq] at same; exact same ▸ covers⟩
                · exact ⟨by simp, fun bound same => by simp at same⟩
            | grounded _ | expression _ =>
                simp only at unified
                subst unified
                exact ⟨by simp, fun bound same => by simp at same⟩
        | grounded value =>
            cases resolvedRight with
            | var other =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by simp at same⟩
                · rename_i notIn
                  refine ⟨by simp, fun bound same => ?_⟩
                  simp only [Unified.ok.injEq] at same
                  exact same ▸ coverRight other _ rightEq leftEq (by simpa [occurs] using notIn)
            | grounded other =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by
                    simp only [Unified.ok.injEq] at same; exact same ▸ covers⟩
                · exact ⟨by simp, fun bound same => by simp at same⟩
            | symbol _ | expression _ =>
                simp only at unified
                subst unified
                exact ⟨by simp, fun bound same => by simp at same⟩
        | expression items =>
            cases resolvedRight with
            | var other =>
                simp only at unified
                subst unified
                split
                · exact ⟨by simp, fun bound same => by simp at same⟩
                · rename_i notIn
                  refine ⟨by simp, fun bound same => ?_⟩
                  simp only [Unified.ok.injEq] at same
                  exact same ▸ coverRight other _ rightEq leftEq (by simpa [occurs] using notIn)
            | expression others =>
                simp only at unified
                subst unified
                exact lists items others leftEq rightEq items others bindings idempotent
                  (Refines.refl idempotent) covers (fun _ member => member) (fun _ member => member)
            | symbol _ | grounded _ =>
                simp only at unified
                subst unified
                exact ⟨by simp, fun bound same => by simp at same⟩
      exact key _ rfl

/-! ## The theorems -/

/-- **At the start the subterms of the two resolved terms cover themselves**: each is its
own resolved form, and what lies below one is another. -/
theorem covers_subterms {bindings : Subst} (idempotent : Idempotent bindings) (left right : Atom) :
    Covers bindings (subterms (resolve bindings left) ++ subterms (resolve bindings right)) := by
  have settled : ∀ s ∈ subterms (resolve bindings left) ++ subterms (resolve bindings right),
      resolve bindings s = s := by
    intro s member
    apply resolve_of_unbound
    intro name inS
    rcases List.mem_append.mp member with inLeft | inRight
    · rcases mem_subterms_cases inLeft with same | below
      · exact unbound_resolve idempotent left name (same ▸ inS)
      · exact unbound_resolve idempotent left name (below.freeVars name inS)
    · rcases mem_subterms_cases inRight with same | below
      · exact unbound_resolve idempotent right name (same ▸ inS)
      · exact unbound_resolve idempotent right name (below.freeVars name inS)
  intro s member u below
  rw [settled s member] at below
  have inS : u ∈ subterms (resolve bindings left) ++ subterms (resolve bindings right) := by
    rcases List.mem_append.mp member with inLeft | inRight
    · rcases mem_subterms_cases inLeft with same | deeper
      · exact List.mem_append_left _ (below_mem_subterms (same ▸ below))
      · exact List.mem_append_left _ (below_mem_subterms (below.trans deeper))
    · rcases mem_subterms_cases inRight with same | deeper
      · exact List.mem_append_right _ (below_mem_subterms (same ▸ below))
      · exact List.mem_append_right _ (below_mem_subterms (below.trans deeper))
  exact ⟨u, inS, settled u inS⟩

/-- **The unifier decides.** On an idempotent substitution, with fuel for the sizes of the
two resolved terms, `unifyTerms` answers a unifier or a clash. -/
theorem unifyTerms_decides (fuel : Nat) (bindings : Subst) (left right : Atom)
    (idempotent : Idempotent bindings)
    (enough : atomSize (resolve bindings left) + atomSize (resolve bindings right) ≤ fuel) :
    unifyTerms fuel bindings left right ≠ .exhausted := by
  let S := subterms (resolve bindings left) ++ subterms (resolve bindings right)
  have covers : Covers bindings S := covers_subterms idempotent left right
  have atRoot := (decides_aux S fuel bindings (resolve bindings left) (resolve bindings right) []
    idempotent covers (List.mem_append_left _ (self_mem_subterms _))
    (List.mem_append_right _ (self_mem_subterms _)) (fun _ member => by cases member) trivial
    (by simp only [S, List.length_append, length_subterms, List.length_nil]; omega)).1
  rwa [unifyTerms_congr fuel bindings (resolve_idem idempotent left)
    (resolve_idem idempotent right)] at atRoot

/-- **`unify` never runs out of fuel** on an idempotent substitution. -/
theorem unify_decides (bindings : Subst) (left right : Atom) (idempotent : Idempotent bindings) :
    unify bindings left right ≠ .exhausted := by
  unfold unify
  exact unifyTerms_decides _ bindings left right idempotent (by unfold fuelFor; omega)

namespace Controls

/-- `(f $x (h $x))` and `(f (g (g a)) (h (g (g b))))`: after `$x` is bound, the second
argument on the left is three levels deep, where it is written two deep. -/
def deepened : Atom × Atom :=
  (.expression [.symbol "f", .var "x", .expression [.symbol "h", .var "x"]],
   .expression [.symbol "f", .expression [.symbol "g", .expression [.symbol "g", .symbol "a"]],
     .expression [.symbol "h",
       .expression [.symbol "g", .expression [.symbol "g", .symbol "b"]]]])

/-- Positive: the unifier decides it (a clash, `a` against `b`, four levels down). -/
theorem deepened_by_a_binding_decides : unify [] deepened.1 deepened.2 = .clash := by
  decide +kernel

/-- Negative: with fuel 2 the same unification runs out, so the bound on fuel is used. -/
theorem short_of_fuel : unifyTerms 2 [] deepened.1 deepened.2 = .exhausted := by
  decide +kernel

/-- `$x` bound to `(g $x)`: resolving `$x` gives a term that holds `$x` again. -/
def cyclic : Subst := [("x", .expression [.symbol "g", .var "x"])]

/-- Negative: the cyclic binding is not idempotent, and on it `unify` runs out of fuel on
`$x` against `$x`, so `unify_decides` needs its hypothesis. -/
theorem cyclic_binding_runs_out :
    ¬ Idempotent cyclic ∧ unify cyclic (.var "x") (.var "x") = .exhausted := by
  refine ⟨fun idempotent => ?_, by decide +kernel⟩
  have unbound := idempotent "x" (.expression [.symbol "g", .var "x"]) (by decide) "x"
    (by decide)
  exact absurd unbound (by decide)

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
