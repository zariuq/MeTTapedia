import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Clauses

/-!
# Scope and sites of the code a clause makes

For the elaboration under a clause (`elabH`):

* **Names** (`NamesWithinH`, `hview_within`, `hview_coherent`): the elements a reading keeps of a tuple
  name only names of that tuple.
* **Scope from the names** (`elabH_scoped`): when every name of the text is unopened and of an allowed
  site, the code is lexically scoped from those sites, for a clause that passes as text only what an
  argument holds or is (`Clause.Faithful`).
* **Scope from the elaboration's** (`elabH_scoped_of`): the code under such a clause is scoped whenever
  the code of `Elaboration.elabText` is, on the readings of text.
* **Sites** (`elabH_sites`, `elabH_nodup`): every binder site of the code extends the path, and no two
  binders of the code share a site.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-! ## Names of readings -/

/-- Every name of the reading's text, and of the texts it is made of, satisfies `A`. -/
def NamesWithinH (A : Name mkeys → Prop) : HView → Prop
  | .holdMark o u => (∀ x ∈ support o, A x) ∧ ∀ x ∈ support u, A x
  | .runMark o inner => (∀ x ∈ support o, A x) ∧ NamesWithinH A inner
  | .var o _ => ∀ x ∈ support o, A x
  | .symbol o _ => ∀ x ∈ support o, A x
  | .call o _ args => (∀ x ∈ support o, A x) ∧ NamesWithinArgsH A args
  | .inert o => ∀ x ∈ support o, A x
  | .other o elements => (∀ x ∈ support o, A x) ∧ NamesWithinArgsH A elements
where
  /-- Every element is so. -/
  NamesWithinArgsH (A : Name mkeys → Prop) : List HView → Prop
    | [] => True
    | a :: rest => NamesWithinH A a ∧ NamesWithinArgsH A rest

theorem NamesWithinH.orig {A : Name mkeys → Prop} : ∀ {v : HView}, NamesWithinH A v → ∀ x ∈ support v.orig, A x
  | .holdMark _ _, within => within.1
  | .runMark _ _, within => within.1
  | .var _ _, within => within
  | .symbol _ _, within => within
  | .call _ _ _, within => within.1
  | .inert _, within => within
  | .other _ _, within => within.1

mutual
theorem NamesWithinH.mono {A B : Name mkeys → Prop} (more : ∀ x, A x → B x) :
    ∀ v : HView, NamesWithinH A v → NamesWithinH B v
  | .holdMark _ _, ⟨ho, hu⟩ => ⟨fun x hx => more x (ho x hx), fun x hx => more x (hu x hx)⟩
  | .runMark _ inner, ⟨ho, hi⟩ => ⟨fun x hx => more x (ho x hx), NamesWithinH.mono more inner hi⟩
  | .var _ _, ho => fun x hx => more x (ho x hx)
  | .symbol _ _, ho => fun x hx => more x (ho x hx)
  | .call _ _ args, ⟨ho, ha⟩ => ⟨fun x hx => more x (ho x hx), NamesWithinArgsH.mono more args ha⟩
  | .inert _, ho => fun x hx => more x (ho x hx)
  | .other _ elements, ⟨ho, ha⟩ => ⟨fun x hx => more x (ho x hx), NamesWithinArgsH.mono more elements ha⟩

theorem NamesWithinArgsH.mono {A B : Name mkeys → Prop} (more : ∀ x, A x → B x) :
    ∀ args : List HView, NamesWithinH.NamesWithinArgsH A args → NamesWithinH.NamesWithinArgsH B args
  | [], _ => trivial
  | a :: rest, ⟨ha, hr⟩ => ⟨NamesWithinH.mono more a ha, NamesWithinArgsH.mono more rest hr⟩
end

mutual
/-- **A reading's names are its text's names.** -/
theorem hviewAt_within : ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []),
    NamesWithinH (· ∈ support t) (hviewAt t h)
  | _, (), .op (.inl .hold) (.cons u .nil), h => by
      rw [hviewAt_hold]
      refine ⟨ElaborationHygiene.atTop_names h _, fun x hx => ?_⟩
      rw [ElaborationHygiene.support_atTop] at hx
      simp [support, supportArgs, hx]
  | _, (), .op (.inl .run) (.cons u .nil), h => by
      rw [hviewAt_run]
      refine ⟨ElaborationHygiene.atTop_names h _, ?_⟩
      exact NamesWithinH.mono (fun x hx => by simp [support, supportArgs, hx]) _
        (hviewAt_within u ((List.nil_append _).trans h))
  | _, (), .op (.inl (.tup n)) args, h => by
      rw [hviewAt_tup]
      have inside := hviewArgsAt_within args h
      split
      · rename_i f rest same
        rw [same] at inside
        refine ⟨ElaborationHygiene.atTop_names h _, ?_⟩
        exact NamesWithinArgsH.mono (fun x hx => by simpa [support] using hx) _ inside.2
      · refine ⟨ElaborationHygiene.atTop_names h _, ?_⟩
        exact NamesWithinArgsH.mono (fun x hx => by simpa [support] using hx) _ inside
  | _, (), .op (.inl (.sym f)) args, h => by
      rw [hviewAt_sym]
      exact ElaborationHygiene.atTop_names h _
  | _, (), .op (.inl (.num k)) args, h => by
      rw [hviewAt_num]
      exact ElaborationHygiene.atTop_names h _
  | _, (), .op (.inl .lam) args, h => by
      rw [hviewAt_lam]
      exact ElaborationHygiene.atTop_names h _
  | _, (), .op (.inr (.mk x)) args, h => by
      rw [hviewAt_name]
      exact ElaborationHygiene.atTop_names h _
  | _, (), .var v, h => by
      rw [hviewAt_var]
      exact ElaborationHygiene.atTop_names h _

theorem hviewArgsAt_within : ∀ {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []),
    NamesWithinH.NamesWithinArgsH (· ∈ supportArgs args) (hviewArgsAt args h)
  | _, _, .nil, h => by rw [hviewArgsAt_nil]; trivial
  | _, _, .cons (bs := bs) (s := ()) hd tl, h => by
      rw [hviewArgsAt_cons]
      split
      · rename_i hb
        refine ⟨NamesWithinH.mono (fun x hx => by simp [supportArgs, hx]) _ (hviewAt_within hd _), ?_⟩
        exact NamesWithinArgsH.mono (fun x hx => by simp [supportArgs, hx]) _ (hviewArgsAt_within tl h)
      · exact NamesWithinArgsH.mono (fun x hx => by simp [supportArgs, hx]) _ (hviewArgsAt_within tl h)
end

/-- The names of `hview t` are the names of `t`. -/
theorem hview_within (t : MData) : NamesWithinH (· ∈ support t) (hview t) := hviewAt_within t rfl

/-- **The kept elements name only names of their tuple**, at every tuple the reading reaches. -/
def Coherent : HView → Prop
  | .runMark _ inner => Coherent inner
  | .call _ _ args => CoherentArgs args
  | .other o elements => NamesWithinH.NamesWithinArgsH (· ∈ support o) elements
  | _ => True
where
  /-- Every argument is so. -/
  CoherentArgs : List HView → Prop
    | [] => True
    | a :: rest => Coherent a ∧ CoherentArgs rest

mutual
theorem hviewAt_coherent : ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []),
    Coherent (hviewAt t h)
  | _, (), .op (.inl .hold) (.cons u .nil), h => by rw [hviewAt_hold]; trivial
  | _, (), .op (.inl .run) (.cons u .nil), h => by
      rw [hviewAt_run]
      exact hviewAt_coherent u ((List.nil_append _).trans h)
  | _, (), .op (.inl (.tup n)) args, h => by
      rw [hviewAt_tup]
      have inside := hviewArgsAt_coherent args h
      have names := hviewArgsAt_within args h
      split
      · rename_i f rest same
        rw [same] at inside
        exact inside.2
      · exact NamesWithinArgsH.mono
          (fun x hx => by rw [ElaborationHygiene.support_atTop]; simpa [support] using hx) _ names
  | _, (), .op (.inl (.sym f)) args, h => by rw [hviewAt_sym]; trivial
  | _, (), .op (.inl (.num k)) args, h => by rw [hviewAt_num]; trivial
  | _, (), .op (.inl .lam) args, h => by rw [hviewAt_lam]; trivial
  | _, (), .op (.inr (.mk x)) args, h => by rw [hviewAt_name]; trivial
  | _, (), .var v, h => by rw [hviewAt_var]; trivial

theorem hviewArgsAt_coherent : ∀ {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []),
    Coherent.CoherentArgs (hviewArgsAt args h)
  | _, _, .nil, h => by rw [hviewArgsAt_nil]; trivial
  | _, _, .cons (bs := bs) (s := ()) hd tl, h => by
      rw [hviewArgsAt_cons]
      split
      · exact ⟨hviewAt_coherent hd _, hviewArgsAt_coherent tl h⟩
      · exact hviewArgsAt_coherent tl h
end

theorem hview_coherent (t : MData) : Coherent (hview t) := hviewAt_coherent t rfl

/-! ## Scope from the names -/

/-- A clause that passes as text only what an argument holds or is. -/
def Clause.Faithful : Clause → Prop
  | .static pass => ∀ head i a u, pass head i a = .text u → (∃ o, a = .holdMark o u) ∨ u = a.orig
  | _ => True

theorem byValue_faithful : Clause.byValue.Faithful := by
  intro head i a u passed
  cases a with
  | holdMark o inside =>
      simp only [passByValue, Pass.text.injEq] at passed
      exact .inl ⟨o, by rw [passed]⟩
  | runMark o inner => simp [passByValue] at passed
  | var o x => simp [passByValue] at passed
  | symbol o f => simp [passByValue] at passed
  | call o f args => simp [passByValue] at passed
  | inert o => simp [passByValue] at passed
  | other o elements => simp [passByValue] at passed

/-- A name is unopened and of an allowed site. -/
abbrev Within (allowed : List (List ℕ)) (x : Name mkeys) : Prop := x.scopes = [] ∧ x.key.site ∈ allowed

theorem namesIn_slot (s : List ℕ) (allowed : List (List ℕ)) (inside : s ∈ allowed) :
    NamesIn (κ := mkeys) allowed (slot s) := by
  intro x hx
  simp only [slot, mvar, support, supportArgs, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, inside⟩

theorem namesIn_mono {allowed allowed' : List (List ℕ)} (more : allowed ⊆ allowed') {t : MData}
    (names : NamesIn (κ := mkeys) allowed t) : NamesIn (κ := mkeys) allowed' t :=
  fun x hx => ⟨(names x hx).1, more (names x hx).2⟩

theorem namesIn_tuple {allowed : List (List ℕ)} {ts : List MData}
    (names : ∀ d ∈ ts, NamesIn (κ := mkeys) allowed d) : NamesIn (κ := mkeys) allowed (tuple ts) := by
  intro x hx
  obtain ⟨d, inside, hd⟩ := ElaborationHygiene.support_tuple ts x hx
  exact names d inside x hd

theorem namesIn_sym (allowed : List (List ℕ)) (f : String) : NamesIn (κ := mkeys) allowed (sym f) := by
  intro x hx
  simp [sym, support, supportArgs] at hx

variable (cl : Clause) (π : Params) (decls : List Decl)

theorem finish_scoped (f : String) (allowed : List (List ℕ)) (done : List MData)
    (names : ∀ d ∈ done, NamesIn (κ := mkeys) allowed d) : (finish decls f done).Scoped allowed := by
  have call : NamesIn (κ := mkeys) allowed (tuple (sym f :: done)) := namesIn_tuple fun d inside => by
    rcases List.mem_cons.mp inside with rfl | old
    · exact namesIn_sym allowed f
    · exact names d old
  simp only [finish]
  split
  · split <;> exact call
  · exact call

/-- What a faithful passing of `passOf` gives, on readings. -/
theorem passOf_faithful (f : String) (i : ℕ) (a : HView) (u : MData)
    (passed : passOf π decls f i a.forget = .text u) : (∃ o, a = .holdMark o u) ∨ u = a.orig := by
  rcases ElaborationHygiene.passOf_text π decls f i a.forget u passed with ⟨o, same⟩ | same
  · cases a with
    | holdMark o' inside =>
        simp only [HView.forget, View.holdMark.injEq] at same
        exact .inl ⟨o', by rw [same.2]⟩
    | runMark o' inner => simp [HView.forget] at same
    | var o' x => simp [HView.forget] at same
    | symbol o' g => simp [HView.forget] at same
    | call o' g args => simp [HView.forget] at same
    | inert o' => simp [HView.forget] at same
    | other o' elements => simp [HView.forget] at same
  · exact .inr (same.trans (HView.forget_orig a))

theorem headDatum_within {A : Name mkeys → Prop} (modes : Name mkeys → VarMode) :
    ∀ (head : HView) (d : MData), headDatum modes head = some d → NamesWithinH A head → ∀ x ∈ support d, A x
  | .var o y, d, datum, within => by
      simp only [headDatum] at datum
      split at datum
      · cases datum
        exact within
      · cases datum
  | .holdMark _ u, d, datum, within => by
      cases datum
      exact within.2
  | .inert o, d, datum, within => by
      cases datum
      exact within
  | .symbol o _, d, datum, within => by
      cases datum
      exact within
  | .runMark _ _, d, datum, _ => by simp [headDatum] at datum
  | .call _ _ _, d, datum, _ => by simp [headDatum] at datum
  | .other _ _, d, datum, _ => by simp [headDatum] at datum

mutual
/-- **Scope from the names**: when every name of the text is unopened and of an allowed site, the code is
lexically scoped from those sites. -/
theorem elabH_scoped (faithful : cl.Faithful) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (v : HView) (allowed : List (List ℕ)), NamesWithinH (Within allowed) v →
      (elabH cl π decls modes path v).Scoped allowed
  | .holdMark _ _, _, within => within.2
  | .runMark _ inner, allowed, within => by
      cases inner with
      | var o' y => exact within.2
      | holdMark o' u => exact elabH_scoped faithful modes path (.holdMark o' u) allowed within.2
      | runMark o' i => exact elabH_scoped faithful modes path (.runMark o' i) allowed within.2
      | symbol o' g => exact elabH_scoped faithful modes path (.symbol o' g) allowed within.2
      | call o' g args => exact elabH_scoped faithful modes path (.call o' g args) allowed within.2
      | inert o' => exact elabH_scoped faithful modes path (.inert o') allowed within.2
      | other o' elements => exact elabH_scoped faithful modes path (.other o' elements) allowed within.2
  | .var o x, allowed, within => by
      simp only [elabH, varAt]
      split
      · exact within
      · split <;> exact within
      · exact within
      · exact within
  | .symbol _ _, _, within => within
  | .call _ f args, allowed, within => by
      simp only [elabH]
      exact elabArgsH_scoped faithful _ (passOf_faithful π decls f) _ allowed
        (fun allowed' done _ names => finish_scoped decls f allowed' done names) modes path 0 args []
        allowed (fun _ inside => inside) within.2 (fun _ none => nomatch none)
  | .inert _, _, within => within
  | .other _ [], _, within => within.1
  | .other o (head :: args), allowed, within => by
      have atHead := elabH_scoped faithful modes (path ++ [args.length]) head allowed within.2.1
      have atArgs := fun (pass : ℕ → HView → Pass)
          (passFaithful : ∀ i a u, pass i a = .text u → (∃ o, a = .holdMark o u) ∨ u = a.orig)
          (fin : List MData → Comp mkeys [] () MTy) (base : List (List ℕ))
          (finScoped : ∀ allowed' done, base ⊆ allowed' → (∀ d ∈ done, NamesIn (κ := mkeys) allowed' d) →
            (fin done).Scoped allowed')
          (allowed' : List (List ℕ)) (more : base ⊆ allowed')
          (inside : NamesWithinH.NamesWithinArgsH (Within allowed') args) =>
        elabArgsH_scoped faithful pass passFaithful fin base finScoped modes path 0 args [] allowed' more inside
          (fun _ none => nomatch none)
      cases cl with
      | asWritten => exact within.1
      | atRunTime => exact within.1
      | static pass =>
          have passFaithful : ∀ i a u, pass head i a = .text u → (∃ o, a = .holdMark o u) ∨ u = a.orig :=
            fun i a u => faithful head i a u
          simp only [elabH]
          split
          · rename_i d datum
            have dNames : NamesIn (κ := mkeys) allowed d := headDatum_within modes head d datum within.2.1
            refine atArgs (pass head) passFaithful _ allowed (fun allowed' done more names => ?_) allowed
              (fun _ inside => inside) within.2.2
            exact namesIn_tuple fun e inside => by
              rcases List.mem_cons.mp inside with rfl | old
              · exact namesIn_mono more dNames
              · exact names e old
          · refine ⟨atHead, namesIn_slot _ _ List.mem_cons_self, ?_⟩
            refine atArgs (pass head) passFaithful _ ((path ++ [args.length]) :: allowed)
              (fun allowed' done more names => ?_) ((path ++ [args.length]) :: allowed) (fun _ inside => inside)
              (NamesWithinArgsH.mono (fun x hx => ⟨hx.1, List.mem_cons_of_mem _ hx.2⟩) args within.2.2)
            exact namesIn_tuple fun e inside => by
              rcases List.mem_cons.mp inside with rfl | old
              · exact namesIn_slot _ _ (more List.mem_cons_self)
              · exact names e old

theorem elabArgsH_scoped (faithful : cl.Faithful) (pass : ℕ → HView → Pass)
    (passFaithful : ∀ i a u, pass i a = .text u → (∃ o, a = .holdMark o u) ∨ u = a.orig)
    (fin : List MData → Comp mkeys [] () MTy) (base : List (List ℕ))
    (finScoped : ∀ allowed done, base ⊆ allowed → (∀ d ∈ done, NamesIn (κ := mkeys) allowed d) →
      (fin done).Scoped allowed)
    (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (i : ℕ) (args : List HView) (done : List MData) (allowed : List (List ℕ)), base ⊆ allowed →
      NamesWithinH.NamesWithinArgsH (Within allowed) args → (∀ d ∈ done, NamesIn (κ := mkeys) allowed d) →
      (elabArgsH cl π decls pass fin modes path i args done).Scoped allowed
  | _, [], done, allowed, more, _, names => by
      simp only [elabArgsH]
      exact finScoped allowed _ more fun d inside => names d (List.mem_reverse.mp inside)
  | i, a :: rest, done, allowed, more, ⟨first, others⟩, names => by
      have slotNames : ∀ d ∈ slot (path ++ [i]) :: done, NamesIn (κ := mkeys) ((path ++ [i]) :: allowed) d := by
        intro d inside
        rcases List.mem_cons.mp inside with rfl | old
        · exact namesIn_slot _ _ List.mem_cons_self
        · exact namesIn_mono (List.subset_cons_self _ _) (names d old)
      have later := elabArgsH_scoped faithful pass passFaithful fin base finScoped modes path (i + 1) rest
        (slot (path ++ [i]) :: done) ((path ++ [i]) :: allowed)
        (fun s inside => List.mem_cons_of_mem _ (more inside))
        (NamesWithinArgsH.mono (fun x hx => ⟨hx.1, List.mem_cons_of_mem _ hx.2⟩) rest others) slotNames
      have here := elabH_scoped faithful modes (path ++ [i]) a allowed first
      cases passed : pass i a with
      | text u =>
          simp only [elabArgsH, passed]
          refine elabArgsH_scoped faithful pass passFaithful fin base finScoped modes path (i + 1) rest
            (u :: done) allowed more others fun d inside => ?_
          rcases List.mem_cons.mp inside with rfl | old
          · rcases passFaithful i a d passed with ⟨o, rfl⟩ | rfl
            · exact first.2
            · exact first.orig
          · exact names d old
      | byName =>
          simp only [elabArgsH, passed]
          refine elabArgsH_scoped faithful pass passFaithful fin base finScoped modes path (i + 1) rest
            (a.orig :: done) allowed more others fun d inside => ?_
          rcases List.mem_cons.mp inside with rfl | old
          · exact first.orig
          · exact names d old
      | evaluate check =>
          cases check with
          | none =>
              simp only [elabArgsH, passed]
              exact ⟨here, namesIn_slot _ _ List.mem_cons_self, later⟩
          | some T =>
              simp only [elabArgsH, passed]
              exact ⟨here, namesIn_slot _ _ List.mem_cons_self, later⟩
      | byNeed =>
          simp only [elabArgsH, passed]
          exact ⟨here, namesIn_slot _ _ List.mem_cons_self, later⟩
end

/-! ## Scope from the elaboration's -/

mutual
/-- **The code under the clause is scoped whenever the elaboration's is**, on readings whose kept elements
name only names of their tuples (those of text: `hview_coherent`). -/
theorem elabH_scoped_of (faithful : cl.Faithful) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (v : HView) (allowed : List (List ℕ)), Coherent v →
      (elabText π decls modes path v.forget).Scoped allowed → (elabH cl π decls modes path v).Scoped allowed
  | .holdMark _ _, _, _, present => present
  | .runMark _ inner, allowed, coherent, present => by
      cases inner with
      | var o' y => exact present
      | holdMark o' u => exact present
      | runMark o' i => exact elabH_scoped_of faithful modes path (.runMark o' i) allowed coherent present
      | symbol o' g => exact present
      | call o' g args => exact elabH_scoped_of faithful modes path (.call o' g args) allowed coherent present
      | inert o' => exact present
      | other o' elements =>
          exact elabH_scoped_of faithful modes path (.other o' elements) allowed coherent present
  | .var _ _, _, _, present => present
  | .symbol _ _, _, _, present => present
  | .call _ f args, allowed, coherent, present => by
      simp only [HView.forget, elabText] at present
      simp only [elabH]
      exact elabArgsH_scoped_of faithful modes path f 0 args [] allowed coherent present
  | .inert _, _, _, present => present
  | .other _ [], _, _, present => present
  | .other o (head :: args), allowed, coherent, present => by
      have names : NamesIn (κ := mkeys) allowed o := present
      have inside : NamesWithinH.NamesWithinArgsH (· ∈ support o) (head :: args) := coherent
      exact elabH_scoped cl π decls faithful modes path (.other o (head :: args)) allowed
        ⟨names, NamesWithinArgsH.mono (fun x hx => names x hx) _ inside⟩

theorem elabArgsH_scoped_of (faithful : cl.Faithful) (modes : Name mkeys → VarMode) (path : List ℕ)
    (f : String) :
    ∀ (i : ℕ) (args : List HView) (done : List MData) (allowed : List (List ℕ)),
      Coherent.CoherentArgs args →
      (elabArgs π decls modes path f i (HView.forget.forgetAll args) done).Scoped allowed →
      (elabArgsH cl π decls (fun i a => passOf π decls f i a.forget) (finish decls f) modes path i args
        done).Scoped allowed
  | _, [], _, _, _, present => present
  | i, a :: rest, done, allowed, ⟨first, others⟩, present => by
      cases passed : passOf π decls f i a.forget with
      | text u =>
          simp only [HView.forget.forgetAll, elabArgs, passed] at present
          simp only [elabArgsH, passed]
          exact elabArgsH_scoped_of faithful modes path f (i + 1) rest _ allowed others present
      | byName =>
          simp only [HView.forget.forgetAll, elabArgs, passed, HView.forget_orig] at present
          simp only [elabArgsH, passed]
          exact elabArgsH_scoped_of faithful modes path f (i + 1) rest _ allowed others present
      | evaluate check =>
          cases check with
          | none =>
              simp only [HView.forget.forgetAll, elabArgs, passed] at present
              simp only [elabArgsH, passed]
              exact ⟨elabH_scoped_of faithful modes (path ++ [i]) a allowed first present.1, present.2.1,
                elabArgsH_scoped_of faithful modes path f (i + 1) rest _ _ others present.2.2⟩
          | some T =>
              simp only [HView.forget.forgetAll, elabArgs, passed] at present
              simp only [elabArgsH, passed]
              exact ⟨elabH_scoped_of faithful modes (path ++ [i]) a allowed first present.1, present.2.1,
                elabArgsH_scoped_of faithful modes path f (i + 1) rest _ _ others present.2.2⟩
      | byNeed =>
          simp only [HView.forget.forgetAll, elabArgs, passed] at present
          simp only [elabArgsH, passed]
          exact ⟨elabH_scoped_of faithful modes (path ++ [i]) a allowed first present.1, present.2.1,
            elabArgsH_scoped_of faithful modes path f (i + 1) rest _ _ others present.2.2⟩
end

/-! ## Sites -/

theorem finish_sites (f : String) (done : List MData) : (finish decls f done).sites = [] := by
  simp only [finish]
  split
  · split <;> rfl
  · rfl

theorem site_index {path : List ℕ} {i j : ℕ} {r r' : List ℕ} (same : path ++ i :: r = path ++ j :: r') :
    i = j :=
  (List.cons.inj (List.append_cancel_left same)).1

mutual
/-- **Every binder site of the code extends the path.** -/
theorem elabH_sites (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : HView, ∀ s ∈ (elabH cl π decls modes path v).sites, ElaborationHygiene.Below path s
  | .holdMark _ _, s, member => by simp [elabH, Comp.sites] at member
  | .runMark _ inner, s, member => by
      cases inner with
      | var o' y => simp [elabH, Comp.sites] at member
      | holdMark o' u => exact elabH_sites modes path (.holdMark o' u) s member
      | runMark o' i => exact elabH_sites modes path (.runMark o' i) s member
      | symbol o' g => exact elabH_sites modes path (.symbol o' g) s member
      | call o' g args => exact elabH_sites modes path (.call o' g args) s member
      | inert o' => exact elabH_sites modes path (.inert o') s member
      | other o' elements => exact elabH_sites modes path (.other o' elements) s member
  | .var o y, s, member => by
      simp only [elabH, varAt] at member
      split at member
      · simp [Comp.sites] at member
      · split at member <;> simp [Comp.sites] at member
      · simp [Comp.sites] at member
      · simp [Comp.sites] at member
  | .symbol _ _, s, member => by simp [elabH, Comp.sites] at member
  | .call _ f args, s, member => by
      simp only [elabH] at member
      obtain ⟨j, r, -, -, rfl⟩ := elabArgsH_sites _ _ (finish_sites decls f) modes path 0 args [] s member
      exact ⟨j, r, rfl⟩
  | .inert _, s, member => by simp [elabH, Comp.sites] at member
  | .other _ [], s, member => by simp [elabH, Comp.sites] at member
  | .other o (head :: args), s, member => by
      have atHead := elabH_sites modes (path ++ [args.length]) head
      have atArgs := fun (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
          (quiet : ∀ done, (fin done).sites = []) => elabArgsH_sites pass fin quiet modes path 0 args []
      cases cl with
      | asWritten => simp [elabH, Comp.sites] at member
      | atRunTime => simp [elabH, Comp.sites] at member
      | static pass =>
          simp only [elabH] at member
          split at member
          · obtain ⟨j, r, -, -, rfl⟩ := atArgs _ _ (fun _ => rfl) s member
            exact ⟨j, r, rfl⟩
          · simp only [Comp.sites, List.mem_cons, List.mem_append] at member
            rcases member with rfl | inHead | inArgs
            · exact ⟨args.length, [], rfl⟩
            · exact ElaborationHygiene.below_extend (atHead s inHead)
            · obtain ⟨j, r, -, -, rfl⟩ := atArgs _ _ (fun _ => rfl) s inArgs
              exact ⟨j, r, rfl⟩

/-- The binder sites of the arguments' code: below the path at an index of an argument still to pass. -/
theorem elabArgsH_sites (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
    (quiet : ∀ done, (fin done).sites = []) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (i : ℕ) (args : List HView) (done : List MData),
      ∀ s ∈ (elabArgsH cl π decls pass fin modes path i args done).sites,
        ∃ j r, i ≤ j ∧ j < i + args.length ∧ s = path ++ j :: r
  | _, [], done, s, member => by
      simp only [elabArgsH, quiet] at member
      cases member
  | i, a :: rest, done, s, member => by
      have later := fun done' => elabArgsH_sites pass fin quiet modes path (i + 1) rest done' s
      have here := elabH_sites modes (path ++ [i]) a s
      have shift : ∀ j r, i + 1 ≤ j ∧ j < i + 1 + rest.length ∧ s = path ++ j :: r →
          ∃ j r, i ≤ j ∧ j < i + (a :: rest).length ∧ s = path ++ j :: r := by
        rintro j r ⟨low, high, same⟩
        exact ⟨j, r, by omega, by simp only [List.length_cons]; omega, same⟩
      have atArrow : s = path ++ [i] ∨ s ∈ (elabH cl π decls modes (path ++ [i]) a).sites ∨
          s ∈ (elabArgsH cl π decls pass fin modes path (i + 1) rest (slot (path ++ [i]) :: done)).sites →
          ∃ j r, i ≤ j ∧ j < i + (a :: rest).length ∧ s = path ++ j :: r := by
        rintro (rfl | inA | inRest)
        · exact ⟨i, [], le_refl _, by simp, rfl⟩
        · obtain ⟨j, r, rfl⟩ := here inA
          exact ⟨i, j :: r, le_refl _, by simp, by simp⟩
        · obtain ⟨j, r, bounds⟩ := later _ inRest
          exact shift j r bounds
      cases passed : pass i a with
      | text u =>
          simp only [elabArgsH, passed] at member
          obtain ⟨j, r, bounds⟩ := later _ member
          exact shift j r bounds
      | byName =>
          simp only [elabArgsH, passed] at member
          obtain ⟨j, r, bounds⟩ := later _ member
          exact shift j r bounds
      | evaluate check =>
          cases check with
          | none =>
              simp only [elabArgsH, passed, Comp.sites, List.mem_cons, List.mem_append] at member
              exact atArrow member
          | some T =>
              simp only [elabArgsH, passed, Comp.sites, List.mem_cons, List.mem_append] at member
              exact atArrow member
      | byNeed =>
          simp only [elabArgsH, passed, Comp.sites, List.mem_cons, List.mem_append] at member
          exact atArrow member
end

/-- The sites of an arrow over two codes are distinct when the arrow's site is the path at an index,
the bound code's sites are below it, and the body's sites are below the path at other indices. -/
theorem nodup_arrow {path : List ℕ} {i : ℕ} {bound body : List (List ℕ)}
    (boundBelow : ∀ s ∈ bound, ElaborationHygiene.Below (path ++ [i]) s)
    (bodyApart : ∀ s ∈ body, ∃ j r, j ≠ i ∧ s = path ++ j :: r)
    (boundNodup : bound.Nodup) (bodyNodup : body.Nodup) : ((path ++ [i]) :: (bound ++ body)).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨boundNodup, bodyNodup, ?_⟩⟩
  · intro member
    rcases List.mem_append.mp member with inBound | inBody
    · obtain ⟨j, r, same⟩ := boundBelow _ inBound
      have lengths := congrArg List.length same
      simp only [List.length_append, List.length_cons, List.length_nil] at lengths
      omega
    · obtain ⟨j, r, different, same⟩ := bodyApart _ inBody
      exact different (site_index (r := []) same).symm
  · intro s inBound s' inBody same
    subst same
    obtain ⟨j, r, sameBound⟩ := boundBelow _ inBound
    obtain ⟨j', r', different, sameBody⟩ := bodyApart _ inBody
    rw [sameBound, List.append_assoc] at sameBody
    exact different (site_index sameBody).symm

mutual
/-- **No two binders of the code share a site.** -/
theorem elabH_nodup (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : HView, (elabH cl π decls modes path v).sites.Nodup
  | .holdMark _ _ => by simp [elabH, Comp.sites]
  | .runMark _ inner => by
      cases inner with
      | var o' y => simp [elabH, Comp.sites]
      | holdMark o' u => exact elabH_nodup modes path (.holdMark o' u)
      | runMark o' i => exact elabH_nodup modes path (.runMark o' i)
      | symbol o' g => exact elabH_nodup modes path (.symbol o' g)
      | call o' g args => exact elabH_nodup modes path (.call o' g args)
      | inert o' => exact elabH_nodup modes path (.inert o')
      | other o' elements => exact elabH_nodup modes path (.other o' elements)
  | .var o y => by
      simp only [elabH, varAt]
      split
      · simp [Comp.sites]
      · split <;> simp [Comp.sites]
      · simp [Comp.sites]
      · simp [Comp.sites]
  | .symbol _ _ => by simp [elabH, Comp.sites]
  | .call _ f args => by
      simp only [elabH]
      exact elabArgsH_nodup _ _ (finish_sites decls f) modes path 0 args []
  | .inert _ => by simp [elabH, Comp.sites]
  | .other _ [] => by simp [elabH, Comp.sites]
  | .other o (head :: args) => by
      have atHead := elabH_nodup modes (path ++ [args.length]) head
      have headBelow := elabH_sites cl π decls modes (path ++ [args.length]) head
      have atArgs := fun (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
          (quiet : ∀ done, (fin done).sites = []) => elabArgsH_nodup pass fin quiet modes path 0 args []
      have argsBelow := fun (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
          (quiet : ∀ done, (fin done).sites = []) => elabArgsH_sites cl π decls pass fin quiet modes path 0 args []
      cases cl with
      | asWritten => simp [elabH, Comp.sites]
      | atRunTime => simp [elabH, Comp.sites]
      | static pass =>
          simp only [elabH]
          split
          · exact atArgs _ _ (fun _ => rfl)
          · simp only [Comp.sites]
            refine nodup_arrow headBelow (fun s inArgs => ?_) atHead (atArgs _ _ (fun _ => rfl))
            obtain ⟨j, r, -, high, same⟩ := argsBelow _ _ (fun _ => rfl) s inArgs
            exact ⟨j, r, by omega, same⟩

theorem elabArgsH_nodup (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
    (quiet : ∀ done, (fin done).sites = []) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (i : ℕ) (args : List HView) (done : List MData),
      (elabArgsH cl π decls pass fin modes path i args done).sites.Nodup
  | _, [], done => by
      simp only [elabArgsH, quiet]
      exact List.nodup_nil
  | i, a :: rest, done => by
      have later := fun done' => elabArgsH_nodup pass fin quiet modes path (i + 1) rest done'
      have laterBelow := fun done' => elabArgsH_sites cl π decls pass fin quiet modes path (i + 1) rest done'
      have here := elabH_nodup modes (path ++ [i]) a
      have hereBelow := elabH_sites cl π decls modes (path ++ [i]) a
      have arrow : ((path ++ [i]) :: ((elabH cl π decls modes (path ++ [i]) a).sites ++
          (elabArgsH cl π decls pass fin modes path (i + 1) rest (slot (path ++ [i]) :: done)).sites)).Nodup :=
        nodup_arrow hereBelow (fun s inRest => by
          obtain ⟨j, r, low, -, same⟩ := laterBelow _ s inRest
          exact ⟨j, r, by omega, same⟩) here (later _)
      cases passed : pass i a with
      | text u =>
          simp only [elabArgsH, passed]
          exact later _
      | byName =>
          simp only [elabArgsH, passed]
          exact later _
      | evaluate check =>
          cases check with
          | none =>
              simp only [elabArgsH, passed, Comp.sites]
              exact arrow
          | some T =>
              simp only [elabArgsH, passed, Comp.sites]
              exact arrow
      | byNeed =>
          simp only [elabArgsH, passed, Comp.sites]
          exact arrow
end

#print axioms hview_within
#print axioms hview_coherent
#print axioms byValue_faithful
#print axioms elabH_scoped
#print axioms elabH_scoped_of
#print axioms elabH_sites
#print axioms elabH_nodup

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
