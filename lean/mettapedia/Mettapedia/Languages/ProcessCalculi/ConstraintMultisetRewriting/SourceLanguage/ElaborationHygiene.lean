import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Hygiene

/-!
# The elaboration's reading of text as code is hygienic

At run time the program reads text as code by the elaboration (every variable a value). The arrows
it inserts are binders, each at its own site below a path. The reading puts that path below
`[2, k]`, where `k` is past every second component of a code site `[2, k', …]` of a name of the text
(`freshIndex`): so no name of the text has the site of an arrow of the code (`reading_apart`), and every
name of a code site in the code is one of the code's own slots, unopened (`reading_uniform`). Together
the reading is hygienic (`reading_hygienic`).

* **Names** (`NamesWithin`, `view_within`, `elabText_names`): every name of the code is a name of the
  text or an unopened slot.
* **Sites** (`elabText_sites`): every binder site of the code made below a path extends that path.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Hygiene

/-! ## Names of views -/

/-- Every name of the view's text, and of the texts it is made of, satisfies `A`. -/
def NamesWithin (A : Name mkeys → Prop) : View → Prop
  | .holdMark o u => (∀ x ∈ support o, A x) ∧ ∀ x ∈ support u, A x
  | .runMark o inner => (∀ x ∈ support o, A x) ∧ NamesWithin A inner
  | .var o _ => ∀ x ∈ support o, A x
  | .symbol o _ => ∀ x ∈ support o, A x
  | .call o _ args => (∀ x ∈ support o, A x) ∧ NamesWithinArgs A args
  | .inert o => ∀ x ∈ support o, A x
  | .other o => ∀ x ∈ support o, A x
where
  NamesWithinArgs (A : Name mkeys → Prop) : List View → Prop
    | [] => True
    | a :: rest => NamesWithin A a ∧ NamesWithinArgs A rest

/-- The names of a view's own text. -/
theorem NamesWithin.orig {A : Name mkeys → Prop} : ∀ {v : View}, NamesWithin A v → ∀ x ∈ support v.orig, A x
  | .holdMark _ _, within => within.1
  | .runMark _ _, within => within.1
  | .var _ _, within => within
  | .symbol _ _, within => within
  | .call _ _ _, within => within.1
  | .inert _, within => within
  | .other _, within => within

mutual
theorem NamesWithin.mono {A B : Name mkeys → Prop} (more : ∀ x, A x → B x) :
    ∀ v : View, NamesWithin A v → NamesWithin B v
  | .holdMark _ _, ⟨ho, hu⟩ => ⟨fun x hx => more x (ho x hx), fun x hx => more x (hu x hx)⟩
  | .runMark _ inner, ⟨ho, hi⟩ => ⟨fun x hx => more x (ho x hx), NamesWithin.mono more inner hi⟩
  | .var _ _, ho => fun x hx => more x (ho x hx)
  | .symbol _ _, ho => fun x hx => more x (ho x hx)
  | .call _ _ args, ⟨ho, ha⟩ => ⟨fun x hx => more x (ho x hx), NamesWithinArgs.mono more args ha⟩
  | .inert _, ho => fun x hx => more x (ho x hx)
  | .other _, ho => fun x hx => more x (ho x hx)

theorem NamesWithinArgs.mono {A B : Name mkeys → Prop} (more : ∀ x, A x → B x) :
    ∀ args : List View, NamesWithin.NamesWithinArgs A args → NamesWithin.NamesWithinArgs B args
  | [], _ => trivial
  | a :: rest, ⟨ha, hr⟩ => ⟨NamesWithin.mono more a ha, NamesWithinArgs.mono more rest hr⟩
end

theorem support_atTop {Δ : Ctx MSig} {s : Unit} (h : Δ = []) (t : Term (signature MSig (fam mkeys)) Δ s) :
    support (atTop h t) = support t := by
  subst h
  rfl

/-! The view of a term, one constructor at a time (by definition). -/

theorem viewAt_hold {Δ : Ctx MSig} (u : Term (signature MSig (fam mkeys)) ([] ++ Δ) ()) (h : Δ = []) :
    viewAt (Term.op (Sum.inl MOp.hold) (Args.cons u Args.nil) : Term (signature MSig (fam mkeys)) Δ ()) h =
      .holdMark (atTop h (.op (.inl .hold) (.cons u .nil))) (atTop ((List.nil_append Δ).trans h) u) := rfl

theorem viewAt_run {Δ : Ctx MSig} (u : Term (signature MSig (fam mkeys)) ([] ++ Δ) ()) (h : Δ = []) :
    viewAt (Term.op (Sum.inl MOp.run) (Args.cons u Args.nil) : Term (signature MSig (fam mkeys)) Δ ()) h =
      .runMark (atTop h (.op (.inl .run) (.cons u .nil))) (viewAt u ((List.nil_append Δ).trans h)) := rfl

theorem viewAt_tup {Δ : Ctx MSig} (n : ℕ) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.tup n)) Δ)
    (h : Δ = []) :
    viewAt (Term.op (Sum.inl (MOp.tup n)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      (match viewArgsAt args h with
       | .symbol _ f :: rest => .call (atTop h (.op (.inl (.tup n)) args)) f rest
       | _ => .other (atTop h (.op (.inl (.tup n)) args))) := rfl

theorem viewAt_sym {Δ : Ctx MSig} (f : String) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.sym f)) Δ)
    (h : Δ = []) :
    viewAt (Term.op (Sum.inl (MOp.sym f)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .symbol (atTop h (.op (.inl (.sym f)) args)) f := rfl

theorem viewAt_num {Δ : Ctx MSig} (k : Int) (args : Args (signature MSig (fam mkeys)) (MOp.arity (MOp.num k)) Δ)
    (h : Δ = []) :
    viewAt (Term.op (Sum.inl (MOp.num k)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .inert (atTop h (.op (.inl (.num k)) args)) := rfl

theorem viewAt_lam {Δ : Ctx MSig} (args : Args (signature MSig (fam mkeys)) (MOp.arity MOp.lam) Δ) (h : Δ = []) :
    viewAt (Term.op (Sum.inl MOp.lam) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .inert (atTop h (.op (.inl .lam) args)) := rfl

theorem viewAt_name {Δ : Ctx MSig} (x : Name mkeys)
    (args : Args (signature MSig (fam mkeys)) ((fam mkeys x).1.map fun sort => ([], sort)) Δ) (h : Δ = []) :
    viewAt (Term.op (Sum.inr (.mk x)) args : Term (signature MSig (fam mkeys)) Δ ()) h =
      .var (atTop h (.op (.inr (.mk x)) args)) x := rfl

theorem viewAt_var {Δ : Ctx MSig} (v : Var Δ ()) (h : Δ = []) :
    viewAt (Term.var v : Term (signature MSig (fam mkeys)) Δ ()) h = .inert (atTop h (.var v)) := rfl

theorem viewArgsAt_nil {Δ : Ctx MSig} (h : Δ = []) :
    viewArgsAt (Args.nil : Args (signature MSig (fam mkeys)) [] Δ) h = [] := rfl

theorem viewArgsAt_cons {as : List (List Unit × Unit)} {bs : List Unit} {Δ : Ctx MSig}
    (hd : Term (signature MSig (fam mkeys)) (bs ++ Δ) ()) (tl : Args (signature MSig (fam mkeys)) as Δ)
    (h : Δ = []) :
    viewArgsAt (Args.cons (bs := bs) (s := ()) hd tl) h =
      if hb : bs = [] then viewAt hd (by subst hb; exact h) :: viewArgsAt tl h else viewArgsAt tl h := rfl

theorem atTop_names {Δ : Ctx MSig} {s : Unit} (h : Δ = []) (t : Term (signature MSig (fam mkeys)) Δ s) :
    ∀ x ∈ support (atTop h t), x ∈ support t := fun x hx => by rwa [support_atTop] at hx

mutual
/-- **A view's names are its text's names.** -/
theorem viewAtWith_within (active : Bool) : ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []) (skip : Bool),
    NamesWithin (· ∈ support t) (viewAtWith active skip t h)
  | _, (), .op (.inl .hold) (.cons u .nil), h, skip => by
      cases skip with
      | false =>
        refine ⟨atTop_names h _, fun x hx => ?_⟩
        rw [support_atTop] at hx
        simp [support, supportArgs, hx]
      | true =>
        exact NamesWithin.mono (fun x hx => by simp [support, supportArgs, hx]) _
          (viewAtWith_within active u ((List.nil_append _).trans h) false)
  | _, (), .op (.inl .run) (.cons u .nil), h, skip => by
      refine ⟨atTop_names h _, ?_⟩
      exact NamesWithin.mono (fun x hx => by simp [support, supportArgs, hx]) _
        (viewAtWith_within active u ((List.nil_append _).trans h) active)
  | _, (), .op (.inl (.tup n)) args, h, skip => by
      change NamesWithin _ (match viewArgsAtWith active args h with
        | .symbol _ f :: rest => .call (atTop h (.op (.inl (.tup n)) args)) f rest
        | _ => .other (atTop h (.op (.inl (.tup n)) args)))
      have inside := viewArgsAtWith_within active args h
      split
      · rename_i f rest same
        rw [same] at inside
        refine ⟨atTop_names h _, ?_⟩
        exact NamesWithinArgs.mono (fun x hx => by simpa [support] using hx) _ inside.2
      · exact atTop_names h _
  | _, (), .op (.inl (.sym f)) args, h, skip => by
      exact atTop_names h _
  | _, (), .op (.inl (.num k)) args, h, skip => by
      exact atTop_names h _
  | _, (), .op (.inl .lam) args, h, skip => by
      exact atTop_names h _
  | _, (), .op (.inr (.mk x)) args, h, skip => by
      exact atTop_names h _
  | _, (), .var v, h, skip => by
      exact atTop_names h _

theorem viewArgsAtWith_within (active : Bool) : ∀ {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []),
    NamesWithin.NamesWithinArgs (· ∈ supportArgs args) (viewArgsAtWith active args h)
  | _, _, .nil, h => by trivial
  | _, _, .cons (bs := bs) (s := ()) hd tl, h => by
      change NamesWithin.NamesWithinArgs _ (if hb : bs = [] then
        viewAtWith active false hd (by subst hb; exact h) :: viewArgsAtWith active tl h else viewArgsAtWith active tl h)
      split
      · rename_i hb
        refine ⟨NamesWithin.mono (fun x hx => by simp [supportArgs, hx]) _ (viewAtWith_within active hd _ false), ?_⟩
        exact NamesWithinArgs.mono (fun x hx => by simp [supportArgs, hx]) _ (viewArgsAtWith_within active tl h)
      · exact NamesWithinArgs.mono (fun x hx => by simp [supportArgs, hx]) _ (viewArgsAtWith_within active tl h)
end

theorem viewAt_within {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []) :
    NamesWithin (· ∈ support t) (viewAt t h) := viewAtWith_within false t h false

theorem viewArgsAt_within {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []) :
    NamesWithin.NamesWithinArgs (· ∈ supportArgs args) (viewArgsAt args h) := viewArgsAtWith_within false args h

/-- The names of `view t` are the names of `t`. -/
theorem view_within (t : MData) : NamesWithin (· ∈ support t) (view t) := viewAt_within t rfl

/-! ## Names of the code -/

theorem support_tupleArgs : ∀ (ts : List MData) (x : Name mkeys),
    x ∈ supportArgs (tupleArgs ts) → ∃ d ∈ ts, x ∈ support d
  | [], _, member => by simp [tupleArgs, supportArgs] at member
  | t :: ts, x, member => by
      simp only [tupleArgs, supportArgs, List.mem_append] at member
      rcases member with here | there
      · exact ⟨t, List.mem_cons_self, here⟩
      · obtain ⟨d, inside, hx⟩ := support_tupleArgs ts x there
        exact ⟨d, List.mem_cons_of_mem _ inside, hx⟩

theorem support_tuple (ts : List MData) (x : Name mkeys) (member : x ∈ support (tuple ts)) :
    ∃ d ∈ ts, x ∈ support d := by
  simp only [tuple, support] at member
  exact support_tupleArgs ts x member

/-- The text a mark or a declaration passes as written: what the view holds, or its text. -/
theorem passOf_text (π : Params) (decls : List Decl) (f : String) (i : ℕ) (a : View) (u : MData)
    (passed : passOf π decls f i a = .text u) : (∃ o, a = .holdMark o u) ∨ u = a.orig := by
  unfold passOf at passed
  split at passed
  · rename_i o u'
    cases passed
    exact .inl ⟨o, rfl⟩
  · cases passed
  · split at passed
    · split at passed
      · split at passed
        · cases passed
          exact .inr rfl
        · split at passed <;> (try split at passed) <;> cases passed
          exact .inr rfl
      · split at passed <;> cases passed
        exact .inr rfl
    · split at passed <;> cases passed
      exact .inr rfl

variable (π : Params) (decls : List Decl)

/-- A datum whose names satisfy `A` or are unopened. -/
abbrev Tame (A : Name mkeys → Prop) (d : MData) : Prop := ∀ x ∈ support d, A x ∨ x.scopes = []

mutual
/-- **Every name of the code is a name of the text, or an unopened slot.** -/
theorem elabText_names (A : Name mkeys → Prop) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : View, NamesWithin A v → ∀ d ∈ (elabText π decls modes path v).data, Tame A d
  | .holdMark _ u, within, d, member, x, hx => by
      simp only [elabText, Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within.2 x hx)
  | .runMark o inner, within, d, member, x, hx => by
      cases inner with
      | var o' y =>
          simp only [elabText, Comp.data, List.mem_singleton] at member
          subst member
          exact .inl (within.2 x hx)
      | holdMark o' u => exact elabText_names A modes path (.holdMark o' u) within.2 d member x hx
      | runMark o' i => exact elabText_names A modes path (.runMark o' i) within.2 d member x hx
      | symbol o' g => exact elabText_names A modes path (.symbol o' g) within.2 d member x hx
      | call o' g args => exact elabText_names A modes path (.call o' g args) within.2 d member x hx
      | inert o' => exact elabText_names A modes path (.inert o') within.2 d member x hx
      | other o' => exact elabText_names A modes path (.other o') within.2 d member x hx
  | .var o y, within, d, member, x, hx => by
      simp only [elabText, varAt] at member
      split at member
      · simp only [Comp.data, List.mem_singleton] at member
        subst member
        exact .inl (within x hx)
      · split at member <;>
        · simp only [Comp.data, List.mem_singleton] at member
          subst member
          exact .inl (within x hx)
      · simp only [Comp.data, List.mem_singleton] at member
        subst member
        exact .inl (within x hx)
      · simp only [Comp.data, List.mem_singleton] at member
        subst member
        exact .inl (within x hx)
  | .symbol o _, within, d, member, x, hx => by
      simp only [elabText, Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within x hx)
  | .call o f args, within, d, member, x, hx =>
      elabArgs_names A modes path f 0 args [] within.2 (fun _ none => by cases none) d member x hx
  | .inert o, within, d, member, x, hx => by
      simp only [elabText, Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within x hx)
  | .other o, within, d, member, x, hx => by
      simp only [elabText, Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within x hx)

theorem elabArgs_names (A : Name mkeys → Prop) (modes : Name mkeys → VarMode) (path : List ℕ) (f : String) :
    ∀ (i : ℕ) (args : List View) (done : List MData), NamesWithin.NamesWithinArgs A args →
      (∀ d ∈ done, Tame A d) → ∀ d ∈ (elabArgs π decls modes path f i args done).data, Tame A d
  | _, [], done, _, tame, d, member => by
      simp only [elabArgs, finish] at member
      have call : ∀ x ∈ support (tuple (sym f :: done.reverse)), A x ∨ x.scopes = [] := by
        intro x hx
        obtain ⟨e, inside, he⟩ := support_tuple _ x hx
        rcases List.mem_cons.mp inside with rfl | inDone
        · simp [sym, support, supportArgs] at he
        · exact tame e (List.mem_reverse.mp inDone) x he
      split at member
      · split at member <;>
        · simp only [Comp.data, List.mem_singleton] at member
          subst member
          exact call
      · simp only [Comp.data, List.mem_singleton] at member
        subst member
        exact call
  | i, a :: rest, done, ⟨first, others⟩, tame, d, member => by
      simp only [elabArgs] at member
      split at member
      · rename_i u passed
        refine elabArgs_names A modes path f (i + 1) rest (u :: done) others ?_ d member
        intro e inside
        rcases List.mem_cons.mp inside with rfl | old
        · rcases passOf_text π decls f i a e passed with ⟨o, rfl⟩ | rfl
          · exact fun x hx => .inl (first.2 x hx)
          · exact fun x hx => .inl (first.orig x hx)
        · exact tame e old
      · refine elabArgs_names A modes path f (i + 1) rest (a.orig :: done) others ?_ d member
        intro e inside
        rcases List.mem_cons.mp inside with rfl | old
        · exact fun x hx => .inl (first.orig x hx)
        · exact tame e old
      all_goals
        have slotTame : Tame A (slot (path ++ [i])) := by
          intro x hx
          simp only [slot, mvar, support, supportArgs, List.mem_singleton] at hx
          subst hx
          exact .inr rfl
        have restTame := elabArgs_names A modes path f (i + 1) rest (slot (path ++ [i]) :: done) others
          (fun e inside => by
            rcases List.mem_cons.mp inside with rfl | old
            · exact slotTame
            · exact tame e old)
        have aTame := elabText_names A modes (path ++ [i]) a first
        simp only [Comp.data, List.mem_cons, List.mem_append] at member
        first
          | (rcases member with rfl | inA | inRest
             · exact slotTame
             · exact aTame d inA
             · exact restTame d inRest)
end

/-! ## Sites of the code -/

/-- A site below a path. -/
abbrev Below (path s : List ℕ) : Prop := ∃ i r, s = path ++ i :: r

theorem below_extend {path : List ℕ} {i : ℕ} {s : List ℕ} (below : Below (path ++ [i]) s) : Below path s := by
  obtain ⟨j, r, rfl⟩ := below
  exact ⟨i, j :: r, by simp⟩

mutual
/-- **Every binder site of the code made below a path extends that path.** -/
theorem elabText_sites (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : View, ∀ s ∈ (elabText π decls modes path v).sites, Below path s
  | .holdMark _ _, s, member => by simp [elabText, Comp.sites] at member
  | .runMark o inner, s, member => by
      cases inner with
      | var o' y => simp [elabText, Comp.sites] at member
      | holdMark o' u => exact elabText_sites modes path (.holdMark o' u) s member
      | runMark o' i => exact elabText_sites modes path (.runMark o' i) s member
      | symbol o' g => exact elabText_sites modes path (.symbol o' g) s member
      | call o' g args => exact elabText_sites modes path (.call o' g args) s member
      | inert o' => exact elabText_sites modes path (.inert o') s member
      | other o' => exact elabText_sites modes path (.other o') s member
  | .var o y, s, member => by
      simp only [elabText, varAt] at member
      split at member
      · simp [Comp.sites] at member
      · split at member <;> simp [Comp.sites] at member
      · simp [Comp.sites] at member
      · simp [Comp.sites] at member
  | .symbol _ _, s, member => by simp [elabText, Comp.sites] at member
  | .call _ f args, s, member => elabArgs_sites modes path f 0 args [] s member
  | .inert _, s, member => by simp [elabText, Comp.sites] at member
  | .other _, s, member => by simp [elabText, Comp.sites] at member

theorem elabArgs_sites (modes : Name mkeys → VarMode) (path : List ℕ) (f : String) :
    ∀ (i : ℕ) (args : List View) (done : List MData), ∀ s ∈ (elabArgs π decls modes path f i args done).sites,
      Below path s
  | _, [], done, s, member => by
      simp only [elabArgs, finish] at member
      split at member
      · split at member <;> simp [Comp.sites] at member
      · simp [Comp.sites] at member
  | i, a :: rest, done, s, member => by
      simp only [elabArgs] at member
      split at member
      · exact elabArgs_sites modes path f (i + 1) rest _ s member
      · exact elabArgs_sites modes path f (i + 1) rest _ s member
      all_goals
        simp only [Comp.sites, List.mem_cons, List.mem_append] at member
        rcases member with rfl | inA | inRest
        · exact ⟨i, [], rfl⟩
        · exact below_extend (elabText_sites modes (path ++ [i]) a s inA)
        · exact elabArgs_sites modes path f (i + 1) rest _ s inRest
end

/-! ## The reading -/

theorem le_foldr_max : ∀ (l : List ℕ) (n : ℕ), n ∈ l → n ≤ l.foldr max 0
  | [], _, member => by cases member
  | m :: ms, n, member => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max ms n inside) (le_max_right _ _)

theorem codeIndex_le (t : MData) : ∀ x ∈ support t, codeIndex x ≤ freshIndex t := fun x member =>
  le_foldr_max _ _ (List.mem_map.mpr ⟨x, member, rfl⟩)

/-- No name of the text has the site of an arrow of the code. -/
theorem fresh_reading_apart (t : MData) (v : View) : ∀ x ∈ support t,
    mkeys.site x.key ∉ (elabText π decls (fun _ => .value) [2, freshIndex t] v).sites := by
  intro x member site
  obtain ⟨i, r, same⟩ := elabText_sites π decls (fun _ => .value) [2, freshIndex t] v _ site
  have index := codeIndex_le t x member
  have siteEq : x.key.site = 2 :: freshIndex t :: i :: r := by simpa using same
  have reach : codeIndex x = freshIndex t + 1 := by simp [codeIndex, siteEq]
  omega

theorem reading_apart (t : MData) : ∀ x ∈ support t, mkeys.site x.key ∉ (reading π decls t).sites :=
  fresh_reading_apart π decls t (view t)

/-- A computation whose names of its own binder sites are unopened has uniform binders. -/
theorem uniform_of_sites_unopened :
    ∀ c : Comp mkeys [] () MTy,
      (∀ d ∈ c.data, ∀ x ∈ support d, mkeys.site x.key ∈ c.sites → x.scopes = []) → Uniform c
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .run _, _ => trivial
  | .let_ s p c k, h =>
      ⟨⟨[], fun x hx same => h p (by simp [Comp.data]) x hx (List.mem_cons.mpr (.inl same)),
          fun t ht x hx same => h t (by simp [Comp.data, ht]) x hx (List.mem_cons.mpr (.inl same))⟩,
        uniform_of_sites_unopened c fun t ht x hx site =>
          h t (by simp [Comp.data, ht]) x hx (List.mem_cons_of_mem _ (List.mem_append_left _ site)),
        uniform_of_sites_unopened k fun t ht x hx site =>
          h t (by simp [Comp.data, ht]) x hx (List.mem_cons_of_mem _ (List.mem_append_right _ site))⟩
  | .choice c d, h =>
      ⟨uniform_of_sites_unopened c fun t ht x hx site =>
          h t (by simp [Comp.data, ht]) x hx (List.mem_append_left _ site),
        uniform_of_sites_unopened d fun t ht x hx site =>
          h t (by simp [Comp.data, ht]) x hx (List.mem_append_right _ site)⟩
  | .fail, _ => trivial
  | .query _ _ k, h => uniform_of_sites_unopened k fun t ht x hx site =>
      h t (by simp [Comp.data, ht]) x hx site
  | .add _ _ k, h => uniform_of_sites_unopened k fun t ht x hx site =>
      h t (by simp [Comp.data, ht]) x hx site
  | .remove _ _ k, h => uniform_of_sites_unopened k fun t ht x hx site =>
      h t (by simp [Comp.data, ht]) x hx site
  | .new s x k, h =>
      ⟨⟨[], fun y hy same => h x (by simp [Comp.data]) y hy (List.mem_cons.mpr (.inl same)),
          fun t ht y hy same => h t (by simp [Comp.data, ht]) y hy (List.mem_cons.mpr (.inl same))⟩,
        uniform_of_sites_unopened k fun t ht y hy site =>
          h t (by simp [Comp.data, ht]) y hy (List.mem_cons_of_mem _ site)⟩
  | .check _ k, h => uniform_of_sites_unopened k fun t ht x hx site =>
      h t (by simp [Comp.data, ht]) x hx site
  | .delay s x c k, h =>
      ⟨⟨[], fun y hy same => h x (by simp [Comp.data]) y hy (List.mem_cons.mpr (.inl same)),
          fun t ht y hy same => h t (by simp [Comp.data, ht]) y hy (List.mem_cons.mpr (.inl same))⟩,
        uniform_of_sites_unopened c fun t ht y hy site =>
          h t (by simp [Comp.data, ht]) y hy (List.mem_cons_of_mem _ (List.mem_append_left _ site)),
        uniform_of_sites_unopened k fun t ht y hy site =>
          h t (by simp [Comp.data, ht]) y hy (List.mem_cons_of_mem _ (List.mem_append_right _ site))⟩
  | .force _, _ => trivial

/-- The code's binders are uniform: every name of a code site in the code is an unopened slot. -/
theorem fresh_reading_uniform (t : MData) (v : View) (inside : NamesWithin (· ∈ support t) v) :
    Uniform (elabText π decls (fun _ => .value) [2, freshIndex t] v) := by
  refine uniform_of_sites_unopened _ fun d member x hx site => ?_
  rcases elabText_names π decls (· ∈ support t) (fun _ => .value) [2, freshIndex t] v
      inside d member x hx with inText | unopened
  · exact absurd site (fresh_reading_apart π decls t v x inText)
  · exact unopened

theorem reading_uniform (t : MData) : Uniform (reading π decls t) :=
  fresh_reading_uniform π decls t (view t) (view_within t)

/-- **The elaboration's reading of text as code is hygienic.** -/
theorem reading_hygienic : ReadingHygienic (reading π decls) :=
  ⟨reading_apart π decls, reading_uniform π decls⟩

/-- **Every elaborated program reads text as code hygienically.** -/
theorem elaborate_hygienic (P : SProgram) : ReadingHygienic (elaborate π P).reflect :=
  reading_hygienic π P.decls

#print axioms view_within
#print axioms elabText_names
#print axioms elabText_sites
#print axioms reading_apart
#print axioms reading_uniform
#print axioms reading_hygienic
#print axioms elaborate_hygienic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene
