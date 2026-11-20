import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.WellFormed

/-!
# Text read as code without capture: uniform binders along every run

A `let`, `new` or `delay` of site `s` opens its names at its bind by renaming **every** name of site
`s` in its pattern and body (`openAt`), whatever that name's scopes. The renaming is an
alpha-conversion only if every name of site `s` there is the binder's own. Program text satisfies this
by its scope clause; text read as code at run time satisfies it only if the reading never puts a binder
at the site of a name of the text it reads.

* **Uniform binders** (`BinderUniform`, `Uniform`): every name of a binder's site in its pattern and
  body has one and the same scopes, the binder's level. A name of the binder's site at another level
  is a name the binder would capture.
* **The law of readings** (`ReadingHygienic`): the code a reading makes of a text has no binder at the
  site of a name of that text, and its binders are uniform. It is a law of the reading, as the laws of a
  `Typing` are laws of the discipline; the elaboration's reading satisfies it
  (`ElaborationHygiene.elaborate_hygienic`).
* **The invariant** (`runs_uniform`, `uniform_along_runs`): along every run of a program whose
  right-hand sides name only unopened names (the scope clause of `WellFormed`), from a query of the
  same kind, with a reading whose code is uniform, every alternative's computation, frames and pending
  cells have uniform binders. So at every bind, every name of the binder's site that it renames is at
  the binder's level (`bind_renames_level`).
* **Code never renames its text** (`opening_fixes_text`): under the `apart` clause, the opening of any
  binder site of the code leaves the text it was read from as it is.
* **The dereferencing choice** (`principal_texts`): two most general solutions of one store dereference
  a text to two texts that are instances of each other and that the store entails equal.

What these do not say: that a binder's own names occur nowhere outside it when it binds (privacy) at
every step of every run of the whole language. For program text without `run` that is the hygiene of
`let` along runs; for the whole language it is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Hygiene

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

/-! ## Supports under relabelling -/

section Relabel

variable (g : Name κ → List ℕ)

/-- Where a relabelling sends a name: new scopes, the same key. -/
def relabelName (x : Name κ) : Name κ := ⟨g x, x.key⟩

mutual
theorem support_relabel : ∀ {Δ : Ctx S} {sort : S.Srt} (t : Term (signature S (fam κ)) Δ sort),
    support (instantiate (relabel κ g) t) = (support t).map (relabelName g)
  | _, _, .var _ => rfl
  | _, _, .op (.inl _) args => by
      simp only [instantiate, support, supportArgs_relabel args]
  | _, _, .op (.inr (.mk x)) args => by
      have inner := supportArgs_relabel args
      simp only [instantiate, relabel, generator, Mettapedia.OSLF.Binding.bind, bindArgs_selfArgs,
        support, inner, List.map_cons, relabelName]

theorem supportArgs_relabel : ∀ {as : List (List S.Srt × S.Srt)} {Δ : Ctx S}
    (args : Args (signature S (fam κ)) as Δ),
    supportArgs (instantiateArgs (relabel κ g) args) = (supportArgs args).map (relabelName g)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instantiateArgs, supportArgs, support_relabel head, supportArgs_relabel tail,
        List.map_append]
end

end Relabel

/-! ## Levels -/

/-- Every name of site `s` in the term has the scopes `L`. -/
def AtLevel (s : κ.Site) (L : List ℕ) {Δ : Ctx S} {sort : S.Srt}
    (t : Term (signature S (fam κ)) Δ sort) : Prop :=
  ∀ x ∈ support t, κ.site x.key = s → x.scopes = L

/-- A relabelling that moves each name's scopes by its site and its scopes only. -/
def byLevel (h : κ.Site → List ℕ → List ℕ) : Assignment (fam κ) (fam κ) :=
  relabel κ fun x => h (κ.site x.key) x.scopes

/-- A copy at a scope moves every level by the same prefix. -/
theorem copyAt_byLevel (n : ℕ) : copyAt κ n = byLevel (fun _ L => n :: L) := rfl

/-- Opening a site moves the level of that site's names. -/
theorem openAt_byLevel (s : κ.Site) (n : ℕ) :
    openAt κ s n = byLevel (fun s' L => if s' = s then n :: L else L) := rfl

theorem atLevel_byLevel (h : κ.Site → List ℕ → List ℕ) {s : κ.Site} {L : List ℕ} {Δ : Ctx S}
    {sort : S.Srt} {t : Term (signature S (fam κ)) Δ sort} (level : AtLevel s L t) :
    AtLevel s (h s L) (instantiate (byLevel h) t) := by
  intro x member same
  rw [byLevel, support_relabel] at member
  obtain ⟨y, inside, rfl⟩ := List.mem_map.mp member
  simp only [relabelName] at same ⊢
  rw [same, level y inside same]

theorem data_mapData (f : Data κ Γ star → Data κ Γ star) (c : Comp κ Γ star Ty) :
    (c.mapData f).data = c.data.map f := by
  induction c <;> simp_all [Comp.mapData, Comp.data]

/-! ## Free contextual names of suspended code -/

def outsideSite (site : κ.Site) (names : List (Name κ)) : List (Name κ) :=
  names.filter fun name => κ.site name.key != site

/-- Contextual names captured from outside a computation. A binding site is
removed only from the pattern and continuation that it binds; a producer or
suspended computation still executes in the enclosing context. -/
def freeNames : Comp κ Γ star Ty → List (Name κ)
  | .ret value | .apply value | .run value | .force value => support value
  | .let_ site pattern producer body =>
      freeNames producer ++ outsideSite site (support pattern ++ freeNames body)
  | .choice left right => freeNames left ++ freeNames right
  | .fail => []
  | .query space pattern body => support space ++ support pattern ++ freeNames body
  | .add space value body | .remove space value body =>
      support space ++ support value ++ freeNames body
  | .new site value body => outsideSite site (support value ++ freeNames body)
  | .check _ body => freeNames body
  | .delay site cell suspended body =>
      freeNames suspended ++ outsideSite site (support cell ++ freeNames body)

/-- A name at a `let`'s binding site can be a capture only when it occurs in
the producer, which is outside the binder. Internal pattern and continuation
occurrences at that site are not closure captures. -/
theorem freeNames_let_at_bound_site (site : κ.Site) (pattern : Data κ Γ star)
    (producer body : Comp κ Γ star Ty) (name : Name κ)
    (member : name ∈ freeNames (.let_ site pattern producer body))
    (same : κ.site name.key = site) : name ∈ freeNames producer := by
  rcases List.mem_append.mp member with captured | internal
  · exact captured
  · have allowed := (List.mem_filter.mp internal).2
    simp [same] at allowed

/-! ## Uniform binders -/

/-- **A uniform binder** of site `s`, pattern `p` and body `k`: every name of site `s` in `p` and in `k`
has one and the same scopes. -/
def BinderUniform (s : κ.Site) (p : Data κ Γ star) (k : Comp κ Γ star Ty) : Prop :=
  ∃ L, AtLevel s L p ∧ ∀ t ∈ k.data, AtLevel s L t

/-- **Every binder of the computation is uniform.** -/
def Uniform : Comp κ Γ star Ty → Prop
  | .ret _ => True
  | .apply _ => True
  | .run _ => True
  | .let_ s p c k => BinderUniform s p k ∧ Uniform c ∧ Uniform k
  | .choice c d => Uniform c ∧ Uniform d
  | .fail => True
  | .query _ _ k => Uniform k
  | .add _ _ k => Uniform k
  | .remove _ _ k => Uniform k
  | .new s x k => BinderUniform s x k ∧ Uniform k
  | .check _ k => Uniform k
  | .delay s x c k => BinderUniform s x k ∧ Uniform c ∧ Uniform k
  | .force _ => True

theorem binderUniform_byLevel (h : κ.Site → List ℕ → List ℕ) {s : κ.Site} {p : Data κ Γ star}
    {k : Comp κ Γ star Ty} (u : BinderUniform s p k) :
    BinderUniform s (instantiate (byLevel h) p) (k.inst (byLevel h)) := by
  obtain ⟨L, hp, hk⟩ := u
  refine ⟨h s L, atLevel_byLevel h hp, fun t member => ?_⟩
  rw [Comp.inst, data_mapData] at member
  obtain ⟨t₀, inside, rfl⟩ := List.mem_map.mp member
  exact atLevel_byLevel h (hk t₀ inside)

/-- **Relabelling by levels keeps binders uniform**: copies and openings. -/
theorem uniform_byLevel (h : κ.Site → List ℕ → List ℕ) :
    ∀ c : Comp κ Γ star Ty, Uniform c → Uniform (c.inst (byLevel h))
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .run _, _ => trivial
  | .let_ _ _ c k, ⟨b, hc, hk⟩ =>
      ⟨binderUniform_byLevel h b, uniform_byLevel h c hc, uniform_byLevel h k hk⟩
  | .choice c d, ⟨hc, hd⟩ => ⟨uniform_byLevel h c hc, uniform_byLevel h d hd⟩
  | .fail, _ => trivial
  | .query _ _ k, hk => uniform_byLevel h k hk
  | .add _ _ k, hk => uniform_byLevel h k hk
  | .remove _ _ k, hk => uniform_byLevel h k hk
  | .new _ _ k, ⟨b, hk⟩ => ⟨binderUniform_byLevel h b, uniform_byLevel h k hk⟩
  | .check _ k, hk => uniform_byLevel h k hk
  | .delay _ _ c k, ⟨b, hc, hk⟩ =>
      ⟨binderUniform_byLevel h b, uniform_byLevel h c hc, uniform_byLevel h k hk⟩
  | .force _, _ => trivial

/-- **Text whose names are all unopened has uniform binders** (each at the level `[]`). -/
theorem uniform_of_unopened :
    ∀ c : Comp κ Γ star Ty, (∀ t ∈ c.data, ∀ x ∈ support t, x.scopes = []) → Uniform c
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .run _, _ => trivial
  | .let_ s p c k, unopened =>
      ⟨⟨[], fun x hx _ => unopened p (by simp [Comp.data]) x hx,
          fun t ht x hx _ => unopened t (by simp [Comp.data, ht]) x hx⟩,
        uniform_of_unopened c fun t ht => unopened t (by simp [Comp.data, ht]),
        uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])⟩
  | .choice c d, unopened =>
      ⟨uniform_of_unopened c fun t ht => unopened t (by simp [Comp.data, ht]),
        uniform_of_unopened d fun t ht => unopened t (by simp [Comp.data, ht])⟩
  | .fail, _ => trivial
  | .query _ _ k, unopened => uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])
  | .add _ _ k, unopened => uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])
  | .remove _ _ k, unopened => uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])
  | .new s x k, unopened =>
      ⟨⟨[], fun y hy _ => unopened x (by simp [Comp.data]) y hy,
          fun t ht y hy _ => unopened t (by simp [Comp.data, ht]) y hy⟩,
        uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])⟩
  | .check _ k, unopened => uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])
  | .delay s x c k, unopened =>
      ⟨⟨[], fun y hy _ => unopened x (by simp [Comp.data]) y hy,
          fun t ht y hy _ => unopened t (by simp [Comp.data, ht]) y hy⟩,
        uniform_of_unopened c fun t ht => unopened t (by simp [Comp.data, ht]),
        uniform_of_unopened k fun t ht => unopened t (by simp [Comp.data, ht])⟩
  | .force _, _ => trivial

/-- **Scoped text is unopened**: the scope clause of well-formedness names only unopened names. -/
theorem unopened_of_scoped :
    ∀ (c : Comp κ Γ star Ty) (allowed : List κ.Site), c.Scoped allowed →
      ∀ t ∈ c.data, ∀ x ∈ support t, x.scopes = []
  | .ret _, _, sc, t, member, x, hx => by
      simp only [Comp.data, List.mem_singleton] at member; subst member; exact (sc x hx).1
  | .apply _, _, sc, t, member, x, hx => by
      simp only [Comp.data, List.mem_singleton] at member; subst member; exact (sc x hx).1
  | .run _, _, sc, t, member, x, hx => by
      simp only [Comp.data, List.mem_singleton] at member; subst member; exact (sc x hx).1
  | .let_ s p c k, allowed, ⟨hc, hp, hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inC | inK
      · exact (hp x hx).1
      · exact unopened_of_scoped c allowed hc t inC x hx
      · exact unopened_of_scoped k (s :: allowed) hk t inK x hx
  | .choice c d, allowed, ⟨hc, hd⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_append] at member
      rcases member with inC | inD
      · exact unopened_of_scoped c allowed hc t inC x hx
      · exact unopened_of_scoped d allowed hd t inD x hx
  | .fail, _, _, t, member, _, _ => by simp [Comp.data] at member
  | .query _ _ k, allowed, ⟨hs, hp, hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons] at member
      rcases member with rfl | rfl | inK
      · exact (hs x hx).1
      · exact (hp x hx).1
      · exact unopened_of_scoped k allowed hk t inK x hx
  | .add _ _ k, allowed, ⟨hs, hp, hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons] at member
      rcases member with rfl | rfl | inK
      · exact (hs x hx).1
      · exact (hp x hx).1
      · exact unopened_of_scoped k allowed hk t inK x hx
  | .remove _ _ k, allowed, ⟨hs, hp, hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons] at member
      rcases member with rfl | rfl | inK
      · exact (hs x hx).1
      · exact (hp x hx).1
      · exact unopened_of_scoped k allowed hk t inK x hx
  | .new s _ k, allowed, ⟨hx', hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons] at member
      rcases member with rfl | inK
      · exact (hx' x hx).1
      · exact unopened_of_scoped k (s :: allowed) hk t inK x hx
  | .check _ k, allowed, hk, t, member, x, hx => unopened_of_scoped k allowed hk t member x hx
  | .delay s _ c k, allowed, ⟨hc, hx', hk⟩, t, member, x, hx => by
      simp only [Comp.data, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inC | inK
      · exact (hx' x hx).1
      · exact unopened_of_scoped c allowed hc t inC x hx
      · exact unopened_of_scoped k (s :: allowed) hk t inK x hx
  | .force _, _, sc, t, member, x, hx => by
      simp only [Comp.data, List.mem_singleton] at member; subst member; exact (sc x hx).1

/-! ## Alternatives -/

/-- Uniform binders in a frame. -/
def FrameUniform : Frame κ Γ star Ty → Prop
  | .bindTo s p k => BinderUniform s p k ∧ Uniform k
  | .checkAt _ => True
  | .memo _ => True

/-- Uniform binders in a focus. -/
def FocusUniform : Focus κ Γ star Ty → Prop
  | .eval c => Uniform c
  | .value _ => True
  | .refused _ _ => True

/-- **An alternative with uniform binders**: its focus, every frame, every pending cell. -/
def BranchUniform (b : Branch κ Γ star Ty) : Prop :=
  FocusUniform b.focus ∧ (∀ f ∈ b.frames, FrameUniform f) ∧ ∀ e ∈ b.pending, Uniform e.2

/-! ## The law of readings -/

/-- **A hygienic reading of text as code**: the code it makes of a text has no binder at the site of a
name of that text, and its binders are uniform. -/
structure ReadingHygienic (reflect : Data κ Γ star → Comp κ Γ star Ty) : Prop where
  apart : ∀ t, ∀ x ∈ support t, κ.site x.key ∉ (reflect t).sites
  uniform : ∀ t, Uniform (reflect t)

/-! ## The invariant along runs -/

variable {D : Discipline S Γ star} {P : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **A move keeps binders uniform**, for a program whose right-hand sides have uniform binders and a
reading whose code has uniform binders. -/
theorem move_uniform (rhs : ∀ e ∈ P.equations, Uniform e.rhs) (reading : ∀ t, Uniform (P.reflect t))
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (moved : Move D P supply w b w' bs) (ub : BranchUniform b) : ∀ b' ∈ bs, BranchUniform b' := by
  obtain ⟨uFocus, uFrames, uPending⟩ := ub
  intro b' child
  cases moved with
  | ret K t fs ps =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, uFrames, uPending⟩
  | apply K t fs ps matched =>
      obtain ⟨e, member, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
      exact ⟨uniform_byLevel (fun _ L => w.scope :: L) e.rhs (rhs e member), uFrames, uPending⟩
  | unmatched K t fs ps none =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, uFrames, uPending⟩
  | run K t fs ps θ principal =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨reading _, uFrames, uPending⟩
  | letStart K s p c k fs ps =>
      rw [Multiset.mem_singleton.mp child]
      obtain ⟨b, hc, hk⟩ := uFocus
      refine ⟨hc, fun f member => ?_, uPending⟩
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨b, hk⟩
      · exact uFrames f inside
  | letBind K v s p k fs ps =>
      rw [Multiset.mem_singleton.mp child]
      obtain ⟨_, hk⟩ := uFrames _ List.mem_cons_self
      exact ⟨uniform_byLevel (fun s' L => if s' = s then w.scope :: L else L) k hk,
        fun f member => uFrames f (List.mem_cons_of_mem _ member), uPending⟩
  | choice K c d fs ps =>
      obtain ⟨hc, hd⟩ := uFocus
      rcases Multiset.mem_cons.mp child with rfl | other
      · exact ⟨hc, uFrames, uPending⟩
      · rw [Multiset.mem_singleton.mp other]
        exact ⟨hd, uFrames, uPending⟩
  | fail K fs ps => simp at child
  | query K sp p k fs ps h addressed =>
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp child
      exact ⟨uFocus, uFrames, uPending⟩
  | add K sp t k fs ps h addressed =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨uFocus, uFrames, uPending⟩
  | remove K sp t k fs ps h addressed r rest split fits =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨uFocus, uFrames, uPending⟩
  | removeMissing K sp t k fs ps h addressed none =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨uFocus, uFrames, uPending⟩
  | new K s x k fs ps =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨uniform_byLevel (fun s' L => if s' = s then w.scope :: L else L) k uFocus.2, uFrames, uPending⟩
  | checkStart K T c fs ps =>
      rw [Multiset.mem_singleton.mp child]
      refine ⟨uFocus, fun f member => ?_, uPending⟩
      rcases List.mem_cons.mp member with rfl | inside
      · trivial
      · exact uFrames f inside
  | admitted K v T fs ps all =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, fun f member => uFrames f (List.mem_cons_of_mem _ member), uPending⟩
  | refused K v T fs ps none =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, fun f member => (by cases member), uPending⟩
  | delay K s x c k fs ps =>
      rw [Multiset.mem_singleton.mp child]
      obtain ⟨_, hc, hk⟩ := uFocus
      refine ⟨uniform_byLevel (fun s' L => if s' = s then w.scope :: L else L) k hk, uFrames, ?_⟩
      intro e member
      rcases List.mem_cons.mp member with rfl | inside
      · exact hc
      · exact uPending e inside
  | forcePending K x cell c fs before after bound =>
      rw [Multiset.mem_singleton.mp child]
      refine ⟨uPending (cell, c) (by simp), fun f member => ?_, fun e member => ?_⟩
      · rcases List.mem_cons.mp member with rfl | inside
        · trivial
        · exact uFrames f inside
      · rcases List.mem_append.mp member with inBefore | inAfter
        · exact uPending e (List.mem_append_left _ inBefore)
        · exact uPending e (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
  | forceDone K x fs ps none =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, uFrames, uPending⟩
  | memo K v x fs ps =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨trivial, fun f member => uFrames f (List.mem_cons_of_mem _ member), uPending⟩

theorem step_uniform (rhs : ∀ e ∈ P.equations, Uniform e.rhs) (reading : ∀ t, Uniform (P.reflect t))
    {C C' : Config κ Γ star D.Ty} (step : Step D P supply C C') (all : ∀ b ∈ C.branches, BranchUniform b) :
    ∀ b ∈ C'.branches, BranchUniform b := by
  cases step with
  | move w w' b rest bs live moved =>
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · exact move_uniform rhs reading moved (all b (Multiset.mem_cons_self _ _)) b' made
      · exact all b' (Multiset.mem_cons_of_mem kept)

/-- **Binders stay uniform along every run.** -/
theorem runs_uniform (rhs : ∀ e ∈ P.equations, Uniform e.rhs) (reading : ∀ t, Uniform (P.reflect t))
    {C C' : Config κ Γ star D.Ty} (runs : Runs D P supply C C') (all : ∀ b ∈ C.branches, BranchUniform b) :
    ∀ b ∈ C'.branches, BranchUniform b := by
  induction runs with
  | refl => exact all
  | tail _ step ih => exact step_uniform rhs reading step ih

/-- **No name of a site occurs at another level in a binder of that site, along every run** of a
well-formed program and query whose reading of text as code makes code with uniform binders (the
`uniform` clause of `ReadingHygienic`). -/
theorem uniform_along_runs [DecidableEq κ.Key] (wf : WellFormed P) {site : κ.Site}
    {q : Comp κ Γ star D.Ty} (qwf : QueryWellFormed P site q) (reading : ∀ t, Uniform (P.reflect t))
    (spaces : Term S Γ star → Multiset (Row κ Γ star)) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) : ∀ b ∈ C.branches, BranchUniform b := by
  refine runs_uniform (fun e member => ?_) reading runs ?_
  · exact uniform_of_unopened e.rhs (unopened_of_scoped e.rhs [e.site] (wf.inScope e member).2)
  · intro b member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨uniform_of_unopened q (unopened_of_scoped q [site] qwf.inScope), fun f h => (by cases h),
      fun e h => (by cases h)⟩

/-- **At a bind, the opening renames names of one level only**: in a uniform frame `bindTo s p k`, every
name of site `s` in `p` and in `k` has the same scopes. -/
theorem bind_renames_level {s : κ.Site} {p : Data κ Γ star} {k : Comp κ Γ star Ty}
    (u : FrameUniform (Frame.bindTo s p k)) :
    ∃ L, ∀ t ∈ p :: k.data, ∀ x ∈ support t, κ.site x.key = s → x.scopes = L := by
  obtain ⟨⟨L, hp, hk⟩, _⟩ := u
  refine ⟨L, fun t member => ?_⟩
  rcases List.mem_cons.mp member with rfl | inside
  · exact hp
  · exact hk t inside

/-- **A code arrow's opening fixes the text it was read from**: under the `apart` clause, opening any
binder site of the code made from `t`, at any scope, leaves `t` as it is. So the renamings the code's
binders make at their binds never touch a name of the text. -/
theorem opening_fixes_text {reflect : Data κ Γ star → Comp κ Γ star Ty} (reading : ReadingHygienic reflect)
    (t : Data κ Γ star) {s : κ.Site} (site : s ∈ (reflect t).sites) (m : ℕ) :
    instantiate (openAt κ s m) t = t := by
  conv_rhs => rw [← instantiate_identity t]
  refine instantiate_congr _ _ t fun x member => ?_
  have other : κ.site x.key ≠ s := fun same => reading.apart t x member (same ▸ site)
  show generator (fam κ) ⟨if κ.site x.key = s then m :: x.scopes else x.scopes, x.key⟩ = generator (fam κ) x
  rw [if_neg other]

/-! ## The dereferencing choice -/

/-- **Two most general solutions dereference a text to mutual instances that the store entails
equal.** So the choice of `θ` in `run` changes the text only within its class modulo the store. -/
theorem principal_texts {K : List (Constraint κ Γ star)} {θ₁ θ₂ : Assignment (fam κ) (fam κ)}
    (p₁ : Principal K θ₁) (p₂ : Principal K θ₂) (t : Data κ Γ star) :
    instantiate θ₂ (instantiate θ₁ t) = instantiate θ₂ t ∧
      instantiate θ₁ (instantiate θ₂ t) = instantiate θ₁ t ∧
      EntailsEq K (instantiate θ₁ t) (instantiate θ₂ t) := by
  have absorb : ∀ {θ θ' : Assignment (fam κ) (fam κ)}, Principal K θ → Models θ' K →
      Assignment.compose θ' θ = θ' := fun {θ θ'} principal solved => by
    funext name
    exact principal.2 (fam κ) θ' solved name
  refine ⟨?_, ?_, ?_⟩
  · rw [← Assignment.instantiate_compose, absorb p₁ p₂.1]
  · rw [← Assignment.instantiate_compose, absorb p₂ p₁.1]
  · intro X target σ solved
    have one : Assignment.compose σ θ₁ = σ := by
      funext name
      exact p₁.2 target σ solved name
    have two : Assignment.compose σ θ₂ = σ := by
      funext name
      exact p₂.2 target σ solved name
    rw [← Assignment.instantiate_compose, one, ← Assignment.instantiate_compose, two]

#print axioms support_relabel
#print axioms uniform_byLevel
#print axioms uniform_of_unopened
#print axioms unopened_of_scoped
#print axioms move_uniform
#print axioms runs_uniform
#print axioms uniform_along_runs
#print axioms bind_renames_level
#print axioms opening_fixes_text
#print axioms principal_texts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Hygiene
