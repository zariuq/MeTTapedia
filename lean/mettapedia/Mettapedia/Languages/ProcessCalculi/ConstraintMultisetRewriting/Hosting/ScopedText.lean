import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowRuns

/-!
# Run-time scoping: the names a `let` binds stay inside it

The source opens the names of a `let` at the bind; the translation opens them when the equation that
contains the `let` is used. They agree when the names a pending `let` binds occur nowhere else
(`FramePrivate`). This module gives the tools to prove that this holds along every run.

* **Supports under relabelling** (`support_relabel`): a copy at a scope or an opening of a site
  (both are `relabel`) sends the names of a datum to their relabelled names, and adds none.
* **Run-time scoping at a level** (`RScoped ok L c`): outside every `let`, the names of `c` satisfy
  `ok`; inside a `let` of site `s`, a name is of another site and satisfies `ok`, or it is one of the
  `let`'s own names: of site `s`, with scopes `L` (`Own s L`). It is monotone in `ok`
  (`RScoped_mono`), kept by relabellings that move own names from one level to one level
  (`RScoped_relabel`), and it bounds every name of the computation (`RScoped_names`).
* **The text lemma** (`RScoped_text`): a computation with arrows scoped by the source's rule
  (`Comp.Scoped`), with binder sites distinct from each other and from the enclosing ones, is scoped
  at run time at the level `[]`. So a copy at scope `n` of an equation's right-hand side is scoped at
  the level `[n]` (`RScoped_copy`), and opening a pending `let` at a bind keeps its body scoped
  (`RScoped_open`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {Ty : Type}

/-! ## Supports under relabelling -/

section Relabel

variable (g : Name κ → List ℕ)

/-- Where a relabelling sends a name: new scopes, the same key. -/
def relabelName (x : Name κ) : Name κ := ⟨g x, x.key⟩

@[simp] theorem relabelName_key (x : Name κ) : (relabelName g x).key = x.key := rfl

@[simp] theorem relabelName_scopes (x : Name κ) : (relabelName g x).scopes = g x := rfl

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

theorem mem_support_relabel {Δ : Ctx S} {sort : S.Srt} {t : Term (signature S (fam κ)) Δ sort}
    {x : Name κ} (member : x ∈ support (instantiate (relabel κ g) t)) :
    ∃ y ∈ support t, relabelName g y = x := by
  rw [support_relabel] at member
  exact List.mem_map.mp member

end Relabel

/-- A copy at scope `n` is a relabelling. -/
theorem copyAt_eq_relabel (n : ℕ) : copyAt κ n = relabel κ (fun name => n :: name.scopes) := rfl

/-- Opening the site `s` at scope `n` is a relabelling. -/
theorem openAt_eq_relabel (s : κ.Site) (n : ℕ) :
    openAt κ s n =
      relabel κ (fun name => if κ.site name.key = s then n :: name.scopes else name.scopes) :=
  rfl

/-- Opening a site leaves the names of other sites as they are. -/
theorem relabelName_open_other {s : κ.Site} {n : ℕ} {y : Name κ} (other : κ.site y.key ≠ s) :
    relabelName (fun name => if κ.site name.key = s then n :: name.scopes else name.scopes) y = y := by
  simp [relabelName, other]

/-- Opening a site prefixes the scope to the names of that site. -/
theorem relabelName_open_same {s : κ.Site} {n : ℕ} {y : Name κ} (same : κ.site y.key = s) :
    relabelName (fun name => if κ.site name.key = s then n :: name.scopes else name.scopes) y =
      ⟨n :: y.scopes, y.key⟩ := by
  simp [relabelName, same]

/-! ## Own names and levels -/

/-- **The names of site `s` at level `L`.** -/
def Own (s : κ.Site) (L : List ℕ) (x : Name κ) : Prop := κ.site x.key = s ∧ x.scopes = L

/-- A level below scope `n`: empty, or headed by a scope below `n`. -/
def LevelBelow (n : ℕ) (L : List ℕ) : Prop := ∀ m, L.head? = some m → m < n

theorem LevelBelow.mono {n n' : ℕ} {L : List ℕ} (below : LevelBelow n L) (le : n ≤ n') :
    LevelBelow n' L :=
  fun m head => Nat.lt_of_lt_of_le (below m head) le

/-- A level below `n` is not a level headed by `n`. -/
theorem LevelBelow.ne_cons {n : ℕ} {L : List ℕ} (below : LevelBelow n L) (L' : List ℕ) :
    L ≠ n :: L' := by
  rintro rfl
  exact Nat.lt_irrefl n (below n rfl)

/-- Inside a `let` of site `s` at level `L`: a name of another site that `ok` allows, or an own name. -/
def insideLet (ok : Name κ → Prop) (s : κ.Site) (L : List ℕ) (x : Name κ) : Prop :=
  (ok x ∧ κ.site x.key ≠ s) ∨ Own s L x

theorem insideLet_mono {ok ok' : Name κ → Prop} (s : κ.Site) (L : List ℕ) (more : ∀ x, ok x → ok' x)
    {x : Name κ} (inside : insideLet ok s L x) : insideLet ok' s L x := by
  rcases inside with ⟨allowed, other⟩ | own
  · exact .inl ⟨more x allowed, other⟩
  · exact .inr own

/-- A name inside a `let` of site `s` that is of site `s` is an own name. -/
theorem insideLet_same {ok : Name κ → Prop} {s : κ.Site} {L : List ℕ} {x : Name κ}
    (inside : insideLet ok s L x) (same : κ.site x.key = s) : Own s L x := by
  rcases inside with ⟨_, other⟩ | own
  · exact absurd same other
  · exact own

/-! ## Run-time scoping -/

/-- **Run-time scoping of a computation at a level.** -/
def RScoped : (Name κ → Prop) → List ℕ → Comp κ Γ star Ty → Prop
  | ok, _, .ret t => ∀ x ∈ support t, ok x
  | ok, _, .apply t => ∀ x ∈ support t, ok x
  | ok, L, .let_ s p c k => RScoped ok L c ∧ (∀ x ∈ support p, insideLet ok s L x) ∧
      RScoped (insideLet ok s L) L k
  | ok, L, .choice c d => RScoped ok L c ∧ RScoped ok L d
  | _, _, .fail => True
  | _, _, .run _ => False
  | _, _, .query _ _ _ => False
  | _, _, .add _ _ _ => False
  | _, _, .remove _ _ _ => False
  | _, _, .new _ _ _ => False
  | _, _, .check _ _ => False
  | _, _, .delay _ _ _ _ => False
  | _, _, .force _ => False

theorem RScoped_mono : ∀ (c : Comp κ Γ star Ty) {ok ok' : Name κ → Prop} {L : List ℕ},
    (∀ x, ok x → ok' x) → RScoped ok L c → RScoped ok' L c
  | .ret _, _, _, _, more, within => fun x member => more x (within x member)
  | .apply _, _, _, _, more, within => fun x member => more x (within x member)
  | .let_ s _ c k, _, _, L, more, ⟨sc, sp, sk⟩ =>
      ⟨RScoped_mono c more sc, fun x member => insideLet_mono s L more (sp x member),
        RScoped_mono k (fun _ inside => insideLet_mono s L more inside) sk⟩
  | .choice c d, _, _, _, more, ⟨sc, sd⟩ => ⟨RScoped_mono c more sc, RScoped_mono d more sd⟩
  | .fail, _, _, _, _, _ => trivial
  | .run _, _, _, _, _, within => within.elim
  | .query _ _ _, _, _, _, _, within => within.elim
  | .add _ _ _, _, _, _, _, within => within.elim
  | .remove _ _ _, _, _, _, _, within => within.elim
  | .new _ _ _, _, _, _, _, within => within.elim
  | .check _ _, _, _, _, _, within => within.elim
  | .delay _ _ _ _, _, _, _, _, within => within.elim
  | .force _, _, _, _, _, within => within.elim

/-- A computation scoped at run time is a computation of the fragment with arrows. -/
theorem RScoped.arrow : ∀ {c : Comp κ Γ star Ty} {ok : Name κ → Prop} {L : List ℕ},
    RScoped ok L c → ArrowComp c
  | .ret _, _, _, _ => trivial
  | .apply _, _, _, _ => trivial
  | .let_ _ _ _ _, _, _, ⟨sc, _, sk⟩ => ⟨RScoped.arrow sc, RScoped.arrow sk⟩
  | .choice _ _, _, _, ⟨sc, sd⟩ => ⟨RScoped.arrow sc, RScoped.arrow sd⟩
  | .fail, _, _, _ => trivial
  | .run _, _, _, within => within.elim
  | .query _ _ _, _, _, within => within.elim
  | .add _ _ _, _, _, within => within.elim
  | .remove _ _ _, _, _, within => within.elim
  | .new _ _ _, _, _, within => within.elim
  | .check _ _, _, _, within => within.elim
  | .delay _ _ _ _, _, _, within => within.elim
  | .force _, _, _, within => within.elim

/-- **Every name of a scoped computation** is allowed, or is an own name of one of its `let`s. -/
theorem RScoped_names : ∀ (c : Comp κ Γ star Ty) {ok : Name κ → Prop} {L : List ℕ},
    RScoped ok L c → ∀ t ∈ c.data, ∀ x ∈ support t, ok x ∨ ∃ s' ∈ c.sites, Own s' L x
  | .ret _, _, _, within, t, member, x, inside => by
      simp only [Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within x inside)
  | .apply _, _, _, within, t, member, x, inside => by
      simp only [Comp.data, List.mem_singleton] at member
      subst member
      exact .inl (within x inside)
  | .let_ s p c k, _, _, ⟨sc, sp, sk⟩, t, member, x, inside => by
      simp only [Comp.data, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inC | inK
      · rcases sp x inside with ⟨allowed, _⟩ | own
        · exact .inl allowed
        · exact .inr ⟨s, by simp [Comp.sites], own⟩
      · rcases RScoped_names c sc t inC x inside with allowed | ⟨s', member', own⟩
        · exact .inl allowed
        · exact .inr ⟨s', by simp [Comp.sites, member'], own⟩
      · rcases RScoped_names k sk t inK x inside with (⟨allowed, _⟩ | own) | ⟨s', member', own⟩
        · exact .inl allowed
        · exact .inr ⟨s, by simp [Comp.sites], own⟩
        · exact .inr ⟨s', by simp [Comp.sites, member'], own⟩
  | .choice c d, _, _, ⟨sc, sd⟩, t, member, x, inside => by
      simp only [Comp.data, List.mem_append] at member
      rcases member with inC | inD
      · rcases RScoped_names c sc t inC x inside with allowed | ⟨s', member', own⟩
        · exact .inl allowed
        · exact .inr ⟨s', by simp [Comp.sites, member'], own⟩
      · rcases RScoped_names d sd t inD x inside with allowed | ⟨s', member', own⟩
        · exact .inl allowed
        · exact .inr ⟨s', by simp [Comp.sites, member'], own⟩
  | .fail, _, _, _, t, member, _, _ => by simp [Comp.data] at member
  | .run _, _, _, within, _, _, _, _ => within.elim
  | .query _ _ _, _, _, within, _, _, _, _ => within.elim
  | .add _ _ _, _, _, within, _, _, _, _ => within.elim
  | .remove _ _ _, _, _, within, _, _, _, _ => within.elim
  | .new _ _ _, _, _, within, _, _, _, _ => within.elim
  | .check _ _, _, _, within, _, _, _, _ => within.elim
  | .delay _ _ _ _, _, _, within, _, _, _, _ => within.elim
  | .force _, _, _, within, _, _, _, _ => within.elim

theorem sites_mapData (f : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, (c.mapData f).sites = c.sites
  | .ret _ => rfl
  | .apply _ => rfl
  | .run _ => rfl
  | .let_ _ _ c k => by simp only [Comp.mapData, Comp.sites, sites_mapData f c, sites_mapData f k]
  | .choice c d => by simp only [Comp.mapData, Comp.sites, sites_mapData f c, sites_mapData f d]
  | .fail => rfl
  | .query _ _ k => by simp only [Comp.mapData, Comp.sites, sites_mapData f k]
  | .add _ _ k => by simp only [Comp.mapData, Comp.sites, sites_mapData f k]
  | .remove _ _ k => by simp only [Comp.mapData, Comp.sites, sites_mapData f k]
  | .new _ _ k => by simp only [Comp.mapData, Comp.sites, sites_mapData f k]
  | .check _ k => by simp only [Comp.mapData, Comp.sites, sites_mapData f k]
  | .delay _ _ c k => by simp only [Comp.mapData, Comp.sites, sites_mapData f c, sites_mapData f k]
  | .force _ => rfl

/-- **A relabelling keeps a computation scoped**, when it sends allowed names to allowed names and the
own names at the level `L` of every `let` of the computation to the level `L'`. -/
theorem RScoped_relabel (g : Name κ → List ℕ) :
    ∀ (c : Comp κ Γ star Ty) {ok ok' : Name κ → Prop} {L L' : List ℕ},
      RScoped ok L c → (∀ y, ok y → ok' (relabelName g y)) →
      (∀ s' ∈ c.sites, ∀ y, Own s' L y → g y = L') →
      RScoped ok' L' (c.mapData (instantiate (relabel κ g)))
  | .ret _, _, _, _, _, within, allowed, _ => by
      intro x member
      obtain ⟨y, inside, rfl⟩ := mem_support_relabel g member
      exact allowed y (within y inside)
  | .apply _, _, _, _, _, within, allowed, _ => by
      intro x member
      obtain ⟨y, inside, rfl⟩ := mem_support_relabel g member
      exact allowed y (within y inside)
  | .let_ s p c k, ok, ok', L, L', ⟨sc, sp, sk⟩, allowed, levels => by
      have here : ∀ y, insideLet ok s L y → insideLet ok' s L' (relabelName g y) := by
        intro y inside
        rcases inside with ⟨yes, other⟩ | own
        · exact .inl ⟨allowed y yes, other⟩
        · exact .inr ⟨own.1, levels s (by simp [Comp.sites]) y own⟩
      refine ⟨RScoped_relabel g c sc allowed
          (fun s' member y own => levels s' (by simp [Comp.sites, member]) y own), ?_,
        RScoped_relabel g k sk here
          (fun s' member y own => levels s' (by simp [Comp.sites, member]) y own)⟩
      intro x member
      obtain ⟨y, inside, rfl⟩ := mem_support_relabel g member
      exact here y (sp y inside)
  | .choice c d, _, _, _, _, ⟨sc, sd⟩, allowed, levels =>
      ⟨RScoped_relabel g c sc allowed
          (fun s' member y own => levels s' (by simp [Comp.sites, member]) y own),
        RScoped_relabel g d sd allowed
          (fun s' member y own => levels s' (by simp [Comp.sites, member]) y own)⟩
  | .fail, _, _, _, _, _, _, _ => trivial
  | .run _, _, _, _, _, within, _, _ => within.elim
  | .query _ _ _, _, _, _, _, within, _, _ => within.elim
  | .add _ _ _, _, _, _, _, within, _, _ => within.elim
  | .remove _ _ _, _, _, _, _, within, _, _ => within.elim
  | .new _ _ _, _, _, _, _, within, _, _ => within.elim
  | .check _ _, _, _, _, _, within, _, _ => within.elim
  | .delay _ _ _ _, _, _, _, _, within, _, _ => within.elim
  | .force _, _, _, _, _, within, _, _ => within.elim

/-! ## The text lemma -/

/-- **Text scoped by the source's rule is scoped at run time at the level `[]`**, for computations
with arrows whose binder sites are distinct from each other and from the enclosing ones. -/
theorem RScoped_text : ∀ (c : Comp κ Γ star Ty) (allowed : List κ.Site), ArrowComp c →
    c.Scoped allowed → (c.sites ++ allowed).Nodup →
    RScoped (fun x => x.scopes = [] ∧ κ.site x.key ∈ allowed) [] c
  | .ret _, _, _, within, _ => within
  | .apply _, _, _, within, _ => within
  | .let_ s p c k, allowed, ⟨ac, ak⟩, ⟨sc, sp, sk⟩, distinct => by
      have whole : (s :: (c.sites ++ (k.sites ++ allowed))).Nodup := by
        simpa only [Comp.sites, List.cons_append, List.append_assoc] using distinct
      have cDistinct : (c.sites ++ allowed).Nodup :=
        whole.sublist (((List.sublist_append_right k.sites allowed).append_left c.sites).cons s)
      have kDistinct : (k.sites ++ s :: allowed).Nodup :=
        List.perm_middle.nodup_iff.mpr
          (whole.sublist ((List.sublist_append_right c.sites (k.sites ++ allowed)).cons_cons s))
      have enter : ∀ x, (x.scopes = [] ∧ κ.site x.key ∈ s :: allowed) →
          insideLet (fun x => x.scopes = [] ∧ κ.site x.key ∈ allowed) s [] x := by
        rintro x ⟨scope, site⟩
        by_cases here : κ.site x.key = s
        · exact .inr ⟨here, scope⟩
        · exact .inl ⟨⟨scope, (List.mem_cons.mp site).resolve_left here⟩, here⟩
      exact ⟨RScoped_text c allowed ac sc cDistinct, fun x member => enter x (sp x member),
        RScoped_mono k enter (RScoped_text k (s :: allowed) ak sk kDistinct)⟩
  | .choice c d, allowed, ⟨ac, ad⟩, ⟨sc, sd⟩, distinct => by
      have whole : (c.sites ++ (d.sites ++ allowed)).Nodup := by
        simpa only [Comp.sites, List.append_assoc] using distinct
      exact ⟨RScoped_text c allowed ac sc
          (whole.sublist ((List.sublist_append_right d.sites allowed).append_left c.sites)),
        RScoped_text d allowed ad sd
          (whole.sublist (List.sublist_append_right c.sites (d.sites ++ allowed)))⟩
  | .fail, _, _, _, _ => trivial
  | .run _, _, arrow, _, _ => arrow.elim
  | .query _ _ _, _, arrow, _, _ => arrow.elim
  | .add _ _ _, _, arrow, _, _ => arrow.elim
  | .remove _ _ _, _, arrow, _, _ => arrow.elim
  | .new _ _ _, _, arrow, _, _ => arrow.elim
  | .check _ _, _, arrow, _, _ => arrow.elim
  | .delay _ _ _ _, _, arrow, _, _ => arrow.elim
  | .force _, _, arrow, _, _ => arrow.elim

/-- **A copy at scope `n` of a scoped right-hand side is scoped at the level `[n]`**, with the
equation's own names at `[n]` allowed. -/
theorem RScoped_copy (e : SourceLanguage.Equation κ Γ star Ty) (n : ℕ) (arrow : ArrowComp e.rhs)
    (within : e.Scoped) (distinct : (e.site :: e.rhs.sites).Nodup) :
    RScoped (Own e.site [n]) [n] (e.rhs.inst (copyAt κ n)) := by
  have text := RScoped_text e.rhs [e.site] arrow within.2
    ((List.perm_append_singleton e.site e.rhs.sites).nodup_iff.mpr distinct)
  rw [copyAt_eq_relabel]
  refine RScoped_relabel _ e.rhs text ?_ ?_
  · rintro y ⟨scope, site⟩
    exact ⟨List.mem_singleton.mp site, by simp [scope]⟩
  · intro s' _ y own
    simp [own.2]

/-- The names of a copy at scope `n` of a scoped left-hand side are the equation's own names at `[n]`. -/
theorem support_copy_lhs (e : SourceLanguage.Equation κ Γ star Ty) (n : ℕ) (within : e.Scoped) :
    ∀ x ∈ support (instantiate (copyAt κ n) e.lhs), Own e.site [n] x := by
  intro x member
  rw [copyAt_eq_relabel] at member
  obtain ⟨y, inside, rfl⟩ := mem_support_relabel _ member
  obtain ⟨scope, site⟩ := within.1 y inside
  exact ⟨List.mem_singleton.mp site, by simp [scope]⟩

/-- **Opening a pending `let` keeps its body scoped**: its own names at `L` become names at `n :: L`. -/
theorem RScoped_open {ok : Name κ → Prop} {s : κ.Site} {L : List ℕ} (n : ℕ) {k : Comp κ Γ star Ty}
    (within : RScoped (insideLet ok s L) L k) (notInside : s ∉ k.sites) :
    RScoped (fun x => ok x ∨ Own s (n :: L) x) L (k.inst (openAt κ s n)) := by
  rw [openAt_eq_relabel]
  refine RScoped_relabel _ k within ?_ ?_
  · intro y inside
    rcases inside with ⟨allowed, other⟩ | ⟨same, scope⟩
    · rw [relabelName_open_other other]
      exact .inl allowed
    · rw [relabelName_open_same same]
      exact .inr ⟨same, by simp [scope]⟩
  · intro s' member y own
    have other : κ.site y.key ≠ s := by
      rw [own.1]
      rintro rfl
      exact notInside member
    simp [other, own.2]

/-- The names of an opened pattern: names of other sites as they were, or own names opened at `n`. -/
theorem support_open_pattern {ok : Name κ → Prop} {s : κ.Site} {L : List ℕ} (n : ℕ)
    {p : Data κ Γ star} (within : ∀ x ∈ support p, insideLet ok s L x) :
    ∀ x ∈ support (instantiate (openAt κ s n) p), ok x ∨ Own s (n :: L) x := by
  intro x member
  rw [openAt_eq_relabel] at member
  obtain ⟨y, inside, rfl⟩ := mem_support_relabel _ member
  rcases within y inside with ⟨allowed, other⟩ | ⟨same, scope⟩
  · rw [relabelName_open_other other]
    exact .inl allowed
  · rw [relabelName_open_same same]
    exact .inr ⟨same, by simp [scope]⟩

#print axioms support_relabel
#print axioms RScoped_names
#print axioms RScoped_relabel
#print axioms RScoped_text
#print axioms RScoped_copy
#print axioms RScoped_open
#print axioms support_open_pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
