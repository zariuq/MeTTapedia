import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

/-!
# Well-formedness of core programs

Three clauses, each decided by a computation on the syntax:

* **Patterns** (`AllPatterns`): an equation's left-hand side and every pattern of its right-hand side
  (arrows, queries, removals, cells) are in the second-order pattern class
  (`ContextualPatternFragment.Pattern`: every unknown applied to distinct bound variables), decided by
  the tree's checker (`check_iff`); any other datum may apply an unknown to arbitrary data only when
  a pattern of the same equation names that unknown (`flexOk`, as `($F $a)` after `(lam x. $F x)`).
  This clause is syntactic. It does **not** make every store of a run have a most general solution:
  unification is two-way, so a call whose own unknown meets `(lam x. $F x)` leaves `$F` undetermined,
  and `($F $a)` then puts `$F` applied to a datum into the store, where two incomparable solutions
  can exist and a `run` waits (`ExampleWaiting.deadlock_observed`). Waiting is shown by the
  observation (`Observation.observe`), not counted as failure. An unknown of a left-hand side applied
  to anything else is outside the clause (the controls are in `ExamplesWellFormed`).
* **Scope** (`Comp.Scoped`): the settled rule for arrows, read on sites. An equation owns the names of
  its site; a `let`, `new` or `delay` owns the names of its own site, which occur only in its pattern
  and its body, never in the computation it binds; a name from an enclosing site may occur in a
  pattern (it crosses: the arrow refines the outer name instead of introducing one); relations
  (`query`, `remove`) introduce nothing. All names of program text are unopened, so every binder of a
  run stays uniform: no name of its site at another level sits in its pattern or body
  (`Hygiene.uniform_along_runs`, which also asks the reading of text as code to be hygienic).
* **Sites** (`SitesDistinct`): no two binders share a site. Opening a site renames all its names, so a
  shared site would let an inner arrow capture the outer one's names (the control is in
  `ExamplesWellFormed`). Code made from text at run time is not program text: the reading keeps its
  arrows' sites apart from the names of the text it reads (`Hygiene.ReadingHygienic`).

Declarations are a surface notion; their consistency is a clause of the surface well-formedness
(`Elaboration.DeclarationsConsistent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

/-! ## Scope -/

/-- Every name of the datum is unopened and belongs to one of the allowed sites. -/
def NamesIn (allowed : List κ.Site) (t : Data κ Γ star) : Prop :=
  ∀ x ∈ support t, x.scopes = [] ∧ κ.site x.key ∈ allowed

instance (allowed : List κ.Site) (t : Data κ Γ star) : Decidable (NamesIn allowed t) := by
  unfold NamesIn; infer_instance

/-- **Lexical scope by sites.** `allowed` lists the sites enclosing the position. -/
def Comp.Scoped (allowed : List κ.Site) : Comp κ Γ star Ty → Prop
  | .ret t => NamesIn allowed t
  | .apply t => NamesIn allowed t
  | .run t => NamesIn allowed t
  | .let_ s p c k => c.Scoped allowed ∧ NamesIn (s :: allowed) p ∧ k.Scoped (s :: allowed)
  | .choice c d => c.Scoped allowed ∧ d.Scoped allowed
  | .fail => True
  | .query sp p k => NamesIn allowed sp ∧ NamesIn allowed p ∧ k.Scoped allowed
  | .add sp t k => NamesIn allowed sp ∧ NamesIn allowed t ∧ k.Scoped allowed
  | .remove sp t k => NamesIn allowed sp ∧ NamesIn allowed t ∧ k.Scoped allowed
  | .new s x k => NamesIn (s :: allowed) x ∧ k.Scoped (s :: allowed)
  | .check _ k => k.Scoped allowed
  | .delay s x c k => c.Scoped allowed ∧ NamesIn (s :: allowed) x ∧ k.Scoped (s :: allowed)
  | .force x => NamesIn allowed x

instance Comp.decScoped : (c : Comp κ Γ star Ty) → (allowed : List κ.Site) → Decidable (c.Scoped allowed)
  | .ret t, a => inferInstanceAs (Decidable (NamesIn a t))
  | .apply t, a => inferInstanceAs (Decidable (NamesIn a t))
  | .run t, a => inferInstanceAs (Decidable (NamesIn a t))
  | .let_ s _ c k, a =>
      letI := Comp.decScoped c a
      letI := Comp.decScoped k (s :: a)
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .choice c d, a =>
      letI := Comp.decScoped c a
      letI := Comp.decScoped d a
      inferInstanceAs (Decidable (_ ∧ _))
  | .fail, _ => isTrue trivial
  | .query _ _ k, a =>
      letI := Comp.decScoped k a
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .add _ _ k, a =>
      letI := Comp.decScoped k a
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .remove _ _ k, a =>
      letI := Comp.decScoped k a
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .new s _ k, a =>
      letI := Comp.decScoped k (s :: a)
      inferInstanceAs (Decidable (_ ∧ _))
  | .check _ k, a => Comp.decScoped k a
  | .delay s _ c k, a =>
      letI := Comp.decScoped c a
      letI := Comp.decScoped k (s :: a)
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .force x, a => inferInstanceAs (Decidable (NamesIn a x))

/-! ## Sites -/

/-- The binder sites of a computation, outermost first. -/
def Comp.sites : Comp κ Γ star Ty → List κ.Site
  | .let_ s _ c k => s :: (c.sites ++ k.sites)
  | .choice c d => c.sites ++ d.sites
  | .query _ _ k => k.sites
  | .add _ _ k => k.sites
  | .remove _ _ k => k.sites
  | .new s _ k => s :: k.sites
  | .check _ k => k.sites
  | .delay s _ c k => s :: (c.sites ++ k.sites)
  | _ => []

/-- The sites of a program: each equation's own, then its binders'. -/
def Program.sites (P : Program κ Γ star Ty) : List κ.Site :=
  P.equations.flatMap fun e => e.site :: e.rhs.sites

/-! ## Patterns -/

/-- Every datum of a computation. -/
def Comp.data : Comp κ Γ star Ty → List (Data κ Γ star)
  | .ret t => [t]
  | .apply t => [t]
  | .run t => [t]
  | .let_ _ p c k => p :: (c.data ++ k.data)
  | .choice c d => c.data ++ d.data
  | .fail => []
  | .query sp p k => sp :: p :: k.data
  | .add sp t k => sp :: t :: k.data
  | .remove sp t k => sp :: t :: k.data
  | .new _ x k => x :: k.data
  | .check _ k => k.data
  | .delay _ x c k => x :: (c.data ++ k.data)
  | .force x => [x]

/-- The datum is in the second-order pattern class. -/
abbrev IsPattern (t : Data κ Γ star) : Prop := ContextualPatternFragment.Pattern S (fam κ) t

instance (t : Data κ Γ star) : Decidable (IsPattern t) :=
  decidable_of_iff _ (ContextualPatternFragment.check_iff t)

/-- The data a computation unifies two ways as patterns: its arrows' patterns, query patterns, the
atoms it removes, the handles and cells it opens. -/
def Comp.patterns : Comp κ Γ star Ty → List (Data κ Γ star)
  | .let_ _ p c k => p :: (c.patterns ++ k.patterns)
  | .choice c d => c.patterns ++ d.patterns
  | .query _ p k => p :: k.patterns
  | .add _ _ k => k.patterns
  | .remove _ t k => t :: k.patterns
  | .new _ x k => x :: k.patterns
  | .check _ k => k.patterns
  | .delay _ x c k => x :: (c.patterns ++ k.patterns)
  | _ => []

mutual
/-- Every unknown applied to something other than distinct bound variables is `bound` (it is
determined by a pattern before the datum is used). -/
def flexOk (bound : Name κ → Bool) : {Δ : Ctx S} → {s : S.Srt} → Term (signature S (fam κ)) Δ s → Bool
  | _, _, .var _ => true
  | _, _, .op (.inl _) args => flexOkArgs bound args
  | _, _, .op (.inr (.mk x)) args =>
      bound x && flexOkArgs bound args || ContextualPatternFragment.check (.op (.inr (.mk x)) args)

def flexOkArgs (bound : Name κ → Bool) : {arities : List (MetaArity S)} → {Δ : Ctx S} →
    Args (signature S (fam κ)) arities Δ → Bool
  | _, _, .nil => true
  | _, _, .cons head tail => flexOk bound head && flexOkArgs bound tail
end

variable [DecidableEq κ.Key]

/-- The names an equation's patterns determine: those of its left-hand side and of the patterns of
its right-hand side. -/
def Equation.determined (e : Equation κ Γ star Ty) (x : Name κ) : Bool :=
  decide (x ∈ support e.lhs) || e.rhs.patterns.any fun p => decide (x ∈ support p)

/-- **The pattern clause**: the left-hand side and every pattern of the right-hand side are patterns,
and every other datum applies only determined unknowns to anything but distinct bound variables. -/
def Equation.AllPatterns (e : Equation κ Γ star Ty) : Prop :=
  IsPattern e.lhs ∧ (∀ p ∈ e.rhs.patterns, IsPattern p) ∧ ∀ t ∈ e.rhs.data, flexOk e.determined t = true

instance (e : Equation κ Γ star Ty) : Decidable e.AllPatterns := by
  unfold Equation.AllPatterns; infer_instance

/-! ## Programs -/

/-- An equation is scoped: its left-hand side names only its own site, and its right-hand side is
lexically scoped from there. -/
def Equation.Scoped (e : Equation κ Γ star Ty) : Prop :=
  NamesIn [e.site] e.lhs ∧ e.rhs.Scoped [e.site]

instance (e : Equation κ Γ star Ty) : Decidable e.Scoped := by
  unfold Equation.Scoped; infer_instance

/-- **Well-formed core programs.** -/
structure WellFormed (P : Program κ Γ star Ty) : Prop where
  patterns : ∀ e ∈ P.equations, e.AllPatterns
  inScope : ∀ e ∈ P.equations, e.Scoped
  distinctSites : P.sites.Nodup

theorem wellFormed_iff (P : Program κ Γ star Ty) :
    WellFormed P ↔ (∀ e ∈ P.equations, e.AllPatterns) ∧ (∀ e ∈ P.equations, e.Scoped) ∧ P.sites.Nodup :=
  ⟨fun wf => ⟨wf.patterns, wf.inScope, wf.distinctSites⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

instance (P : Program κ Γ star Ty) : Decidable (WellFormed P) :=
  decidable_of_iff _ (wellFormed_iff P).symm

/-- A well-formed query: its names belong to its own site and it is scoped from there, its data are
patterns, and its binders' sites are distinct from each other and from the program's. -/
structure QueryWellFormed (P : Program κ Γ star Ty) (site : κ.Site) (q : Comp κ Γ star Ty) : Prop where
  patterns : (∀ p ∈ q.patterns, IsPattern p) ∧
    ∀ t ∈ q.data, flexOk (fun x => q.patterns.any fun p => decide (x ∈ support p)) t = true
  inScope : q.Scoped [site]
  distinctSites : (site :: q.sites ++ P.sites).Nodup

theorem queryWellFormed_iff (P : Program κ Γ star Ty) (site : κ.Site) (q : Comp κ Γ star Ty) :
    QueryWellFormed P site q ↔
      ((∀ p ∈ q.patterns, IsPattern p) ∧
        ∀ t ∈ q.data, flexOk (fun x => q.patterns.any fun p => decide (x ∈ support p)) t = true) ∧
      q.Scoped [site] ∧ (site :: q.sites ++ P.sites).Nodup :=
  ⟨fun wf => ⟨wf.patterns, wf.inScope, wf.distinctSites⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

instance (P : Program κ Γ star Ty) (site : κ.Site) (q : Comp κ Γ star Ty) :
    Decidable (QueryWellFormed P site q) :=
  decidable_of_iff _ (queryWellFormed_iff P site q).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage
