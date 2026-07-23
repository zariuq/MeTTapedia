/-
# Output provenance for the unifier and the binding merge

The state-free evaluator argument needs one seam closed: that safe inputs to
the matching stack produce safe output bindings.  The naive statement — "every
value in an output binding is a SUBTERM of an input" — is FALSE, and the
reason determines this module's shape.

`Bindings.merge` folds `addVarBinding`, whose reconciliation path runs the
whole-system unifier (`reconcileAll` → `Unify.unifyRounds`) and rebuilds the
binding set from the resulting substitution.  The unifier ELIMINATES
variables: at each round it applies `[(x, t)]` to the remaining equations, so
a value in the final substitution is a subterm with substitutions applied,
not a subterm of any single input.  Composing `$x ↦ f($y)` with `$y ↦ g(c)`
yields `f(g(c))`, which occurs nowhere in the inputs.

So the reusable invariant is not "subterm" but a predicate closed under the
operations the pipeline actually performs.  Three requirements, each read off
the source rather than chosen for convenience:

* `hereditary` — immediate subterms of a safe expression are safe.  Without
  it `decomposeEq`/`decomposeList` break at the `expr`/`expr` case.
* `substClosed` — a safe substitution applied to a safe atom stays safe.
  Without it the elimination step at the heart of `unifyRounds` breaks.
* `varSafe` — variables are safe.  This one is easy to miss: the elimination
  step rebuilds each remaining equation as
  `(Subst.apply sub (Atom.var p.1), Subst.apply sub p.2)`, CONSTRUCTING a
  variable atom on the left.  Nothing in the input guarantees it, so it must
  be required.

Everything is generic in the predicate, so the same API serves any future
property of matcher output.  `StateOpFree` is instantiated at the end, where
each obligation is discharged by an existing lemma rather than re-proved.
-/
import Mettapedia.Languages.MeTTa.HE.StateFreePreservation
import MettaHyperonFull.Proofs.Basic

namespace Mettapedia.Languages.MeTTa.HE.MatcherProvenance

open Metta
open Mettapedia.Languages.MeTTa.HE.StateFreeFragment

/-! ## The safety interface -/

/-- The closure properties a predicate must have to survive the matching
pipeline.  All three are forced by the runtime; see the module docstring. -/
structure AtomSafety (P : Atom → Prop) : Prop where
  /-- Immediate subterms of a safe expression are safe. -/
  hereditary : ∀ atoms, P (.expr atoms) → ∀ a ∈ atoms, P a
  /-- A safe substitution applied to a safe atom is safe. -/
  substClosed : ∀ (s : Subst) (a : Atom),
    (∀ entry ∈ s, P entry.2) → P a → P (Subst.apply s a)
  /-- Variables are safe: the unifier constructs them during elimination. -/
  varSafe : ∀ name : VarName, P (.var name)

/-- Every value in a substitution is safe. -/
def SubstSafe (P : Atom → Prop) (s : Subst) : Prop := ∀ entry ∈ s, P entry.2

/-- Every atom recorded by a variable constraint is safe. -/
def ConstraintsSafe (P : Atom → Prop) (cs : List (VarName × Atom)) : Prop :=
  ∀ c ∈ cs, P c.2

/-- Both sides of every equation are safe. -/
def EquationsSafe (P : Atom → Prop) (eqs : List (Atom × Atom)) : Prop :=
  ∀ e ∈ eqs, P e.1 ∧ P e.2

/-- A binding relation stores only safe values; aliases store no atom. -/
def BindingRelSafe (P : Atom → Prop) : BindingRel → Prop
  | .val _ value => P value
  | .eq _ _ => True

/-- Every value stored in a binding set is safe. -/
def BindingsSafe (P : Atom → Prop) (b : Bindings) : Prop :=
  ∀ r ∈ b, BindingRelSafe P r

variable {P : Atom → Prop}

@[simp] theorem bindingsSafe_nil : BindingsSafe P [] := by
  intro r member; cases member

theorem bindingsSafe_cons {r : BindingRel} {b : Bindings} :
    BindingsSafe P (r :: b) ↔ BindingRelSafe P r ∧ BindingsSafe P b := by
  constructor
  · intro h
    exact ⟨h r (by simp), fun s member => h s (by simp [member])⟩
  · rintro ⟨hr, hb⟩ s member
    rcases List.mem_cons.mp member with rfl | tail
    · exact hr
    · exact hb s tail

theorem bindingsSafe_append {b c : Bindings}
    (hb : BindingsSafe P b) (hc : BindingsSafe P c) :
    BindingsSafe P (b ++ c) := by
  intro r member
  rcases List.mem_append.mp member with h | h
  · exact hb r h
  · exact hc r h

theorem substSafe_nil : SubstSafe P [] := by intro entry member; cases member

theorem substSafe_erase {s : Subst} (h : SubstSafe P s) (x : VarName) :
    SubstSafe P (Subst.erase s x) := by
  intro entry member
  exact h entry (List.mem_filter.mp member).1

theorem substSafe_extend {s : Subst} (h : SubstSafe P s) {x : VarName}
    {value : Atom} (hvalue : P value) :
    SubstSafe P (Subst.extend s x value) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | tail
  · exact hvalue
  · exact substSafe_erase h x entry tail

theorem substSafe_singleton {x : VarName} {value : Atom} (hvalue : P value) :
    SubstSafe P [(x, value)] := by
  intro entry member
  rcases List.mem_singleton.mp member with rfl
  exact hvalue

/-! ## Decomposition

`decomposeEq` never invents an atom: every constraint it emits carries a side
of the equation it decomposed, or a subterm of one.  The list companion is
stated with an explicit pointwise hypothesis so that it does not need to be
mutually recursive with the atom-level proof. -/

private theorem decomposeList_safe :
    ∀ {atoms : List Atom},
      (∀ a ∈ atoms, ∀ (right : Atom) (cs : List (VarName × Atom)),
        P right → Unify.decomposeEq a right = some cs → ConstraintsSafe P cs) →
      ∀ {others : List Atom}, (∀ a ∈ others, P a) →
      ∀ {cs : List (VarName × Atom)},
        Unify.decomposeList atoms others = some cs → ConstraintsSafe P cs := by
  intro atoms
  induction atoms with
  | nil =>
      intro _ others _ cs equation
      cases others with
      | nil => cases equation; intro c member; cases member
      | cons _ _ => simp [Unify.decomposeList] at equation
  | cons a rest ih =>
      intro pointwise others hothers cs equation
      cases others with
      | nil => simp [Unify.decomposeList] at equation
      | cons b others' =>
          simp only [Unify.decomposeList] at equation
          cases headEq : Unify.decomposeEq a b with
          | none => rw [headEq] at equation; simp at equation
          | some c₁ =>
            cases tailEq : Unify.decomposeList rest others' with
            | none => rw [headEq, tailEq] at equation; simp at equation
            | some c₂ =>
              rw [headEq, tailEq] at equation
              cases equation
              intro c member
              rcases List.mem_append.mp member with h | h
              · exact pointwise a (by simp) b c₁ (hothers b (by simp)) headEq c h
              · exact ih (fun x hx => pointwise x (by simp [hx]))
                  (fun x hx => hothers x (by simp [hx])) tailEq c h

private theorem decomposeEq_safe (S : AtomSafety P) :
    ∀ (left : Atom), P left → ∀ (right : Atom) (cs : List (VarName × Atom)),
      P right → Unify.decomposeEq left right = some cs →
      ConstraintsSafe P cs := by
  intro left
  induction left with
  | sym name =>
      intro hleft right cs hright equation
      cases right with
      | var y =>
          -- `decomposeEq t (var x)` records the LEFT atom as the constraint value
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hleft
      | sym other =>
          simp only [Unify.decomposeEq] at equation
          split at equation
          · cases equation; intro c member; cases member
          · simp at equation
      | _ => simp [Unify.decomposeEq] at equation
  | var x =>
      intro _ right cs hright equation
      cases right with
      | var y =>
          simp only [Unify.decomposeEq] at equation
          split at equation
          · cases equation; intro c member; cases member
          · cases equation
            intro c member
            rcases List.mem_singleton.mp member with rfl
            exact hright
      | sym other =>
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hright
      | gnd other =>
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hright
      | expr others =>
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hright
  | gnd value =>
      intro hleft right cs hright equation
      cases right with
      | var y =>
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hleft
      | gnd other =>
          simp only [Unify.decomposeEq] at equation
          split at equation
          · cases equation; intro c member; cases member
          · simp at equation
      | _ => simp [Unify.decomposeEq] at equation
  | expr atoms ih =>
      intro hleft right cs hright equation
      cases right with
      | var y =>
          simp only [Unify.decomposeEq] at equation
          cases equation
          intro c member
          rcases List.mem_singleton.mp member with rfl
          exact hleft
      | expr others =>
          simp only [Unify.decomposeEq] at equation
          refine decomposeList_safe (P := P) ?_ (S.hereditary others hright) equation
          intro a amember r c hr eq
          exact ih a amember (S.hereditary atoms hleft a amember) r c hr eq
      | _ => simp [Unify.decomposeEq] at equation

theorem decomposeAll_safe (S : AtomSafety P) :
    ∀ {eqs : List (Atom × Atom)} {cs : List (VarName × Atom)},
      EquationsSafe P eqs → Unify.decomposeAll eqs = some cs →
      ConstraintsSafe P cs := by
  intro eqs
  induction eqs with
  | nil =>
      intro cs _ equation
      cases equation
      intro c member; cases member
  | cons e rest ih =>
      intro cs hsafe equation
      simp only [Unify.decomposeAll] at equation
      cases headEq : Unify.decomposeEq e.1 e.2 with
      | none => rw [headEq] at equation; simp at equation
      | some c₁ =>
        cases tailEq : Unify.decomposeAll rest with
        | none => rw [headEq, tailEq] at equation; simp at equation
        | some c₂ =>
          rw [headEq, tailEq] at equation
          cases equation
          intro c member
          rcases List.mem_append.mp member with h | h
          · exact decomposeEq_safe S e.1 (hsafe e (by simp)).1 e.2 c₁
              (hsafe e (by simp)).2 headEq c h
          · exact ih (fun x hx => hsafe x (by simp [hx])) tailEq c h

/-! ## The unifier

The keystone.  Everything downstream — `merge`, and therefore the matcher's
own recursive step — routes through here. -/

/-- **Unification preserves safety.**  Safe equations and a safe accumulated
substitution yield a safe most-general unifier.

This is where all three interface obligations are consumed: `hereditary` via
decomposition, and `substClosed` together with `varSafe` in the elimination
step, which rebuilds each remaining equation by substituting into a freshly
constructed variable atom. -/
theorem unifyRounds_safe (S : AtomSafety P) :
    ∀ (fuel : Nat) {eqs : List (Atom × Atom)} {s result : Subst},
      EquationsSafe P eqs → SubstSafe P s →
      Unify.unifyRounds fuel eqs s = some result → SubstSafe P result := by
  intro fuel
  induction fuel with
  | zero =>
      intro eqs s result _ hs equation
      simp only [Unify.unifyRounds] at equation
      cases hdec : Unify.decomposeAll eqs with
      | none => rw [hdec] at equation; simp at equation
      | some cs =>
        rw [hdec] at equation
        cases cs with
        | nil => cases equation; exact hs
        | cons _ _ => simp at equation
  | succ fuel ih =>
      intro eqs s result heqs hs equation
      simp only [Unify.unifyRounds] at equation
      cases hdec : Unify.decomposeAll eqs with
      | none => rw [hdec] at equation; simp at equation
      | some cs =>
        have hcs : ConstraintsSafe P cs := decomposeAll_safe S heqs hdec
        rw [hdec] at equation
        cases cs with
        | nil => cases equation; exact hs
        | cons c rest =>
          obtain ⟨x, t⟩ := c
          have ht : P t := hcs (x, t) (by simp)
          have hrest : ConstraintsSafe P rest := fun d member =>
            hcs d (by simp [member])
          simp only at equation
          split at equation
          · simp at equation
          · refine ih ?_ (substSafe_extend hs ht) equation
            intro e member
            obtain ⟨d, dmember, rfl⟩ := List.mem_map.mp member
            exact ⟨S.substClosed _ _ (substSafe_singleton ht) (S.varSafe d.1),
              S.substClosed _ _ (substSafe_singleton ht) (hrest d dmember)⟩

/-! ## Rebuilding a binding set from a unifier

The reconciliation path returns a substitution, and `addVarBinding` turns it
back into bindings.  Aliases carry no atom, so only the substitution's values
can threaten safety — which the keystone above already controls. -/

theorem removeVal_safe {b : Bindings} (hb : BindingsSafe P b) (x : VarName) :
    BindingsSafe P (Bindings.removeVal b x) := by
  intro r member
  exact hb r (List.mem_filter.mp member).1

theorem addValRaw_safe {b : Bindings} (hb : BindingsSafe P b) (x : VarName)
    {value : Atom} (hvalue : P value) :
    BindingsSafe P (Bindings.addValRaw b x value) :=
  bindingsSafe_cons.mpr ⟨hvalue, removeVal_safe hb x⟩

theorem addEqRaw_safe {b : Bindings} (hb : BindingsSafe P b) (x y : VarName) :
    BindingsSafe P (Bindings.addEqRaw b x y) := by
  unfold Bindings.addEqRaw
  split
  · exact hb
  · exact bindingsSafe_cons.mpr ⟨trivial, hb⟩

theorem restoreAlias_safe {b : Bindings} (hb : BindingsSafe P b)
    (edge : VarName × VarName) :
    BindingsSafe P (Bindings.restoreAlias b edge) := by
  unfold Bindings.restoreAlias
  split
  · exact hb
  · exact addEqRaw_safe hb _ _

/-- The equality skeleton keeps only aliases, so it is safe for ANY predicate
— no hypothesis on the source bindings is required. -/
theorem equalitySkeleton_safe (b : Bindings) :
    BindingsSafe P (Bindings.equalitySkeleton b) := by
  induction b with
  | nil => simp [Bindings.equalitySkeleton]
  | cons r rest ih =>
      cases r with
      | val x value => simpa [Bindings.equalitySkeleton] using ih
      | eq x y =>
          rw [Bindings.equalitySkeleton]
          exact bindingsSafe_cons.mpr ⟨trivial, ih⟩

theorem ofSubst_safe {s : Subst} (hs : SubstSafe P s) :
    BindingsSafe P (Bindings.ofSubst s) := by
  intro r member
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  cases hentry : entry.2 with
  | var y => simp [BindingRelSafe]
  | sym name => simpa [hentry, BindingRelSafe] using hentry ▸ hs entry entryMember
  | gnd value => simpa [hentry, BindingRelSafe] using hentry ▸ hs entry entryMember
  | expr atoms => simpa [hentry, BindingRelSafe] using hentry ▸ hs entry entryMember

theorem rebuildFromSubst_safe (b : Bindings) {s : Subst} (hs : SubstSafe P s) :
    BindingsSafe P (Bindings.rebuildFromSubst b s) :=
  bindingsSafe_append (equalitySkeleton_safe b) (ofSubst_safe hs)

/-- Folding alias restoration preserves safety, for any starting accumulator. -/
theorem foldl_restoreAlias_safe :
    ∀ (aliases : List (VarName × VarName)) {b : Bindings}, BindingsSafe P b →
      BindingsSafe P (aliases.foldl Bindings.restoreAlias b) := by
  intro aliases
  induction aliases with
  | nil => intro b hb; simpa using hb
  | cons edge rest ih =>
      intro b hb
      simp only [List.foldl_cons]
      exact ih (restoreAlias_safe hb edge)

theorem rebuildFromReconciliation_safe (candidate source : Bindings)
    (extra : List (Atom × Atom)) {s : Subst} (hs : SubstSafe P s) :
    BindingsSafe P (Bindings.rebuildFromReconciliation candidate source extra s) :=
  foldl_restoreAlias_safe _ (rebuildFromSubst_safe candidate hs)

/-! ## Reconciliation -/

theorem equations_safe (S : AtomSafety P) {b : Bindings} (hb : BindingsSafe P b) :
    EquationsSafe P (Bindings.equations b) := by
  intro e member
  obtain ⟨r, rmember, rfl⟩ := List.mem_map.mp member
  cases r with
  | val x value => exact ⟨S.varSafe x, hb _ rmember⟩
  | eq x y => exact ⟨S.varSafe x, S.varSafe y⟩

theorem reconcileAll_safe (S : AtomSafety P) {b : Bindings}
    {extra : List (Atom × Atom)} {s : Subst}
    (hb : BindingsSafe P b) (hextra : EquationsSafe P extra)
    (equation : Bindings.reconcileAll b extra = some s) : SubstSafe P s := by
  refine unifyRounds_safe S _ ?_ substSafe_nil equation
  intro e member
  rcases List.mem_append.mp member with h | h
  · exact equations_safe S hb e h
  · exact hextra e h

/-! ## Adding one binding

Both entry points either store an input value directly or rebuild from a
reconciliation substitution.  Safety of the second case is exactly the
keystone. -/

theorem addVarEquality_safe (S : AtomSafety P) {b : Bindings}
    (hb : BindingsSafe P b) (x y : VarName) :
    ∀ c ∈ Bindings.addVarEquality b x y, BindingsSafe P c := by
  intro c member
  simp only [Bindings.addVarEquality] at member
  cases hu : Bindings.unifyValues
      (Bindings.classValues (Bindings.addEqRaw b x y) x) with
  | none => rw [hu] at member; simp at member
  | some values =>
    rw [hu] at member
    cases values with
    | nil =>
        rcases List.mem_singleton.mp member with rfl
        exact addEqRaw_safe hb x y
    | cons _ _ =>
      cases hr : Bindings.reconcileAll b [(Atom.var x, Atom.var y)] with
      | none => rw [hr] at member; simp at member
      | some sigma =>
        rw [hr] at member
        rcases List.mem_singleton.mp member with rfl
        exact rebuildFromReconciliation_safe _ _ _
          (reconcileAll_safe S hb
            (by
              intro e emember
              rcases List.mem_singleton.mp emember with rfl
              exact ⟨S.varSafe x, S.varSafe y⟩)
            hr)

theorem addVarBinding_safe (S : AtomSafety P) {b : Bindings}
    (hb : BindingsSafe P b) (x : VarName) {value : Atom} (hvalue : P value) :
    ∀ c ∈ Bindings.addVarBinding b x value, BindingsSafe P c := by
  intro c member
  unfold Bindings.addVarBinding at member
  split at member
  · exact addVarEquality_safe S hb x _ c member
  · split at member
    · rcases List.mem_singleton.mp member with rfl
      exact addValRaw_safe hb x hvalue
    · split at member
      · simp at member
      · rcases List.mem_singleton.mp member with rfl
        exact hb
      · split at member
        · simp at member
        · rcases List.mem_singleton.mp member with rfl
          next sigma reconciliation =>
            exact rebuildFromReconciliation_safe _ _ _
              (reconcileAll_safe S hb
                (by
                  intro e emember
                  rcases List.mem_singleton.mp emember with rfl
                  exact ⟨S.varSafe x, hvalue⟩)
                reconciliation)

/-! ## Merge -/

theorem mergeOne_safe (S : AtomSafety P) {bs : List Bindings}
    (hbs : ∀ b ∈ bs, BindingsSafe P b) {r : BindingRel}
    (hr : BindingRelSafe P r) :
    ∀ c ∈ Bindings.mergeOne bs r, BindingsSafe P c := by
  intro c member
  obtain ⟨b, bmember, cmember⟩ := List.mem_flatMap.mp member
  cases r with
  | val x value => exact addVarBinding_safe S (hbs b bmember) x hr c cmember
  | eq x y => exact addVarEquality_safe S (hbs b bmember) x y c cmember

/-- Folding `mergeOne` preserves safety for any safe accumulator. -/
theorem foldl_mergeOne_safe (S : AtomSafety P) :
    ∀ (rest : Bindings) {bs : List Bindings}, (∀ b ∈ bs, BindingsSafe P b) →
      (∀ r ∈ rest, BindingRelSafe P r) →
      ∀ c ∈ rest.foldl Bindings.mergeOne bs, BindingsSafe P c := by
  intro rest
  induction rest with
  | nil => intro bs hbs _ c member; exact hbs c member
  | cons r more ih =>
      intro bs hbs hrest c member
      simp only [List.foldl_cons] at member
      exact ih (mergeOne_safe S hbs (hrest r (by simp)))
        (fun s smember => hrest s (by simp [smember])) c member

/-- **Merging safe binding sets is safe.**  This is the fact the matcher's
recursive step needs, and it is where the unifier keystone is cashed in. -/
theorem merge_safe (S : AtomSafety P) {a b : Bindings}
    (ha : BindingsSafe P a) (hb : BindingsSafe P b) :
    ∀ c ∈ Bindings.merge a b, BindingsSafe P c :=
  foldl_mergeOne_safe S b
    (by
      intro d dmember
      rcases List.mem_singleton.mp dmember with rfl
      exact ha)
    (fun r rmember => hb r rmember)

/-! ## The matcher

`matchAtomsWith` stores only an input atom into a binding; its recursive step
delegates to `matchAll`, which threads accumulated sets through `merge`.  So
the matcher needs the merge fact above, and nothing more.

The default matcher (`custom = none`) is the public boundary.  A CUSTOM
grounded matcher is an arbitrary `Atom → Atom → List Bindings`, so no
provenance claim is possible for it — the statements below are deliberately
about `none`, matching `matchAtoms`. -/

private theorem matchAll_none_safe (S : AtomSafety P) :
    ∀ (atoms : List Atom),
      (∀ a ∈ atoms, ∀ (right : Atom), P right →
        ∀ b ∈ matchAtomsWith none a right, BindingsSafe P b) →
      ∀ (others : List Atom), (∀ a ∈ others, P a) →
      ∀ (acc : List Bindings), (∀ b ∈ acc, BindingsSafe P b) →
      ∀ b ∈ matchAll none acc atoms others, BindingsSafe P b := by
  intro atoms
  induction atoms with
  | nil =>
      intro _ others _ acc hacc b member
      cases others with
      | nil => exact hacc b member
      | cons _ _ => simp [matchAll] at member
  | cons a rest ih =>
      intro pointwise others hothers acc hacc b member
      cases others with
      | nil => simp [matchAll] at member
      | cons o others' =>
          simp only [matchAll] at member
          refine ih (fun x hx => pointwise x (by simp [hx]))
            others' (fun x hx => hothers x (by simp [hx])) _ ?_ b member
          intro d dmember
          obtain ⟨e, emember, dmem⟩ := List.mem_flatMap.mp dmember
          obtain ⟨f, fmember, dmem'⟩ := List.mem_flatMap.mp dmem
          refine merge_safe S (hacc e emember) ?_ d dmem'
          exact pointwise a (by simp) o (hothers o (by simp)) f
            (List.mem_of_mem_filter fmember)

/-- **The default matcher produces safe bindings from safe inputs.** -/
theorem matchAtomsWith_none_safe (S : AtomSafety P) :
    ∀ (left : Atom), P left → ∀ (right : Atom), P right →
      ∀ b ∈ matchAtomsWith none left right, BindingsSafe P b := by
  intro left
  induction left with
  | sym name =>
      intro _ right hright b member
      cases right with
      | var y =>
          simp only [matchAtomsWith] at member
          split at member
          · simp at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_cons.mpr ⟨‹P (Atom.sym name)›, bindingsSafe_nil⟩
      | _ =>
          simp only [matchAtomsWith] at member
          split at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_nil
          · simp at member
  | var x =>
      intro _ right hright b member
      cases right with
      | var y =>
          simp only [matchAtomsWith] at member
          split at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_nil
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_cons.mpr ⟨trivial, bindingsSafe_nil⟩
      | _ =>
          simp only [matchAtomsWith] at member
          split at member
          · simp at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_cons.mpr ⟨hright, bindingsSafe_nil⟩
  | gnd value =>
      intro hleft right hright b member
      cases right with
      | var y =>
          simp only [matchAtomsWith] at member
          split at member
          · simp at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_cons.mpr ⟨hleft, bindingsSafe_nil⟩
      | _ =>
          simp only [matchAtomsWith] at member
          split at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_nil
          · simp at member
  | expr atoms ih =>
      intro hleft right hright b member
      cases right with
      | var y =>
          simp only [matchAtomsWith] at member
          split at member
          · simp at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_cons.mpr ⟨hleft, bindingsSafe_nil⟩
      | expr others =>
          simp only [matchAtomsWith] at member
          refine matchAll_none_safe S atoms ?_ others (S.hereditary others hright)
            [[]] ?_ b member
          · intro a amember r hr
            exact ih a amember (S.hereditary atoms hleft a amember) r hr
          · intro d dmember
            rcases List.mem_singleton.mp dmember with rfl
            exact bindingsSafe_nil
      | _ =>
          simp only [matchAtomsWith] at member
          split at member
          · rcases List.mem_singleton.mp member with rfl
            exact bindingsSafe_nil
          · simp at member

/-- **The public matcher boundary.**  `matchAtoms` is `matchAtomsWith none`
followed by a loop filter, so safety transports through the filter. -/
theorem matchAtoms_safe (S : AtomSafety P) {left right : Atom}
    (hleft : P left) (hright : P right) :
    ∀ b ∈ matchAtoms left right, BindingsSafe P b := by
  intro b member
  exact matchAtomsWith_none_safe S left hleft right hright b
    (List.mem_of_mem_filter member)

/-! ## Instantiation at the state-free fragment

Each obligation is discharged by an existing lemma rather than re-proved, so
this section is a bridge and carries no new mathematical content. -/

/-- The state-free predicate satisfies the matching-pipeline interface. -/
theorem stateOpFree_atomSafety : AtomSafety StateOpFree where
  hereditary := fun _ safe _ member => stateOpFree_of_mem safe.2 member
  substClosed := fun _ a hs ha =>
    StateFreePreservation.stateOpFree_substApply
      (fun name value member => hs (name, value) member) a ha
  varSafe := fun _ => trivial

/-- The membership-style generic carrier coincides with the recursive carrier
used by the evaluator invariant. -/
theorem bindingsSafe_stateOpFree_iff (bindings : Bindings) :
    BindingsSafe StateOpFree bindings ↔ BindingsStateOpFree bindings := by
  induction bindings with
  | nil => simp [BindingsSafe, BindingsStateOpFree]
  | cons relation rest inductionHypothesis =>
      rw [bindingsSafe_cons, bindingsStateOpFree_cons, inductionHypothesis]
      cases relation <;> rfl

/-- Safe atoms match to state-operation-free bindings. -/
theorem matchAtoms_stateOpFree {left right : Atom}
    (hleft : StateOpFree left) (hright : StateOpFree right) :
    ∀ b ∈ matchAtoms left right, BindingsSafe StateOpFree b :=
  matchAtoms_safe stateOpFree_atomSafety hleft hright

/-- Evaluator-facing matcher boundary in the recursive binding invariant. -/
theorem matchAtoms_bindingsStateOpFree {left right : Atom}
    (leftSafe : StateOpFree left) (rightSafe : StateOpFree right) :
    ∀ bindings ∈ matchAtoms left right, BindingsStateOpFree bindings := by
  intro bindings member
  exact (bindingsSafe_stateOpFree_iff bindings).mp
    (matchAtoms_stateOpFree leftSafe rightSafe bindings member)

/-- Merging state-operation-free binding sets stays state-operation-free. -/
theorem merge_stateOpFree {a b : Bindings}
    (ha : BindingsSafe StateOpFree a) (hb : BindingsSafe StateOpFree b) :
    ∀ c ∈ Bindings.merge a b, BindingsSafe StateOpFree c :=
  merge_safe stateOpFree_atomSafety ha hb

/-- Evaluator-facing merge boundary in the recursive binding invariant. -/
theorem merge_bindingsStateOpFree {left right : Bindings}
    (leftSafe : BindingsStateOpFree left)
    (rightSafe : BindingsStateOpFree right) :
    ∀ bindings ∈ Bindings.merge left right,
      BindingsStateOpFree bindings := by
  intro bindings member
  exact (bindingsSafe_stateOpFree_iff bindings).mp
    (merge_stateOpFree
      ((bindingsSafe_stateOpFree_iff left).mpr leftSafe)
      ((bindingsSafe_stateOpFree_iff right).mpr rightSafe)
      bindings member)

/-- Evaluator-visible restriction remains state-operation-free.  The raw
projection is safe by structural resolution; replay through the ordinary
merge normalizer is safe by the generic merger theorem above. -/
theorem bindingsStateOpFree_restrictBnd {bindings : Bindings}
    (safe : BindingsStateOpFree bindings) (scopeVars : List VarName) :
    BindingsStateOpFree (Metta.Minimal.restrictBnd scopeVars bindings) := by
  have rawSafe : BindingsStateOpFree
      (Metta.Minimal.restrictBndRaw scopeVars bindings) :=
    StateFreePreservation.bindingsStateOpFree_restrictBndRaw safe scopeVars
  unfold Metta.Minimal.restrictBnd
  generalize rawEquation :
      Metta.Minimal.restrictBndRaw scopeVars bindings = raw
  rw [rawEquation] at rawSafe
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simpa [mergeEquation] using rawSafe
  | cons output outputs =>
      have outputMember : output ∈ Metta.Bindings.merge [] raw := by
        rw [mergeEquation]
        simp
      have outputSafe := merge_bindingsStateOpFree
        (left := ([] : Bindings)) (right := raw)
        (by trivial) rawSafe output outputMember
      simpa [mergeEquation] using outputSafe

/-- Unification of state-operation-free equations yields a safe unifier. -/
theorem unifyRounds_stateOpFree (fuel : Nat) {eqs : List (Atom × Atom)}
    {s result : Subst} (heqs : EquationsSafe StateOpFree eqs)
    (hs : SubstSafe StateOpFree s)
    (equation : Unify.unifyRounds fuel eqs s = some result) :
    SubstSafe StateOpFree result :=
  unifyRounds_safe stateOpFree_atomSafety fuel heqs hs equation

/-! ## Canaries

Positive: the pipeline accepts a real match and returns a real binding.
Negative: safety genuinely rejects — the predicate is not vacuously true, and
an input outside the fragment really does produce a binding outside it, so the
hypotheses are load-bearing rather than decorative. -/

/-- An ordinary symbol is in the fragment. -/
theorem canary_sym_a_safe : StateOpFree (Atom.sym "a") := by
  simp [StateOpFree, worldMutatingHeads]

/-- POSITIVE: matching a variable against a safe symbol binds it, safely. -/
theorem canary_match_var_sym :
    ∀ b ∈ matchAtoms (Atom.var "x") (Atom.sym "a"),
      BindingsSafe StateOpFree b :=
  matchAtoms_stateOpFree trivial canary_sym_a_safe

/-- POSITIVE: the matcher core really does produce a binding — the safety
statement above is not vacuously about an empty result set.  Stated on
`matchAtomsWith none` rather than `matchAtoms` so that it reduces without
evaluating the acyclicity filter, which is irrelevant to provenance. -/
theorem canary_matchAtomsWith_produces :
    matchAtomsWith none (Atom.var "x") (Atom.sym "a")
      = [[BindingRel.val "x" (Atom.sym "a")]] := by
  simp [matchAtomsWith, Subst.occurs]

/-- NEGATIVE: a mutation head is not a safe atom, so the hypothesis of the
positive canary genuinely constrains. -/
theorem canary_add_atom_not_safe : ¬ StateOpFree (Atom.sym "add-atom") := by
  simp [StateOpFree, worldMutatingHeads]

/-- NEGATIVE: `BindingsSafe` is not the constantly-true predicate. -/
theorem canary_bindingsSafe_rejects :
    ¬ BindingsSafe StateOpFree [BindingRel.val "x" (Atom.sym "add-atom")] := by
  intro contra
  exact canary_add_atom_not_safe
    (contra (BindingRel.val "x" (Atom.sym "add-atom")) (by simp))

/-- NEGATIVE: matching a variable against a mutation head DOES bind the
variable to it, so an input outside the fragment yields a binding outside it.
This is why the input hypotheses cannot be dropped. -/
theorem canary_outside_input_outside_output :
    ¬ (∀ b ∈ matchAtomsWith none (Atom.var "x") (Atom.sym "add-atom"),
        BindingsSafe StateOpFree b) := by
  intro contra
  have equation : matchAtomsWith none (Atom.var "x") (Atom.sym "add-atom")
      = [[BindingRel.val "x" (Atom.sym "add-atom")]] := by
    simp [matchAtomsWith, Subst.occurs]
  exact canary_bindingsSafe_rejects (contra _ (by rw [equation]; simp))

end Mettapedia.Languages.MeTTa.HE.MatcherProvenance
