import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Private unknowns: when two families of terms share no unknown

At the one-frame action of a substitution action, the step has no partition of its unknowns into
owners: every unknown is a term of the one frame, and any party's knowledge may constrain it. This
module states, without naming unknowns at all, what it means for two families of terms to share
none.

## Independence

`Independent A F G`: every instantiation of the family `F` and every instantiation of the family `G`
are realized together by one substitution, on the terms of each family. It is the property the
opening of a rule is asked for by `Firing.Fresh` (an amalgamation of the state's terms with the
rule's), now asked of any two families.

* It is symmetric (`Independent.symm`) and survives shrinking either family (`Independent.mono`).
* **Fixed terms share no unknown with anything** (`independent_of_fixed`): a family whose terms
  every substitution fixes, such as ground rows, is independent of every family.
* **Stores over independent families are solvable together when each is** (`consistent_append`).
  This is the joint solution that composition needs; `models_of_agree` is the reason: a
  substitution agreeing with a solution on the terms of a store solves it.

## At first-order terms, independence is disjoint mention

For the first-order action (`FirstOrder.action`), the unknowns a family mentions are the free
variables of its terms (`UnknownsOf`).

* `independent_of_disjoint`: families that mention disjoint unknowns are independent; the witness
  glues the two substitutions along the unknowns of the first family.
* `not_independent_of_shared`: one shared unknown defeats independence, as soon as the signature has
  two distinct terms (instantiate the shared unknown by each).
* `independent_iff_disjoint`: so independence is exactly disjoint mention. The lemma under it,
  `agree_of_applyTerm_eq`, says that two substitutions that agree on a term agree on each of its
  unknowns.

Controls: two terms with one common unknown are not independent (`Controls.shared_dependent`); the
same unknown beside a constant is (`Controls.fixed_independent`); two terms with different unknowns
are (`Controls.disjoint_independent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Mettapedia.Logic.LP

universe uT uS

/-! ## Independence, for every substitution action -/

section Semantic

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **Two families of terms share no unknown**, semantically: any instantiation of the first and any
instantiation of the second are realized together by one substitution, on the terms of each. -/
def Independent (F G : T → Prop) : Prop :=
  ∀ σ τ : S, ∃ ρ : S, (∀ t, F t → A.E (A.apply ρ t) (A.apply σ t)) ∧
    ∀ t, G t → A.E (A.apply ρ t) (A.apply τ t)

/-- Terms that every substitution fixes. -/
def Fixed (G : T → Prop) : Prop := ∀ t, G t → ∀ σ : S, A.E (A.apply σ t) t

/-- The terms of an equation store: the sides of its equations. -/
def StoreTerms (K : EquationStore T) (t : T) : Prop := t ∈ K.map Prod.fst ∨ t ∈ K.map Prod.snd

variable {A}

theorem Independent.symm {F G : T → Prop} (independent : Independent A F G) :
    Independent A G F := by
  intro σ τ
  obtain ⟨ρ, onF, onG⟩ := independent τ σ
  exact ⟨ρ, onG, onF⟩

theorem Independent.mono {F G F' G' : T → Prop} (independent : Independent A F G)
    (inF : ∀ t, F' t → F t) (inG : ∀ t, G' t → G t) : Independent A F' G' := by
  intro σ τ
  obtain ⟨ρ, onF, onG⟩ := independent σ τ
  exact ⟨ρ, fun t member => onF t (inF t member), fun t member => onG t (inG t member)⟩

/-- **Fixed terms share no unknown with anything.** -/
theorem independent_of_fixed {F G : T → Prop} (fixed : Fixed A G) : Independent A F G := by
  intro σ τ
  refine ⟨σ, fun t _ => A.equivalence.refl _, fun t member => ?_⟩
  exact A.equivalence.trans (fixed t member σ) (A.equivalence.symm (fixed t member τ))

theorem storeTerms_of_mem {K : EquationStore T} {e : Equation T} (member : e ∈ K) :
    StoreTerms K e.1 ∧ StoreTerms K e.2 :=
  ⟨Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩), Or.inr (List.mem_map.mpr ⟨e, member, rfl⟩)⟩

/-- **A substitution that agrees with a solution on the terms of a store solves it.** -/
theorem models_of_agree {ρ σ : S} {K : EquationStore T}
    (agree : ∀ t, StoreTerms K t → A.E (A.apply ρ t) (A.apply σ t)) (solved : A.Models σ K) :
    A.Models ρ K := by
  intro e member
  have left : A.E (A.apply ρ e.1) (A.apply σ e.1) := agree e.1 (storeTerms_of_mem member).1
  have right : A.E (A.apply ρ e.2) (A.apply σ e.2) := agree e.2 (storeTerms_of_mem member).2
  exact A.equivalence.trans left (A.equivalence.trans (solved e member) (A.equivalence.symm right))

/-- **Stores over independent families are solvable together** when each is. -/
theorem consistent_append {F G : T → Prop} (independent : Independent A F G)
    {K L : EquationStore T} (overF : ∀ t, StoreTerms K t → F t) (overG : ∀ t, StoreTerms L t → G t)
    (solvedK : A.Consistent K) (solvedL : A.Consistent L) : A.Consistent (K ++ L) := by
  obtain ⟨σ, onK⟩ := solvedK
  obtain ⟨τ, onL⟩ := solvedL
  obtain ⟨ρ, onF, onG⟩ := independent σ τ
  refine ⟨ρ, (A.models_append ρ K L).mpr ⟨?_, ?_⟩⟩
  · exact models_of_agree (fun t member => onF t (overF t member)) onK
  · exact models_of_agree (fun t member => onG t (overG t member)) onL

end Semantic

/-! ## At first-order terms, independence is disjoint mention -/

section FirstOrder

variable {sig : LPSignature} [DecidableEq sig.vars]

/-- **The unknowns a family of first-order terms mentions**: the free variables of its terms. -/
def UnknownsOf (F : Term sig → Prop) (v : sig.vars) : Prop := ∃ t, F t ∧ v ∈ t.freeVars

/-- **Families that mention disjoint unknowns are independent**: glue the two substitutions along
the unknowns of the first family. -/
theorem independent_of_disjoint {F G : Term sig → Prop}
    (apart : ∀ v, UnknownsOf F v → ¬ UnknownsOf G v) :
    Independent (FirstOrder.action sig) F G := by
  classical
  intro σ τ
  refine ⟨fun v => if UnknownsOf F v then σ v else τ v, fun t member => ?_, fun t member => ?_⟩
  · show Subst.applyTerm _ t = Subst.applyTerm σ t
    apply Subst.applyTerm_congr
    intro v inside
    show (if UnknownsOf F v then σ v else τ v) = σ v
    exact if_pos ⟨t, member, inside⟩
  · show Subst.applyTerm _ t = Subst.applyTerm τ t
    apply Subst.applyTerm_congr
    intro v inside
    have notF : ¬ UnknownsOf F v := fun inF => apart v inF ⟨t, member, inside⟩
    show (if UnknownsOf F v then σ v else τ v) = τ v
    exact if_neg notF

/-- **Two substitutions that agree on a term agree on each of its unknowns.** -/
theorem agree_of_applyTerm_eq {ρ σ : Subst sig} (t : Term sig) :
    Subst.applyTerm ρ t = Subst.applyTerm σ t → ∀ v ∈ t.freeVars, ρ v = σ v := by
  induction t with
  | var w =>
      intro same v inside
      rw [Term.mem_freeVars_var] at inside
      subst inside
      exact same
  | const _ =>
      intro _ v inside
      exact absurd inside Term.not_mem_freeVars_const
  | app f ts ih =>
      intro same v inside
      obtain ⟨i, inChild⟩ := Term.mem_freeVars_app.mp inside
      simp only [Subst.applyTerm_app] at same
      have children := (Term.app.inj same).2
      have child : Subst.applyTerm ρ (ts i) = Subst.applyTerm σ (ts i) :=
        congrFun (eq_of_heq children) i
      exact ih i child v inChild

/-- **A shared unknown defeats independence**, as soon as two distinct terms exist. -/
theorem not_independent_of_shared {F G : Term sig → Prop} {a b : Term sig} (different : a ≠ b)
    {v : sig.vars} (inF : UnknownsOf F v) (inG : UnknownsOf G v) :
    ¬ Independent (FirstOrder.action sig) F G := by
  intro independent
  obtain ⟨t, memberF, insideF⟩ := inF
  obtain ⟨u, memberG, insideG⟩ := inG
  obtain ⟨ρ, onF, onG⟩ := independent (fun _ => a) (fun _ => b)
  have first : ρ v = a := agree_of_applyTerm_eq t (onF t memberF) v insideF
  have second : ρ v = b := agree_of_applyTerm_eq u (onG u memberG) v insideG
  exact different (first.symm.trans second)

/-- **At first-order terms, independence is exactly disjoint mention.** -/
theorem independent_iff_disjoint {F G : Term sig → Prop} {a b : Term sig} (different : a ≠ b) :
    Independent (FirstOrder.action sig) F G ↔ ∀ v, UnknownsOf F v → ¬ UnknownsOf G v :=
  ⟨fun independent _ inF inG => not_independent_of_shared different inF inG independent,
    independent_of_disjoint⟩

end FirstOrder

/-! ## Controls -/

namespace Controls

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The unknown `n`. -/
abbrev unknown (n : ℕ) : Term atoms := .var n

/-- The constant `n`. -/
abbrev number (n : ℕ) : Term atoms := .const n

theorem numbers_differ : (number 0 : Term atoms) ≠ number 1 := by
  intro same
  exact absurd (Term.const.inj same) (by decide)

/-- **Two terms with one common unknown are not independent.** -/
theorem shared_dependent : ¬ Independent action (· = unknown 0) (· = unknown 0) :=
  not_independent_of_shared (v := 0) numbers_differ ⟨unknown 0, rfl, by simp [Term.freeVars]⟩
    ⟨unknown 0, rfl, by simp [Term.freeVars]⟩

/-- **The same unknown beside a constant is independent of it.** -/
theorem fixed_independent : Independent action (· = unknown 0) (· = number 3) :=
  independent_of_fixed fun t same σ => by
    subst same
    rfl

/-- **Terms with different unknowns are independent.** -/
theorem disjoint_independent : Independent action (· = unknown 0) (· = unknown 1) := by
  apply independent_of_disjoint
  rintro w ⟨t, rfl, inside⟩ ⟨u, rfl, inside'⟩
  simp only [Term.freeVars, Finset.mem_singleton] at inside inside'
  omega

end Controls

#print axioms Independent.symm
#print axioms Independent.mono
#print axioms independent_of_fixed
#print axioms models_of_agree
#print axioms consistent_append
#print axioms independent_of_disjoint
#print axioms agree_of_applyTerm_eq
#print axioms not_independent_of_shared
#print axioms independent_iff_disjoint
#print axioms Controls.shared_dependent
#print axioms Controls.fixed_independent
#print axioms Controls.disjoint_independent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
