/-
The declarative presentation-instantiation relation for finite type
substitutions.

`TypeInstantiatePresentationRel σ a b` is the relational counterpart of
`HumanTypePresentation.TypeSubst.apply`: resolved variables are replaced by
their first-hit assignment (one pass — normal substitutions carry no
assigned variable inside a stored value), unresolved variables are preserved
syntactically as themselves, and expressions instantiate pointwise.  The
unresolved-preservation clause is a constructor, not a lemma: the relation
cannot present an unconstrained variable as anything but itself, which is
the presentation law the escape counterexample demanded.

Exports: determinism (functionality), coincidence with the executable-free
`apply` function in both directions, unresolved-variable preservation, and
the commuting bridge to the Lea-side substitution application through the
structural translation — the form the fold-to-runtime correspondence
consumes.
-/
import Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeImage

namespace Mettapedia.Languages.MeTTa.HE.HumanTypeInstantiation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## The relation -/

/-- Declarative one-pass instantiation of a finite type substitution.
Unresolved variables are preserved as themselves by construction. -/
inductive TypeInstantiatePresentationRel (σ : TypeSubst) : Atom → Atom → Prop
  | symbol (name : String) :
      TypeInstantiatePresentationRel σ (.symbol name) (.symbol name)
  | grounded (value) :
      TypeInstantiatePresentationRel σ (.grounded value) (.grounded value)
  | varResolved (name : String) (value : Atom)
      (h : σ.lookup name = some value) :
      TypeInstantiatePresentationRel σ (.var name) value
  | varUnresolved (name : String) (h : σ.lookup name = none) :
      TypeInstantiatePresentationRel σ (.var name) (.var name)
  | expression {atoms outputs : List Atom}
      (h : List.Forall₂ (TypeInstantiatePresentationRel σ) atoms outputs) :
      TypeInstantiatePresentationRel σ
        (.expression atoms) (.expression outputs)

private theorem instantiation_size_pos (a : Atom) : 0 < sizeOf a := by
  cases a <;> simp

private theorem instantiation_size_lt_of_mem {a : Atom} :
    ∀ {l : List Atom}, a ∈ l → sizeOf a < sizeOf l
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp
      omega
    | inr h2 =>
      have := instantiation_size_lt_of_mem h2
      simp
      omega

/-! ## List helpers (pointwise-consuming, no size state) -/

private theorem forall₂_agreement_list {σ : TypeSubst} :
    ∀ {xs ys : List Atom},
      List.Forall₂ (TypeInstantiatePresentationRel σ) xs ys →
      (∀ x ∈ xs, ∀ y, TypeInstantiatePresentationRel σ x y →
        y = σ.apply x) →
      ys = xs.map σ.apply := by
  intro xs ys hforall
  induction hforall with
  | nil => intro _; rfl
  | @cons x y xtail ytail hxy _ ihtail =>
    intro hpt
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hpt x List.mem_cons_self y hxy,
      ihtail fun z hz w hw => hpt z (List.mem_cons_of_mem _ hz) w hw⟩

private theorem forall₂_totality_list {σ : TypeSubst} :
    ∀ {xs : List Atom},
      (∀ x ∈ xs, TypeInstantiatePresentationRel σ x (σ.apply x)) →
      List.Forall₂ (TypeInstantiatePresentationRel σ) xs
        (xs.map σ.apply) := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Forall₂.nil
  | cons x xtail ihtail =>
    intro hpt
    exact List.Forall₂.cons (hpt x List.mem_cons_self)
      (ihtail fun z hz => hpt z (List.mem_cons_of_mem _ hz))

private theorem mem_typeVarsList_of_mem {v : String} :
    ∀ {atoms : List Atom} {x : Atom}, x ∈ atoms →
      v ∈ TypeSubst.typeVars x → v ∈ TypeSubst.typeVarsList atoms := by
  intro atoms
  induction atoms with
  | nil =>
    intro x hx
    exact absurd hx (List.not_mem_nil)
  | cons y ytail ih =>
    intro x hx hv
    simp only [TypeSubst.typeVarsList]
    rcases List.mem_cons.mp hx with heq | hmem
    · subst heq
      exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (ih hmem hv)

private theorem map_apply_id_list {σ : TypeSubst} :
    ∀ {atoms : List Atom},
      (∀ x ∈ atoms, σ.apply x = x) →
      atoms.map σ.apply = atoms := by
  intro atoms
  induction atoms with
  | nil => intro _; rfl
  | cons x xtail ih =>
    intro hpt
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hpt x List.mem_cons_self,
      ih fun z hz => hpt z (List.mem_cons_of_mem _ hz)⟩

/-! ## Coincidence with the one-pass application -/

/-- Agreement: every derivation output is the one-pass application. -/
theorem agreement {σ : TypeSubst} :
    ∀ {a b : Atom}, TypeInstantiatePresentationRel σ a b →
      b = σ.apply a := by
  suffices key : ∀ (n : Nat) (a b : Atom), sizeOf a ≤ n →
      TypeInstantiatePresentationRel σ a b → b = σ.apply a by
    intro a b h
    exact key (sizeOf a) a b le_rfl h
  intro n
  induction n with
  | zero =>
    intro a b hsize
    exact absurd hsize (by have := instantiation_size_pos a; omega)
  | succ n ihn =>
    intro a b hsize h
    cases h with
    | symbol name => simp [TypeSubst.apply]
    | grounded value => simp [TypeSubst.apply]
    | varResolved name value hlookup =>
      simp [TypeSubst.apply, hlookup]
    | varUnresolved name hlookup =>
      simp [TypeSubst.apply, hlookup]
    | @expression atoms outputs hforall =>
      simp only [TypeSubst.apply, Atom.expression.injEq]
      have hatoms : sizeOf atoms ≤ n := by
        have : sizeOf (Atom.expression atoms) ≤ n + 1 := hsize
        simp at this
        omega
      apply forall₂_agreement_list hforall
      intro x hx y hxy
      have hxsize : sizeOf x ≤ n := by
        have := instantiation_size_lt_of_mem hx
        omega
      exact ihn x y hxsize hxy

/-- Totality: the one-pass application is derivable. -/
theorem totality (σ : TypeSubst) :
    ∀ a : Atom, TypeInstantiatePresentationRel σ a (σ.apply a) := by
  suffices key : ∀ (n : Nat) (a : Atom), sizeOf a ≤ n →
      TypeInstantiatePresentationRel σ a (σ.apply a) by
    intro a
    exact key (sizeOf a) a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := instantiation_size_pos a; omega)
  | succ n ihn =>
    intro a hsize
    cases a with
    | symbol name =>
      simpa [TypeSubst.apply] using
        TypeInstantiatePresentationRel.symbol (σ := σ) name
    | grounded value =>
      simpa [TypeSubst.apply] using
        TypeInstantiatePresentationRel.grounded (σ := σ) value
    | var name =>
      cases hlookup : σ.lookup name with
      | none =>
        simpa [TypeSubst.apply, hlookup] using
          TypeInstantiatePresentationRel.varUnresolved name hlookup
      | some value =>
        simpa [TypeSubst.apply, hlookup] using
          TypeInstantiatePresentationRel.varResolved name value hlookup
    | expression atoms =>
      simp only [TypeSubst.apply]
      apply TypeInstantiatePresentationRel.expression
      have hatoms : sizeOf atoms ≤ n := by
        simp at hsize
        omega
      apply forall₂_totality_list
      intro x hx
      have hxsize : sizeOf x ≤ n := by
        have := instantiation_size_lt_of_mem hx
        omega
      exact ihn x hxsize

/-- **Functionality.**  The relation is deterministic. -/
theorem functionality {σ : TypeSubst} {a b₁ b₂ : Atom}
    (h₁ : TypeInstantiatePresentationRel σ a b₁)
    (h₂ : TypeInstantiatePresentationRel σ a b₂) : b₁ = b₂ := by
  rw [agreement h₁, agreement h₂]

/-- **Coincidence.**  The relation is exactly the graph of `apply`. -/
theorem coincidence (σ : TypeSubst) (a b : Atom) :
    TypeInstantiatePresentationRel σ a b ↔ σ.apply a = b := by
  constructor
  · intro h
    exact (agreement h).symm
  · intro h
    subst h
    exact totality σ a

/-! ## Unresolved-variable preservation -/

/-- Unassigned variables present as themselves — the constructor, exported. -/
theorem unresolved_var {σ : TypeSubst} {name : String}
    (h : σ.lookup name = none) :
    TypeInstantiatePresentationRel σ (.var name) (.var name) :=
  TypeInstantiatePresentationRel.varUnresolved name h

private theorem apply_id_of_unresolved {σ : TypeSubst} :
    ∀ (n : Nat) (a : Atom), sizeOf a ≤ n →
      (∀ v ∈ TypeSubst.typeVars a, σ.lookup v = none) →
      σ.apply a = a := by
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := instantiation_size_pos a; omega)
  | succ n ihn =>
    intro a hsize hfree
    cases a with
    | symbol name => simp [TypeSubst.apply]
    | grounded value => simp [TypeSubst.apply]
    | var name =>
      have : σ.lookup name = none :=
        hfree name (by simp [TypeSubst.typeVars])
      simp [TypeSubst.apply, this]
    | expression atoms =>
      simp only [TypeSubst.apply, Atom.expression.injEq]
      have hatoms : sizeOf atoms ≤ n := by
        simp at hsize
        omega
      apply map_apply_id_list
      intro x hx
      have hxsize : sizeOf x ≤ n := by
        have := instantiation_size_lt_of_mem hx
        omega
      apply ihn x hxsize
      intro v hv
      apply hfree
      simp only [TypeSubst.typeVars]
      exact mem_typeVarsList_of_mem hx hv

/-- An atom none of whose type variables are assigned instantiates to
itself. -/
theorem unresolved_preservation {σ : TypeSubst} {a : Atom}
    (hfree : ∀ v ∈ TypeSubst.typeVars a, σ.lookup v = none) :
    TypeInstantiatePresentationRel σ a a :=
  (coincidence σ a a).mpr
    (apply_id_of_unresolved (sizeOf a) a le_rfl hfree)

/-! ## The Lea-side bridge -/

/-- Translate a human finite type substitution to a Lea substitution. -/
def toLeaTTaTypeSubst (σ : TypeSubst) : Metta.Subst :=
  σ.map fun entry => (entry.1, toLeaTTaAtom entry.2)

private theorem lookup_comm (σ : TypeSubst) (name : String) :
    Metta.Subst.lookup (toLeaTTaTypeSubst σ) name =
      (σ.lookup name).map toLeaTTaAtom := by
  induction σ with
  | nil => simp [toLeaTTaTypeSubst, Metta.Subst.lookup, TypeSubst.lookup]
  | cons entry rest ih =>
    simp only [toLeaTTaTypeSubst, List.map_cons, Metta.Subst.lookup,
      TypeSubst.lookup]
    by_cases hname : name = entry.1
    · subst hname
      simp
    · have hbeq : (name == entry.1) = false := by
        simpa using hname
      simp only [hbeq, if_neg hname]
      simp only [Bool.false_eq_true, if_false]
      exact ih

private theorem toLeaTTaAtoms_map_comm {σ : TypeSubst} :
    ∀ {atoms : List Atom},
      (∀ x ∈ atoms, toLeaTTaAtom (σ.apply x) =
        Metta.Subst.apply (toLeaTTaTypeSubst σ) (toLeaTTaAtom x)) →
      toLeaTTaAtoms (atoms.map σ.apply) =
        (toLeaTTaAtoms atoms).map
          (Metta.Subst.apply (toLeaTTaTypeSubst σ)) := by
  intro atoms
  induction atoms with
  | nil => intro _; rfl
  | cons x xtail ih =>
    intro hpt
    simp only [List.map_cons, toLeaTTaAtoms, List.cons.injEq]
    exact ⟨hpt x List.mem_cons_self,
      ih fun z hz => hpt z (List.mem_cons_of_mem _ hz)⟩

/-- **The commuting square.**  Human one-pass application translates to
Lea-side substitution application. -/
theorem toLeaTTaAtom_apply_comm (σ : TypeSubst) :
    ∀ a : Atom,
      toLeaTTaAtom (σ.apply a) =
        Metta.Subst.apply (toLeaTTaTypeSubst σ) (toLeaTTaAtom a) := by
  suffices key : ∀ (n : Nat) (a : Atom), sizeOf a ≤ n →
      toLeaTTaAtom (σ.apply a) =
        Metta.Subst.apply (toLeaTTaTypeSubst σ) (toLeaTTaAtom a) by
    intro a
    exact key (sizeOf a) a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := instantiation_size_pos a; omega)
  | succ n ihn =>
    intro a hsize
    cases a with
    | symbol name =>
      simp [TypeSubst.apply, toLeaTTaAtom, Metta.Subst.apply]
    | grounded value =>
      simp [TypeSubst.apply, toLeaTTaAtom, Metta.Subst.apply]
    | var name =>
      simp only [TypeSubst.apply, toLeaTTaAtom, Metta.Subst.apply,
        lookup_comm]
      cases hlookup : σ.lookup name with
      | none => simp [toLeaTTaAtom]
      | some value => simp
    | expression atoms =>
      simp only [TypeSubst.apply, toLeaTTaAtom, Metta.Subst.apply,
        Metta.Atom.expr.injEq]
      have hatoms : sizeOf atoms ≤ n := by
        simp at hsize
        omega
      apply toLeaTTaAtoms_map_comm
      intro x hx
      have hxsize : sizeOf x ≤ n := by
        have := instantiation_size_lt_of_mem hx
        omega
      exact ihn x hxsize

/-- Relation-level bridge: every derivation translates to a Lea-side
substitution-application equation — the form the fold-to-runtime
correspondence consumes. -/
theorem rel_toLeaTTa_bridge {σ : TypeSubst} {a b : Atom}
    (h : TypeInstantiatePresentationRel σ a b) :
    Metta.Subst.apply (toLeaTTaTypeSubst σ) (toLeaTTaAtom a) =
      toLeaTTaAtom b := by
  rw [agreement h]
  exact (toLeaTTaAtom_apply_comm σ a).symm

/-- Instantiation outputs of translated inputs are in the HE image. -/
theorem rel_output_heImage {σ : TypeSubst} {a b : Atom}
    (h : TypeInstantiatePresentationRel σ a b) :
    LeaAtomHEImage (Metta.Subst.apply (toLeaTTaTypeSubst σ)
      (toLeaTTaAtom a)) := by
  rw [rel_toLeaTTa_bridge h]
  exact leaAtomHEImage_toLeaTTaAtom b

end Mettapedia.Languages.MeTTa.HE.HumanTypeInstantiation
