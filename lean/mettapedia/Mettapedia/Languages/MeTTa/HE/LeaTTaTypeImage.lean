/-
Exact HE-image provenance for the repaired type-matching pipeline.

`LeaAtomHEImage a` holds when `a` is the structural translation of some
native HE atom.  The type-layer soundness theorems need this provenance for
recursively inferred results: every value stored by the repaired matcher,
merge, and type-argument fold — including every substitution value produced
by LeaTTa's own unifier during reconciliation — is assembled from subterms
of image inputs under image-valued substitutions, hence stays in the image.

Two closure facts drive everything:
* subterm closure — the translation is compositional, so subterms of image
  atoms are images of native subterms;
* substitution closure — applying an image-valued substitution to an image
  atom yields an image atom.

No HE-executable matcher/merge and no `DeclMatchSpec` enter any proof; the
structural inductions are over repaired LeaTTa's own functions only.
-/
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## The image predicates -/

/-- An atom in the exact structural image of the HE translation. -/
def LeaAtomHEImage (a : Metta.Atom) : Prop :=
  ∃ native : OSLFCore.Atom, toLeaTTaAtom native = a

/-- A list of atoms pointwise in the exact translation image. -/
def LeaAtomsHEImage (atoms : List Metta.Atom) : Prop :=
  ∃ natives : List OSLFCore.Atom, toLeaTTaAtoms natives = atoms

/-- A substitution whose stored values are all in the translation image. -/
def MettaSubstHEImage (subst : Metta.Subst) : Prop :=
  ∀ pair ∈ subst, LeaAtomHEImage pair.2

/-- A binding record whose stored direct values are all in the image. -/
def LeaBindingsHEImage (lb : Metta.Bindings) : Prop :=
  ∀ x v, Metta.BindingRel.val x v ∈ lb → LeaAtomHEImage v

/-! ## Basic image facts and the two closure lemmas -/

theorem leaAtomHEImage_toLeaTTaAtom (a : OSLFCore.Atom) :
    LeaAtomHEImage (toLeaTTaAtom a) := ⟨a, rfl⟩

theorem leaAtomHEImage_sym (s : String) :
    LeaAtomHEImage (Metta.Atom.sym s) := ⟨.symbol s, rfl⟩

theorem leaAtomHEImage_var (v : String) :
    LeaAtomHEImage (Metta.Atom.var v) := ⟨.var v, rfl⟩

theorem leaAtomsHEImage_nil : LeaAtomsHEImage [] := ⟨[], rfl⟩

theorem leaAtomsHEImage_cons {x : Metta.Atom} {xs : List Metta.Atom}
    (hx : LeaAtomHEImage x) (hxs : LeaAtomsHEImage xs) :
    LeaAtomsHEImage (x :: xs) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨ns, hns⟩ := hxs
  exact ⟨n :: ns, by simp [toLeaTTaAtoms, hn, hns]⟩

theorem leaAtomsHEImage_cons_iff {x : Metta.Atom} {xs : List Metta.Atom} :
    LeaAtomsHEImage (x :: xs) ↔ LeaAtomHEImage x ∧ LeaAtomsHEImage xs := by
  constructor
  · rintro ⟨ns, hns⟩
    cases ns with
    | nil => simp [toLeaTTaAtoms] at hns
    | cons n ntail =>
      simp only [toLeaTTaAtoms, List.cons.injEq] at hns
      exact ⟨⟨n, hns.1⟩, ⟨ntail, hns.2⟩⟩
  · rintro ⟨hx, hxs⟩
    exact leaAtomsHEImage_cons hx hxs

theorem leaAtomHEImage_expr_iff {xs : List Metta.Atom} :
    LeaAtomHEImage (Metta.Atom.expr xs) ↔ LeaAtomsHEImage xs := by
  constructor
  · rintro ⟨native, hnative⟩
    cases native with
    | symbol s => simp [toLeaTTaAtom] at hnative
    | var v => simp [toLeaTTaAtom] at hnative
    | grounded g => simp [toLeaTTaAtom] at hnative
    | expression es =>
      simp only [toLeaTTaAtom, Metta.Atom.expr.injEq] at hnative
      exact ⟨es, hnative⟩
  · rintro ⟨ns, hns⟩
    exact ⟨.expression ns, by simp [toLeaTTaAtom, hns]⟩

theorem leaAtomsHEImage_of_mem {xs : List Metta.Atom}
    (h : LeaAtomsHEImage xs) : ∀ x ∈ xs, LeaAtomHEImage x := by
  induction xs with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons head tail ih =>
    rw [leaAtomsHEImage_cons_iff] at h
    intro x hx
    rcases List.mem_cons.mp hx with heq | hmem
    · subst heq; exact h.1
    · exact ih h.2 x hmem

theorem leaAtomsHEImage_of_forall {xs : List Metta.Atom}
    (h : ∀ x ∈ xs, LeaAtomHEImage x) : LeaAtomsHEImage xs := by
  induction xs with
  | nil => exact leaAtomsHEImage_nil
  | cons head tail ih =>
    exact leaAtomsHEImage_cons (h head List.mem_cons_self)
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **Subterm closure.**  Children of an image expression are images. -/
theorem leaAtomHEImage_children {xs : List Metta.Atom}
    (h : LeaAtomHEImage (Metta.Atom.expr xs)) :
    ∀ x ∈ xs, LeaAtomHEImage x :=
  leaAtomsHEImage_of_mem (leaAtomHEImage_expr_iff.mp h)

private theorem image_size_pos (a : Metta.Atom) : 0 < a.size := by
  cases a <;> simp only [Metta.Atom.size] <;> omega

private theorem image_size_lt_of_mem {a : Metta.Atom} :
    ∀ {l : List Metta.Atom}, a ∈ l →
      a.size < (Metta.Atom.expr l).size
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
      omega
    | inr h2 =>
      have := image_size_lt_of_mem h2
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at this ⊢
      omega

private theorem substLookup_image {subst : Metta.Subst}
    (hsubst : MettaSubstHEImage subst) :
    ∀ {x : String} {v : Metta.Atom},
      Metta.Subst.lookup subst x = some v → LeaAtomHEImage v := by
  intro x v hlookup
  induction subst with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons pair rest ih =>
    simp only [Metta.Subst.lookup] at hlookup
    by_cases hx : (x == pair.1) = true
    · rw [if_pos hx] at hlookup
      cases hlookup
      exact hsubst pair List.mem_cons_self
    · rw [if_neg hx] at hlookup
      exact ih (fun p hp => hsubst p (List.mem_cons_of_mem _ hp)) hlookup

/-- **Substitution closure.**  Applying an image-valued substitution to an
image atom yields an image atom. -/
theorem substApply_image {subst : Metta.Subst}
    (hsubst : MettaSubstHEImage subst) :
    ∀ a : Metta.Atom, LeaAtomHEImage a →
      LeaAtomHEImage (Metta.Subst.apply subst a) := by
  suffices key : ∀ (n : Nat) (a : Metta.Atom), a.size ≤ n →
      LeaAtomHEImage a →
      LeaAtomHEImage (Metta.Subst.apply subst a) by
    exact fun a => key a.size a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := image_size_pos a; omega)
  | succ n ihn =>
    intro a hsize himage
    cases a with
    | sym s => simpa [Metta.Subst.apply] using himage
    | gnd g => simpa [Metta.Subst.apply] using himage
    | var x =>
      simp only [Metta.Subst.apply]
      cases hlookup : Metta.Subst.lookup subst x with
      | none => simpa using leaAtomHEImage_var x
      | some v =>
        simpa using substLookup_image hsubst hlookup
    | expr xs =>
      simp only [Metta.Subst.apply]
      rw [leaAtomHEImage_expr_iff]
      apply leaAtomsHEImage_of_forall
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hlt := image_size_lt_of_mem hz
      exact ihn z (by omega)
        (leaAtomHEImage_children himage z hz)

/-! ## Image provenance through LeaTTa's own unifier -/

private theorem decomposeEq_image :
    ∀ (n : Nat) (a b : Metta.Atom)
      (constraints : List (Metta.VarName × Metta.Atom)),
      a.size + b.size ≤ n →
      LeaAtomHEImage a → LeaAtomHEImage b →
      Metta.Unify.decomposeEq a b = some constraints →
      ∀ c ∈ constraints, LeaAtomHEImage c.2 := by
  intro n
  induction n with
  | zero =>
    intro a b constraints hsize
    exact absurd hsize (by
      have := image_size_pos a
      have := image_size_pos b
      omega)
  | succ n ihn =>
    intro a b constraints hsize ha hb hdecompose
    have hlist : ∀ (xs ys : List Metta.Atom)
        (cs : List (Metta.VarName × Metta.Atom)),
        (Metta.Atom.expr xs).size + (Metta.Atom.expr ys).size ≤ n + 1 →
        (∀ x ∈ xs, LeaAtomHEImage x) →
        (∀ y ∈ ys, LeaAtomHEImage y) →
        Metta.Unify.decomposeList xs ys = some cs →
        ∀ c ∈ cs, LeaAtomHEImage c.2 := by
      intro xs
      induction xs with
      | nil =>
        intro ys cs _ _ _ hdec
        cases ys with
        | nil =>
          simp only [Metta.Unify.decomposeList, Option.some.injEq] at hdec
          subst hdec
          intro c hc
          exact absurd hc (List.not_mem_nil)
        | cons _ _ => simp [Metta.Unify.decomposeList] at hdec
      | cons x xtail ihx =>
        intro ys cs hsz hxs hys hdec
        cases ys with
        | nil => simp [Metta.Unify.decomposeList] at hdec
        | cons y ytail =>
          simp only [Metta.Unify.decomposeList] at hdec
          cases hhead : Metta.Unify.decomposeEq x y with
          | none => rw [hhead] at hdec; cases hdec
          | some cHead =>
            cases htail : Metta.Unify.decomposeList xtail ytail with
            | none => rw [hhead, htail] at hdec; cases hdec
            | some cTail =>
              rw [hhead, htail] at hdec
              cases hdec
              intro c hc
              rcases List.mem_append.mp hc with hmem | hmem
              · have hxsize : x.size + y.size ≤ n := by
                  have hx := image_size_lt_of_mem
                    (List.mem_cons_self (a := x) (l := xtail))
                  have hy := image_size_lt_of_mem
                    (List.mem_cons_self (a := y) (l := ytail))
                  simp only [Metta.Atom.size, List.map_cons,
                    List.sum_cons] at hsz hx hy ⊢
                  omega
                exact ihn x y cHead hxsize
                  (hxs x List.mem_cons_self)
                  (hys y List.mem_cons_self) hhead c hmem
              · have hszTail : (Metta.Atom.expr xtail).size +
                    (Metta.Atom.expr ytail).size ≤ n + 1 := by
                  simp only [Metta.Atom.size, List.map_cons,
                    List.sum_cons] at hsz ⊢
                  have := image_size_pos x
                  have := image_size_pos y
                  omega
                exact ihx ytail cTail hszTail
                  (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
                  (fun z hz => hys z (List.mem_cons_of_mem _ hz))
                  htail c hmem
    cases a with
    | var x =>
      cases b with
      | var y =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        by_cases hxy : (x == y) = true
        · rw [if_pos hxy] at hdecompose
          cases hdecompose
          intro c hc
          exact absurd hc (List.not_mem_nil)
        · rw [if_neg hxy] at hdecompose
          cases hdecompose
          intro c hc
          rcases List.mem_cons.mp hc with heq | hmem
          · subst heq
            exact leaAtomHEImage_var y
          · exact absurd hmem (List.not_mem_nil)
      | sym s =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact hb
        · exact absurd hmem (List.not_mem_nil)
      | gnd g =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact hb
        · exact absurd hmem (List.not_mem_nil)
      | expr ys =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact hb
        · exact absurd hmem (List.not_mem_nil)
    | sym s =>
      cases b with
      | var y =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact ha
        · exact absurd hmem (List.not_mem_nil)
      | sym t =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        by_cases hst : (s == t) = true
        · rw [if_pos hst] at hdecompose
          cases hdecompose
          intro c hc
          exact absurd hc (List.not_mem_nil)
        · rw [if_neg hst] at hdecompose
          cases hdecompose
      | gnd g => simp [Metta.Unify.decomposeEq] at hdecompose
      | expr ys => simp [Metta.Unify.decomposeEq] at hdecompose
    | gnd g =>
      cases b with
      | var y =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact ha
        · exact absurd hmem (List.not_mem_nil)
      | sym t => simp [Metta.Unify.decomposeEq] at hdecompose
      | gnd g' =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        by_cases hg : (Metta.Ground.equiv g g') = true
        · rw [if_pos hg] at hdecompose
          cases hdecompose
          intro c hc
          exact absurd hc (List.not_mem_nil)
        · rw [if_neg hg] at hdecompose
          cases hdecompose
      | expr ys => simp [Metta.Unify.decomposeEq] at hdecompose
    | expr xs =>
      cases b with
      | var y =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        cases hdecompose
        intro c hc
        rcases List.mem_cons.mp hc with heq | hmem
        · subst heq; exact ha
        · exact absurd hmem (List.not_mem_nil)
      | sym t => simp [Metta.Unify.decomposeEq] at hdecompose
      | gnd g => simp [Metta.Unify.decomposeEq] at hdecompose
      | expr ys =>
        simp only [Metta.Unify.decomposeEq] at hdecompose
        exact hlist xs ys constraints hsize
          (leaAtomHEImage_children ha)
          (leaAtomHEImage_children hb) hdecompose

private theorem decomposeAll_image :
    ∀ {equations : List (Metta.Atom × Metta.Atom)}
      {constraints : List (Metta.VarName × Metta.Atom)},
      (∀ e ∈ equations, LeaAtomHEImage e.1 ∧ LeaAtomHEImage e.2) →
      Metta.Unify.decomposeAll equations = some constraints →
      ∀ c ∈ constraints, LeaAtomHEImage c.2 := by
  intro equations
  induction equations with
  | nil =>
    intro constraints _ hdec
    simp only [Metta.Unify.decomposeAll, Option.some.injEq] at hdec
    subst hdec
    intro c hc
    exact absurd hc (List.not_mem_nil)
  | cons eq rest ih =>
    intro constraints himage hdec
    simp only [Metta.Unify.decomposeAll] at hdec
    cases hhead : Metta.Unify.decomposeEq eq.1 eq.2 with
    | none => rw [hhead] at hdec; cases hdec
    | some cHead =>
      cases htail : Metta.Unify.decomposeAll rest with
      | none => rw [hhead, htail] at hdec; cases hdec
      | some cTail =>
        rw [hhead, htail] at hdec
        cases hdec
        intro c hc
        rcases List.mem_append.mp hc with hmem | hmem
        · have := himage eq List.mem_cons_self
          exact decomposeEq_image (eq.1.size + eq.2.size) eq.1 eq.2
            cHead le_rfl this.1 this.2 hhead c hmem
        · exact ih (fun e he => himage e (List.mem_cons_of_mem _ he))
            htail c hmem

private theorem substErase_subset {subst : Metta.Subst} {x : String} :
    ∀ p ∈ Metta.Subst.erase subst x, p ∈ subst := by
  intro p hp
  have hfilter : p ∈ subst.filter (fun q => q.1 != x) := by
    simpa [Metta.Subst.erase] using hp
  exact (List.mem_filter.mp hfilter).1

private theorem substExtend_image {subst : Metta.Subst} {x : String}
    {t : Metta.Atom} (hsubst : MettaSubstHEImage subst)
    (ht : LeaAtomHEImage t) :
    MettaSubstHEImage (Metta.Subst.extend subst x t) := by
  intro p hp
  simp only [Metta.Subst.extend] at hp
  rcases List.mem_cons.mp hp with heq | hmem
  · subst heq; exact ht
  · exact hsubst p (substErase_subset p hmem)

/-- Every substitution value emitted by LeaTTa's own unification loop on an
image-valued problem is in the translation image. -/
theorem unifyRounds_result_image
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hequations : ∀ e ∈ equations,
      LeaAtomHEImage e.1 ∧ LeaAtomHEImage e.2)
    (hsubst : MettaSubstHEImage subst)
    (hunify : Metta.Unify.unifyRounds fuel equations subst = some result) :
    MettaSubstHEImage result := by
  induction fuel generalizing equations subst result with
  | zero =>
    cases hdecompose : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.unifyRounds, hdecompose] at hunify
    | some constraints =>
      cases constraints with
      | nil =>
        simp [Metta.Unify.unifyRounds, hdecompose] at hunify
        subst result
        exact hsubst
      | cons constraint rest =>
        simp [Metta.Unify.unifyRounds, hdecompose] at hunify
  | succ fuel ih =>
    cases hdecompose : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.unifyRounds, hdecompose] at hunify
    | some constraints =>
      cases constraints with
      | nil =>
        simp [Metta.Unify.unifyRounds, hdecompose] at hunify
        subst result
        exact hsubst
      | cons constraint rest =>
        obtain ⟨x, term⟩ := constraint
        cases hoccurs : Metta.Subst.occurs x term with
        | true =>
          simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hunify
        | false =>
          have hconstraints := decomposeAll_image hequations hdecompose
          have hterm : LeaAtomHEImage term :=
            hconstraints (x, term) (by simp)
          have hsingleton : MettaSubstHEImage [(x, term)] := by
            intro p hp
            rcases List.mem_cons.mp hp with heq | hmem
            · subst heq; exact hterm
            · exact absurd hmem (List.not_mem_nil)
          have hunify' :
              Metta.Unify.unifyRounds fuel
                  (rest.map fun p =>
                    (Metta.Subst.apply [(x, term)] (.var p.1),
                      Metta.Subst.apply [(x, term)] p.2))
                  (Metta.Subst.extend subst x term) = some result := by
            simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs]
              using hunify
          apply ih ?_ (substExtend_image hsubst hterm) hunify'
          intro e he
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
          constructor
          · exact substApply_image hsingleton _ (leaAtomHEImage_var p.1)
          · exact substApply_image hsingleton _
              (hconstraints p (List.mem_cons_of_mem _ hp))

/-! ## Image provenance through reconciliation and merge -/

theorem leaBindingsHEImage_empty : LeaBindingsHEImage [] := by
  intro x v hv
  exact absurd hv (List.not_mem_nil)

private theorem leaBindingEquations_image
    {lb : Metta.Bindings} (himage : LeaBindingsHEImage lb) :
    ∀ e ∈ Metta.Bindings.equations lb,
      LeaAtomHEImage e.1 ∧ LeaAtomHEImage e.2 := by
  intro e he
  unfold Metta.Bindings.equations at he
  obtain ⟨rel, hrel, hrel_eq⟩ := List.mem_map.mp he
  cases rel with
  | val x v =>
    subst hrel_eq
    exact ⟨leaAtomHEImage_var x, himage x v hrel⟩
  | eq x y =>
    subst hrel_eq
    exact ⟨leaAtomHEImage_var x, leaAtomHEImage_var y⟩

/-- Every substitution value emitted by a successful whole-system
reconciliation of image inputs is in the translation image. -/
theorem wholeBindingReconciliation_result_image
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindings : LeaBindingsHEImage bindings)
    (hextra : ∀ e ∈ extra, LeaAtomHEImage e.1 ∧ LeaAtomHEImage e.2)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    MettaSubstHEImage result := by
  have himage : ∀ e ∈ Metta.Bindings.equations bindings ++ extra,
      LeaAtomHEImage e.1 ∧ LeaAtomHEImage e.2 := by
    intro e he
    rcases List.mem_append.mp he with hmem | hmem
    · exact leaBindingEquations_image hbindings e hmem
    · exact hextra e hmem
  have hrun : Metta.Unify.unifyRounds
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations bindings ++ extra))
      (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll]
      using hreconcile
  exact unifyRounds_result_image himage
    (by intro p hp; exact absurd hp (List.not_mem_nil)) hrun

private theorem ofSubst_image {sigma : Metta.Subst}
    (hsigma : MettaSubstHEImage sigma) :
    LeaBindingsHEImage (Metta.Bindings.ofSubst sigma) := by
  intro x v hv
  unfold Metta.Bindings.ofSubst at hv
  obtain ⟨pair, hpair, hpair_eq⟩ := List.mem_map.mp hv
  cases hval : pair.2 with
  | var y =>
    rw [hval] at hpair_eq
    simp only [] at hpair_eq
    cases hpair_eq
  | sym s =>
    rw [hval] at hpair_eq
    simp only [] at hpair_eq
    cases hpair_eq
    have := hsigma pair hpair
    rw [hval] at this
    exact this
  | gnd g =>
    rw [hval] at hpair_eq
    simp only [] at hpair_eq
    cases hpair_eq
    have := hsigma pair hpair
    rw [hval] at this
    exact this
  | expr xs =>
    rw [hval] at hpair_eq
    simp only [] at hpair_eq
    cases hpair_eq
    have := hsigma pair hpair
    rw [hval] at this
    exact this

private theorem equalitySkeleton_image (lb : Metta.Bindings) :
    LeaBindingsHEImage (Metta.Bindings.equalitySkeleton lb) := by
  intro x v hv
  exfalso
  induction lb with
  | nil => simp [Metta.Bindings.equalitySkeleton] at hv
  | cons rel rest ih =>
    cases rel with
    | val y w =>
      simp only [Metta.Bindings.equalitySkeleton] at hv
      exact ih hv
    | eq y z =>
      simp only [Metta.Bindings.equalitySkeleton] at hv
      rcases List.mem_cons.mp hv with heq | hmem
      · cases heq
      · exact ih hmem

private theorem leaBindingsHEImage_append
    {left right : Metta.Bindings}
    (hleft : LeaBindingsHEImage left) (hright : LeaBindingsHEImage right) :
    LeaBindingsHEImage (left ++ right) := by
  intro x v hv
  rcases List.mem_append.mp hv with hmem | hmem
  · exact hleft x v hmem
  · exact hright x v hmem

private theorem addEqRaw_image {lb : Metta.Bindings}
    (himage : LeaBindingsHEImage lb) (x y : String) :
    LeaBindingsHEImage (Metta.Bindings.addEqRaw lb x y) := by
  intro z v hv
  unfold Metta.Bindings.addEqRaw at hv
  split at hv
  · exact himage z v hv
  · rcases List.mem_cons.mp hv with heq | hmem
    · cases heq
    · exact himage z v hmem

private theorem addValRaw_image {lb : Metta.Bindings}
    (himage : LeaBindingsHEImage lb) {x : String} {value : Metta.Atom}
    (hvalue : LeaAtomHEImage value) :
    LeaBindingsHEImage (Metta.Bindings.addValRaw lb x value) := by
  intro z v hv
  unfold Metta.Bindings.addValRaw at hv
  rcases List.mem_cons.mp hv with heq | hmem
  · cases heq
    exact hvalue
  · unfold Metta.Bindings.removeVal at hmem
    exact himage z v (List.mem_filter.mp hmem).1

private theorem restoreAlias_image {lb : Metta.Bindings}
    (himage : LeaBindingsHEImage lb) (edge : String × String) :
    LeaBindingsHEImage (Metta.Bindings.restoreAlias lb edge) := by
  unfold Metta.Bindings.restoreAlias
  split
  · exact himage
  · exact addEqRaw_image himage edge.1 edge.2

private theorem restoreAliases_image
    {aliases : List (String × String)} :
    ∀ {lb : Metta.Bindings}, LeaBindingsHEImage lb →
      LeaBindingsHEImage (aliases.foldl Metta.Bindings.restoreAlias lb) := by
  induction aliases with
  | nil => intro lb himage; exact himage
  | cons edge rest ih =>
    intro lb himage
    simp only [List.foldl_cons]
    exact ih (restoreAlias_image himage edge)

private theorem rebuildFromReconciliation_image
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {sigma : Metta.Subst}
    (hsigma : MettaSubstHEImage sigma) :
    LeaBindingsHEImage
      (Metta.Bindings.rebuildFromReconciliation candidate source
        extra sigma) := by
  unfold Metta.Bindings.rebuildFromReconciliation
    Metta.Bindings.rebuildFromSubst
  exact restoreAliases_image
    (leaBindingsHEImage_append (equalitySkeleton_image candidate)
      (ofSubst_image hsigma))

private theorem addVarEquality_image
    {lb out : Metta.Bindings} (himage : LeaBindingsHEImage lb)
    {x y : String}
    (hout : out ∈ Metta.Bindings.addVarEquality lb x y) :
    LeaBindingsHEImage out := by
  unfold Metta.Bindings.addVarEquality at hout
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues (Metta.Bindings.addEqRaw lb x y) x) with
  | none =>
    simp only [hunify] at hout
    exact absurd hout (List.not_mem_nil)
  | some result =>
    simp only [hunify] at hout
    cases result with
    | nil =>
      rcases List.mem_cons.mp hout with heq | hmem
      · subst heq
        exact addEqRaw_image himage x y
      · exact absurd hmem (List.not_mem_nil)
    | cons c rest =>
      cases hreconcile : Metta.Bindings.reconcileAll lb
          [(Metta.Atom.var x, Metta.Atom.var y)] with
      | none =>
        simp only [hreconcile] at hout
        exact absurd hout (List.not_mem_nil)
      | some sigma =>
        simp only [hreconcile] at hout
        rcases List.mem_cons.mp hout with heq | hmem
        · subst heq
          apply rebuildFromReconciliation_image
          have hrun : wholeBindingReconciliation lb
              [(Metta.Atom.var x, Metta.Atom.var y)] = some sigma := by
            simpa [wholeBindingReconciliation] using hreconcile
          exact wholeBindingReconciliation_result_image himage
            (by
              intro e he
              rcases List.mem_cons.mp he with heq' | hmem'
              · subst heq'
                exact ⟨leaAtomHEImage_var x, leaAtomHEImage_var y⟩
              · exact absurd hmem' (List.not_mem_nil))
            hrun
        · exact absurd hmem (List.not_mem_nil)

private theorem addVarBinding_image
    {lb out : Metta.Bindings} (himage : LeaBindingsHEImage lb)
    {x : String} {value : Metta.Atom} (hvalue : LeaAtomHEImage value)
    (hout : out ∈ Metta.Bindings.addVarBinding lb x value) :
    LeaBindingsHEImage out := by
  unfold Metta.Bindings.addVarBinding at hout
  cases value with
  | var y => exact addVarEquality_image himage hout
  | sym s =>
    cases hvalues : Metta.Bindings.classValues lb x with
    | nil =>
      rw [hvalues] at hout
      rcases List.mem_cons.mp hout with heq | hmem
      · subst heq
        exact addValRaw_image himage hvalue
      · exact absurd hmem (List.not_mem_nil)
    | cons v vs =>
      rw [hvalues] at hout
      simp only [List.cons_append] at hout
      cases hunify : Metta.Bindings.unifyValues
          (v :: (vs ++ [Metta.Atom.sym s])) with
      | none =>
        simp only [hunify] at hout
        exact absurd hout (List.not_mem_nil)
      | some result =>
        simp only [hunify] at hout
        cases result with
        | nil =>
          rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact himage
          · exact absurd hmem (List.not_mem_nil)
        | cons c rest =>
          cases hreconcile : Metta.Bindings.reconcileAll lb
              [(Metta.Atom.var x, Metta.Atom.sym s)] with
          | none =>
            simp only [hreconcile] at hout
            exact absurd hout (List.not_mem_nil)
          | some sigma =>
            simp only [hreconcile] at hout
            rcases List.mem_cons.mp hout with heq | hmem
            · subst heq
              apply rebuildFromReconciliation_image
              have hrun : wholeBindingReconciliation lb
                  [(Metta.Atom.var x, Metta.Atom.sym s)] = some sigma := by
                simpa [wholeBindingReconciliation] using hreconcile
              refine wholeBindingReconciliation_result_image himage ?_ hrun
              intro e he
              rcases List.mem_cons.mp he with heq' | hmem'
              · subst heq'
                constructor
                · exact leaAtomHEImage_var x
                · exact hvalue
              · exact absurd hmem' (List.not_mem_nil)
            · exact absurd hmem (List.not_mem_nil)
  | gnd g =>
    cases hvalues : Metta.Bindings.classValues lb x with
    | nil =>
      rw [hvalues] at hout
      rcases List.mem_cons.mp hout with heq | hmem
      · subst heq
        exact addValRaw_image himage hvalue
      · exact absurd hmem (List.not_mem_nil)
    | cons v vs =>
      rw [hvalues] at hout
      simp only [List.cons_append] at hout
      cases hunify : Metta.Bindings.unifyValues
          (v :: (vs ++ [Metta.Atom.gnd g])) with
      | none =>
        simp only [hunify] at hout
        exact absurd hout (List.not_mem_nil)
      | some result =>
        simp only [hunify] at hout
        cases result with
        | nil =>
          rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact himage
          · exact absurd hmem (List.not_mem_nil)
        | cons c rest =>
          cases hreconcile : Metta.Bindings.reconcileAll lb
              [(Metta.Atom.var x, Metta.Atom.gnd g)] with
          | none =>
            simp only [hreconcile] at hout
            exact absurd hout (List.not_mem_nil)
          | some sigma =>
            simp only [hreconcile] at hout
            rcases List.mem_cons.mp hout with heq | hmem
            · subst heq
              apply rebuildFromReconciliation_image
              have hrun : wholeBindingReconciliation lb
                  [(Metta.Atom.var x, Metta.Atom.gnd g)] = some sigma := by
                simpa [wholeBindingReconciliation] using hreconcile
              refine wholeBindingReconciliation_result_image himage ?_ hrun
              intro e he
              rcases List.mem_cons.mp he with heq' | hmem'
              · subst heq'
                constructor
                · exact leaAtomHEImage_var x
                · exact hvalue
              · exact absurd hmem' (List.not_mem_nil)
            · exact absurd hmem (List.not_mem_nil)
  | expr atoms =>
    cases hvalues : Metta.Bindings.classValues lb x with
    | nil =>
      rw [hvalues] at hout
      rcases List.mem_cons.mp hout with heq | hmem
      · subst heq
        exact addValRaw_image himage hvalue
      · exact absurd hmem (List.not_mem_nil)
    | cons v vs =>
      rw [hvalues] at hout
      simp only [List.cons_append] at hout
      cases hunify : Metta.Bindings.unifyValues
          (v :: (vs ++ [Metta.Atom.expr atoms])) with
      | none =>
        simp only [hunify] at hout
        exact absurd hout (List.not_mem_nil)
      | some result =>
        simp only [hunify] at hout
        cases result with
        | nil =>
          rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact himage
          · exact absurd hmem (List.not_mem_nil)
        | cons c rest =>
          cases hreconcile : Metta.Bindings.reconcileAll lb
              [(Metta.Atom.var x, Metta.Atom.expr atoms)] with
          | none =>
            simp only [hreconcile] at hout
            exact absurd hout (List.not_mem_nil)
          | some sigma =>
            simp only [hreconcile] at hout
            rcases List.mem_cons.mp hout with heq | hmem
            · subst heq
              apply rebuildFromReconciliation_image
              have hrun : wholeBindingReconciliation lb
                  [(Metta.Atom.var x, Metta.Atom.expr atoms)] =
                    some sigma := by
                simpa [wholeBindingReconciliation] using hreconcile
              refine wholeBindingReconciliation_result_image himage ?_ hrun
              intro e he
              rcases List.mem_cons.mp he with heq' | hmem'
              · subst heq'
                constructor
                · exact leaAtomHEImage_var x
                · exact hvalue
              · exact absurd hmem' (List.not_mem_nil)
            · exact absurd hmem (List.not_mem_nil)

private theorem mergeOne_image
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaBindingsHEImage seed)
    (hrelation : ∀ x v, relation = Metta.BindingRel.val x v →
      LeaAtomHEImage v)
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    LeaBindingsHEImage out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hseedOut⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val x v =>
    exact addVarBinding_image (hseeds seed hseed)
      (hrelation x v rfl) hseedOut
  | eq x y => exact addVarEquality_image (hseeds seed hseed) hseedOut

/-- **Merge image preservation.**  Every successful merge of image-valued
binding records is image-valued. -/
theorem leaMerge_result_image
    {left right out : Metta.Bindings}
    (hleft : LeaBindingsHEImage left) (hright : LeaBindingsHEImage right)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaBindingsHEImage out := by
  unfold Metta.Bindings.merge at hout
  suffices key : ∀ (relations : List Metta.BindingRel)
      (seeds : List Metta.Bindings),
      (∀ seed ∈ seeds, LeaBindingsHEImage seed) →
      (∀ rel ∈ relations, ∀ x v,
        rel = Metta.BindingRel.val x v → LeaAtomHEImage v) →
      ∀ result ∈ relations.foldl Metta.Bindings.mergeOne seeds,
        LeaBindingsHEImage result by
    apply key right [left]
    · intro seed hseed
      rw [List.mem_singleton] at hseed
      subst hseed
      exact hleft
    · intro rel hrel x v hrelEq
      subst hrelEq
      exact hright x v hrel
    · exact hout
  intro relations
  induction relations with
  | nil =>
    intro seeds hseeds _ result hresult
    exact hseeds result hresult
  | cons rel rest ih =>
    intro seeds hseeds hrelations result hresult
    simp only [List.foldl_cons] at hresult
    apply ih (Metta.Bindings.mergeOne seeds rel) ?_ ?_ result hresult
    · intro seed hseed
      exact mergeOne_image hseeds
        (fun x v hrelEq =>
          hrelations rel List.mem_cons_self x v hrelEq) hseed
    · intro r hr x v hrelEq
      exact hrelations r (List.mem_cons_of_mem _ hr) x v hrelEq

/-! ## Image provenance through the repaired matcher -/

private theorem matchAtomsWith_image :
    ∀ (n : Nat) (l r : Metta.Atom) (out : Metta.Bindings),
      l.size + r.size ≤ n →
      LeaAtomHEImage l → LeaAtomHEImage r →
      out ∈ Metta.matchAtomsWith none l r →
      LeaBindingsHEImage out := by
  intro n
  induction n with
  | zero =>
    intro l r out hsize
    exact absurd hsize (by
      have := image_size_pos l
      have := image_size_pos r
      omega)
  | succ n ihn =>
    intro l r out hsize hl hr hout
    have hall : ∀ (xs ys : List Metta.Atom)
        (acc : List Metta.Bindings) (result : Metta.Bindings),
        (Metta.Atom.expr xs).size + (Metta.Atom.expr ys).size ≤ n + 1 →
        (∀ x ∈ xs, LeaAtomHEImage x) →
        (∀ y ∈ ys, LeaAtomHEImage y) →
        (∀ seed ∈ acc, LeaBindingsHEImage seed) →
        result ∈ Metta.matchAll none acc xs ys →
        LeaBindingsHEImage result := by
      intro xs
      induction xs with
      | nil =>
        intro ys acc result _ _ _ hacc hresult
        cases ys with
        | nil =>
          simp only [Metta.matchAll] at hresult
          exact hacc result hresult
        | cons y ytail =>
          simp only [Metta.matchAll] at hresult
          exact absurd hresult (List.not_mem_nil)
      | cons x xtail ihx =>
        intro ys acc result hsz hxs hys hacc hresult
        cases ys with
        | nil =>
          simp only [Metta.matchAll] at hresult
          exact absurd hresult (List.not_mem_nil)
        | cons y ytail =>
          simp only [Metta.matchAll] at hresult
          have hszTail : (Metta.Atom.expr xtail).size +
              (Metta.Atom.expr ytail).size ≤ n + 1 := by
            simp only [Metta.Atom.size, List.map_cons,
              List.sum_cons] at hsz ⊢
            have := image_size_pos x
            have := image_size_pos y
            omega
          apply ihx ytail _ result hszTail
            (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
            (fun z hz => hys z (List.mem_cons_of_mem _ hz))
            ?_ hresult
          intro seed hseed
          obtain ⟨a, ha, hseedInner⟩ := List.mem_flatMap.mp hseed
          obtain ⟨b, hb, hseedMerge⟩ := List.mem_flatMap.mp hseedInner
          have hbRaw : b ∈ Metta.matchAtomsWith none x y :=
            (List.mem_filter.mp hb).1
          have hxsize : x.size + y.size ≤ n := by
            have hx := image_size_lt_of_mem
              (List.mem_cons_self (a := x) (l := xtail))
            have hy := image_size_lt_of_mem
              (List.mem_cons_self (a := y) (l := ytail))
            simp only [Metta.Atom.size, List.map_cons,
              List.sum_cons] at hsz hx hy ⊢
            omega
          have hbImage : LeaBindingsHEImage b :=
            ihn x y b hxsize (hxs x List.mem_cons_self)
              (hys y List.mem_cons_self) hbRaw
          exact leaMerge_result_image (hacc a ha) hbImage hseedMerge
    cases l with
    | sym s =>
      cases r with
      | sym t =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | var y =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hl
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | gnd g =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | expr ys =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
    | var x =>
      cases r with
      | var y =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | sym t =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hr
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | gnd g =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hr
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | expr ys =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hr
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
    | gnd g =>
      cases r with
      | var y =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hl
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | sym t =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | gnd g' =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | expr ys =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
    | expr xs =>
      cases r with
      | var y =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · exact absurd hout (List.not_mem_nil)
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq
            intro z v hv
            rcases List.mem_cons.mp hv with heq' | hmem'
            · cases heq'
              exact hl
            · exact absurd hmem' (List.not_mem_nil)
          · exact absurd hmem (List.not_mem_nil)
      | sym t =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | gnd g =>
        simp only [Metta.matchAtomsWith] at hout
        split at hout
        · rcases List.mem_cons.mp hout with heq | hmem
          · subst heq; exact leaBindingsHEImage_empty
          · exact absurd hmem (List.not_mem_nil)
        · exact absurd hout (List.not_mem_nil)
      | expr ys =>
        simp only [Metta.matchAtomsWith] at hout
        exact hall xs ys [[]] out hsize
          (leaAtomHEImage_children hl)
          (leaAtomHEImage_children hr)
          (by
            intro seed hseed
            rcases List.mem_cons.mp hseed with heq | hmem
            · subst heq; exact leaBindingsHEImage_empty
            · exact absurd hmem (List.not_mem_nil))
          hout

/-- **Matcher image preservation.**  Every repaired-matcher output on image
inputs is image-valued. -/
theorem leaMatchAtoms_result_heImage
    {l r : Metta.Atom} {out : Metta.Bindings}
    (hl : LeaAtomHEImage l) (hr : LeaAtomHEImage r)
    (hout : out ∈ Metta.matchAtoms l r) :
    LeaBindingsHEImage out := by
  have hraw : out ∈ Metta.matchAtomsWith none l r := by
    have : out ∈ (Metta.matchAtomsWith none l r).filter
        (fun b => !b.hasLoop) := by
      simpa [Metta.matchAtoms] using hout
    exact (List.mem_filter.mp this).1
  exact matchAtomsWith_image (l.size + r.size) l r out le_rfl hl hr hraw

/-! ## Image provenance through the repaired type matcher -/

private theorem headFiltered_mem {l : List Metta.Bindings}
    {out : Metta.Bindings} (h : l.head? = some out) : out ∈ l := by
  cases l with
  | nil => simp at h
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

private theorem matchReduced_image :
    ∀ (n : Nat) (tb : Metta.Bindings) (expected actual : Metta.Atom)
      (out : Metta.Bindings),
      expected.size + actual.size ≤ n →
      LeaBindingsHEImage tb →
      LeaAtomHEImage expected → LeaAtomHEImage actual →
      Metta.Minimal.matchReduced tb expected actual = some out →
      LeaBindingsHEImage out := by
  intro n
  induction n with
  | zero =>
    intro tb expected actual out hsize
    exact absurd hsize (by
      have := image_size_pos expected
      have := image_size_pos actual
      omega)
  | succ n ihn =>
    intro tb expected actual out hsize htb hexpected hactual hmatch
    have hlist : ∀ (es acts : List Metta.Atom) (seed : Metta.Bindings)
        (result : Metta.Bindings),
        (Metta.Atom.expr es).size + (Metta.Atom.expr acts).size ≤ n + 1 →
        LeaBindingsHEImage seed →
        (∀ e ∈ es, LeaAtomHEImage e) →
        (∀ a ∈ acts, LeaAtomHEImage a) →
        Metta.Minimal.matchReducedList seed es acts = some result →
        LeaBindingsHEImage result := by
      intro es
      induction es with
      | nil =>
        intro acts seed result _ hseed _ _ hrun
        cases acts with
        | nil =>
          simp only [Metta.Minimal.matchReducedList,
            Option.some.injEq] at hrun
          subst hrun
          exact hseed
        | cons a atail =>
          simp [Metta.Minimal.matchReducedList] at hrun
      | cons e etail ihe =>
        intro acts seed result hsz hseed hes hacts hrun
        cases acts with
        | nil => simp [Metta.Minimal.matchReducedList] at hrun
        | cons a atail =>
          simp only [Metta.Minimal.matchReducedList] at hrun
          cases hhead : Metta.Minimal.matchReduced seed e a with
          | none => rw [hhead] at hrun; cases hrun
          | some seed' =>
            rw [hhead] at hrun
            have hesize : e.size + a.size ≤ n := by
              have he := image_size_lt_of_mem
                (List.mem_cons_self (a := e) (l := etail))
              have ha := image_size_lt_of_mem
                (List.mem_cons_self (a := a) (l := atail))
              simp only [Metta.Atom.size, List.map_cons,
                List.sum_cons] at hsz he ha ⊢
              omega
            have hseed' : LeaBindingsHEImage seed' :=
              ihn seed e a seed' hesize hseed
                (hes e List.mem_cons_self)
                (hacts a List.mem_cons_self) hhead
            have hszTail : (Metta.Atom.expr etail).size +
                (Metta.Atom.expr atail).size ≤ n + 1 := by
              simp only [Metta.Atom.size, List.map_cons,
                List.sum_cons] at hsz ⊢
              have := image_size_pos e
              have := image_size_pos a
              omega
            exact ihe atail seed' result hszTail hseed'
              (fun z hz => hes z (List.mem_cons_of_mem _ hz))
              (fun z hz => hacts z (List.mem_cons_of_mem _ hz)) hrun
    unfold Metta.Minimal.matchReduced at hmatch
    split at hmatch
    · cases hmatch
      exact htb
    · split at hmatch
      next es acts hne =>
        exact hlist es acts tb out hsize htb
          (leaAtomHEImage_children hexpected)
          (leaAtomHEImage_children hactual) hmatch
      next =>
        have hmem := headFiltered_mem hmatch
        have hmem' : out ∈ (Metta.matchAtoms expected actual).flatMap
            (Metta.Bindings.merge tb) :=
          (List.mem_filter.mp hmem).1
        obtain ⟨mb, hmb, hmerge⟩ := List.mem_flatMap.mp hmem'
        exact leaMerge_result_image htb
          (leaMatchAtoms_result_heImage hexpected hactual hmb) hmerge

/-- **Type-match image preservation.** -/
theorem matchType_result_heImage
    {tb : Metta.Bindings} {expected actual : Metta.Atom}
    {out : Metta.Bindings}
    (htb : LeaBindingsHEImage tb)
    (hexpected : LeaAtomHEImage expected)
    (hactual : LeaAtomHEImage actual)
    (hmatch : Metta.Minimal.matchType tb expected actual = some out) :
    LeaBindingsHEImage out := by
  unfold Metta.Minimal.matchType at hmatch
  split at hmatch
  · cases hmatch
    exact htb
  · exact matchReduced_image (expected.size + actual.size) tb expected
      actual out le_rfl htb hexpected hactual hmatch

/-- **The decisive theorem.**  A successful application-argument fold on
image inputs from an image-valued initial record yields an image-valued
output record. -/
theorem matchApplicationTypeArguments_result_heImage :
    ∀ {tb : Metta.Bindings} {expected actual : List Metta.Atom}
      {out : Metta.Bindings},
      LeaBindingsHEImage tb →
      (∀ e ∈ expected, LeaAtomHEImage e) →
      (∀ a ∈ actual, LeaAtomHEImage a) →
      Metta.Minimal.matchApplicationTypeArguments tb expected actual =
        some out →
      LeaBindingsHEImage out := by
  intro tb expected
  induction expected generalizing tb with
  | nil =>
    intro actual out htb _ _ hrun
    cases actual with
    | nil =>
      simp only [Metta.Minimal.matchApplicationTypeArguments,
        Option.some.injEq] at hrun
      subst hrun
      exact htb
    | cons a atail =>
      simp [Metta.Minimal.matchApplicationTypeArguments] at hrun
  | cons e etail ih =>
    intro actual out htb hes hacts hrun
    cases actual with
    | nil =>
      simp [Metta.Minimal.matchApplicationTypeArguments] at hrun
    | cons a atail =>
      simp only [Metta.Minimal.matchApplicationTypeArguments] at hrun
      cases hhead : Metta.Minimal.matchType tb e a with
      | none => rw [hhead] at hrun; cases hrun
      | some next =>
        rw [hhead] at hrun
        have hnext : LeaBindingsHEImage next :=
          matchType_result_heImage htb (hes e List.mem_cons_self)
            (hacts a List.mem_cons_self) hhead
        exact ih hnext
          (fun z hz => hes z (List.mem_cons_of_mem _ hz))
          (fun z hz => hacts z (List.mem_cons_of_mem _ hz)) hrun

/-! ## Image provenance through instantiation -/

private theorem lookupVal_mem_image :
    ∀ {lb : Metta.Bindings} {x : String} {a : Metta.Atom},
      Metta.Bindings.lookupVal lb x = some a →
      Metta.BindingRel.val x a ∈ lb
  | [], _, _, h => by simp [Metta.Bindings.lookupVal] at h
  | .val y v :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    by_cases hxy : (x == y) = true
    · rw [if_pos hxy] at h
      cases h
      have : x = y := by simpa using hxy
      subst this
      exact List.mem_cons_self
    · rw [if_neg hxy] at h
      exact List.mem_cons_of_mem _ (lookupVal_mem_image h)
  | .eq _ _ :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    exact List.mem_cons_of_mem _ (lookupVal_mem_image h)

private theorem classValues_image {lb : Metta.Bindings}
    (himage : LeaBindingsHEImage lb) {z : String} {v : Metta.Atom}
    (hv : v ∈ Metta.Bindings.classValues lb z) : LeaAtomHEImage v := by
  unfold Metta.Bindings.classValues at hv
  obtain ⟨y, _, hlookup⟩ := List.mem_filterMap.mp hv
  exact himage y v (lookupVal_mem_image hlookup)

private theorem mapM_image_pointwise
    {f : Metta.Atom → Option Metta.Atom} :
    ∀ (xs ys : List Metta.Atom),
      xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → LeaAtomHEImage y) →
      ∀ y ∈ ys, LeaAtomHEImage y
  | [], ys, h, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    intro y hy
    exact absurd hy (List.not_mem_nil)
  | x :: xs, ys, h, hpt => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        have hys : xr :: xsr = ys := by
          simpa [List.mapM_cons, hx, hxs] using h
        subst hys
        intro y hy
        rcases List.mem_cons.mp hy with heq | hmem
        · subst heq
          exact hpt x List.mem_cons_self _ hx
        · exact mapM_image_pointwise xs xsr hxs
            (fun z hz => hpt z (List.mem_cons_of_mem _ hz)) y hmem

private theorem resolveAtomAux_image
    {lb : Metta.Bindings} (himage : LeaBindingsHEImage lb) :
    ∀ (fuel : Nat) (visited : List String) (a r : Metta.Atom),
      LeaAtomHEImage a →
      Metta.Bindings.resolveAtomAux lb fuel visited a = some r →
      LeaAtomHEImage r := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a r _ h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a r ha h
    cases a with
    | sym s =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases h
      exact ha
    | gnd g =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases h
      exact ha
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      cases hmap : xs.mapM
          (Metta.Bindings.resolveAtomAux lb fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        rw [hmap] at h
        cases h
        rw [leaAtomHEImage_expr_iff]
        apply leaAtomsHEImage_of_forall
        exact mapM_image_pointwise xs ys hmap
          (fun z hz w hw =>
            ih visited z w (leaAtomHEImage_children ha z hz) hw)
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h
      by_cases hguard : ((Metta.Bindings.eqClassOrdered lb z).any
          visited.contains) = true
      · rw [if_pos hguard] at h
        cases h
      · rw [if_neg hguard] at h
        cases hvalues : Metta.Bindings.classValues lb z with
        | nil =>
          rw [hvalues] at h
          cases h
          exact leaAtomHEImage_var _
        | cons v rest =>
          rw [hvalues] at h
          have hvimage : LeaAtomHEImage v :=
            classValues_image himage (by
              rw [hvalues]; exact List.mem_cons_self)
          cases v with
          | var y =>
            by_cases hcontains : y ∈ Metta.Bindings.eqClassOrdered lb z
            · by_cases hlen :
                  (Metta.Bindings.eqClassOrdered lb z).length = 1
              · simp [hcontains, hlen] at h
              · have hsome : Metta.Atom.var
                    (Metta.Bindings.eqRepresentative lb z) = r := by
                  simpa [hcontains, hlen] using h
                subst hsome
                exact leaAtomHEImage_var _
            · have hrec : Metta.Bindings.resolveAtomAux lb fuel
                  (Metta.Bindings.eqClassOrdered lb z ++ visited)
                  (Metta.Atom.var y) = some r := by
                simpa [hcontains] using h
              exact ih _ _ _ hvimage hrec
          | sym s =>
            have hrec : Metta.Bindings.resolveAtomAux lb fuel
                (Metta.Bindings.eqClassOrdered lb z ++ visited)
                (Metta.Atom.sym s) = some r := by
              simpa using h
            exact ih _ _ _ hvimage hrec
          | gnd g =>
            have hrec : Metta.Bindings.resolveAtomAux lb fuel
                (Metta.Bindings.eqClassOrdered lb z ++ visited)
                (Metta.Atom.gnd g) = some r := by
              simpa using h
            exact ih _ _ _ hvimage hrec
          | expr atoms =>
            have hrec : Metta.Bindings.resolveAtomAux lb fuel
                (Metta.Bindings.eqClassOrdered lb z ++ visited)
                (Metta.Atom.expr atoms) = some r := by
              simpa using h
            exact ih _ _ _ hvimage hrec

/-- **Instantiation image preservation.**  Applying an image-valued binding
record to an image atom stays in the image, with no side conditions:
failure branches fall back to the input. -/
theorem instantiate_heImage
    {lb : Metta.Bindings} (hlb : LeaBindingsHEImage lb) :
    ∀ a : Metta.Atom, LeaAtomHEImage a →
      LeaAtomHEImage (Metta.instantiate lb a) := by
  suffices key : ∀ (n : Nat) (a : Metta.Atom), a.size ≤ n →
      LeaAtomHEImage a →
      LeaAtomHEImage (Metta.Bindings.resolveAtom lb a) by
    intro a ha
    exact key a.size a le_rfl ha
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := image_size_pos a; omega)
  | succ n ihn =>
    intro a hsize ha
    cases a with
    | sym s => simpa [Metta.Bindings.resolveAtom] using ha
    | gnd g => simpa [Metta.Bindings.resolveAtom] using ha
    | var x =>
      simp only [Metta.Bindings.resolveAtom]
      cases hres : Metta.Bindings.resolve lb x with
      | none => simpa using ha
      | some r =>
        simp only [Option.getD_some]
        have hres' : Metta.Bindings.resolveAtomAux lb
            (Metta.Bindings.resolutionFuel lb (Metta.Atom.var x)) []
            (Metta.Atom.var x) = some r := by
          by_cases hguard :
              ((Metta.Bindings.eqClassOrdered lb x == [x]) &&
                (Metta.Bindings.classValues lb x).isEmpty) = true
          · simp [Metta.Bindings.resolve, hguard] at hres
          · simpa [Metta.Bindings.resolve, hguard] using hres
        exact resolveAtomAux_image hlb _ _ _ _
          (leaAtomHEImage_var x) hres'
    | expr xs =>
      simp only [Metta.Bindings.resolveAtom]
      rw [leaAtomHEImage_expr_iff]
      apply leaAtomsHEImage_of_forall
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hlt := image_size_lt_of_mem hz
      exact ihn z (by omega) (leaAtomHEImage_children ha z hz)

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
