import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientFrame

/-!
# The pattern frame modulo the bag laws of quoted processes

`ReflQuotientFrame` compares patterns modulo the bag laws at every position (`BagLaws`, the frame `QX`).
That relation also equates the parallel bags of the **spine**: the bag a row's label is, and the bags of the
continuations that will become rows. Splitting such a bag into rows is then matching modulo associativity,
commutativity and unit, which is not unitary: a heating rule reads its made rows ambiguously
(`ReflQuotient.Controls.heat_reads_ambiguous`, and `ReflLocated.Controls.no_check_guard_at_quotient`).

Here the bag laws act **inside the quote constructors only**: a name `@P` (`MQuote`) and the term form of a
process (`MTermProc`). Inside a quote the full relation `BagLaws` applies, at every depth of the quoted
process. Outside the quotes terms are compared as written. This is the name equivalence of the reflective
higher-order calculus: two names are equal when the processes they quote are structurally equivalent. The
structural congruence of the spine is the business of the bag store and its housekeeping (heating and
clearing), as in the finite hosting.

## What is shown

* `NameRewrite`, `NameLaws`: one law of `BagLaws` under a quote, at any position; its equivalence closure.
  It is a congruence (`nameLaws_apply`, `nameLaws_collection`), contained in `BagLaws`
  (`bagLaws_of_nameLaws`).
* **Substitution respects it** (`nameLaws_psubst`), for all terms, unknowns included.
* **The canonical form** `nameCanon` (`bagCanon` under each quote, the spine kept) **decides it** on all
  terms: `nameLaws_iff`.
* **The frame** `QN = OneFrame.frames nameAction`.
* **Inversions**: an application is related only to an application of the same head
  (`nameLaws_heads`), argument by argument outside the quotes (`nameLaws_apply_iff`); a binary parallel bag
  only to a binary parallel bag, member by member (`nameLaws_pair_left`).
* **Controls**: names are compared modulo the bag laws (`names_modulo_bag_laws`, `terms_modulo_bag_laws`);
  the spine is not (`spine_as_written`), nor the process of a reflection, which steps rather than being quoted
  (`reflected_process_as_written`); `QX` relates both (`spine_related_at_bag_frame`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pPar pZero par nQuote pFor tProc pReflect demoChan)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none PSubst)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open ReflQuotient (BagLaws BagRewrite bagCanon bagLaws_iff bagLaws_bagCanon bagCanon_eq_of_bagLaws bagLaws_psubst
  bagLaws_apply)

/-! ## The relation -/

/-- **The quote constructors**: a name `@P` and the term form of a process. -/
def IsQuote (c : String) : Prop := c = "MQuote" ∨ c = "MTermProc"

instance (c : String) : Decidable (IsQuote c) := inferInstanceAs (Decidable (_ ∨ _))

/-- **One law under a quote, at one position.** Inside a quote the quoted processes are compared by the bag
laws at every depth (`BagLaws`); every constructor is a context. -/
inductive NameRewrite : Pattern → Pattern → Prop where
  | quote {c : String} (quoting : IsQuote c) {p q : Pattern} :
      BagLaws p q → NameRewrite (.apply c [p]) (.apply c [q])
  | apply (c : String) (pre post : List Pattern) {a b : Pattern} :
      NameRewrite a b → NameRewrite (.apply c (pre ++ a :: post)) (.apply c (pre ++ b :: post))
  | lambda (nm : Option String) {a b : Pattern} : NameRewrite a b → NameRewrite (.lambda nm a) (.lambda nm b)
  | multiLambda (n : Nat) (nms : List String) {a b : Pattern} :
      NameRewrite a b → NameRewrite (.multiLambda n nms a) (.multiLambda n nms b)
  | substBody (repl : Pattern) {a b : Pattern} : NameRewrite a b → NameRewrite (.subst a repl) (.subst b repl)
  | substRepl (body : Pattern) {a b : Pattern} : NameRewrite a b → NameRewrite (.subst body a) (.subst body b)
  | collection (ct : CollType) (pre post : List Pattern) (rest : Option String) {a b : Pattern} :
      NameRewrite a b →
        NameRewrite (.collection ct (pre ++ a :: post) rest) (.collection ct (pre ++ b :: post) rest)

/-- **Equality modulo the bag laws of quoted processes**: the equivalence closure of `NameRewrite`. -/
abbrev NameLaws : Pattern → Pattern → Prop := Relation.EqvGen NameRewrite

namespace NameLaws

theorem refl (p : Pattern) : NameLaws p p := Relation.EqvGen.refl p

theorem symm {p q : Pattern} (h : NameLaws p q) : NameLaws q p := Relation.EqvGen.symm _ _ h

theorem trans {p q r : Pattern} (h : NameLaws p q) (h' : NameLaws q r) : NameLaws p r :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_rewrite {p q : Pattern} (h : NameRewrite p q) : NameLaws p q := Relation.EqvGen.rel _ _ h

theorem equivalence : Equivalence NameLaws := Relation.EqvGen.is_equivalence _

/-- A context that carries one rewrite carries the relation. -/
theorem map {f : Pattern → Pattern} (step : ∀ {a b : Pattern}, NameRewrite a b → NameRewrite (f a) (f b))
    {p q : Pattern} (h : NameLaws p q) : NameLaws (f p) (f q) := by
  induction h with
  | rel a b r => exact of_rewrite (step r)
  | refl a => exact refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A context of lists: related members, position by position, give related wholes. -/
theorem list {wrap : List Pattern → Pattern}
    (step : ∀ (pre post : List Pattern) {a b : Pattern}, NameRewrite a b →
      NameRewrite (wrap (pre ++ a :: post)) (wrap (pre ++ b :: post)))
    {xs ys : List Pattern} (h : List.Forall₂ NameLaws xs ys) : NameLaws (wrap xs) (wrap ys) := by
  have general : ∀ pre : List Pattern, NameLaws (wrap (pre ++ xs)) (wrap (pre ++ ys)) := by
    induction h with
    | nil => intro pre; exact refl _
    | @cons a b l₁ l₂ hab _ ih =>
        intro pre
        have first : NameLaws (wrap (pre ++ a :: l₁)) (wrap (pre ++ b :: l₁)) :=
          map (f := fun z => wrap (pre ++ z :: l₁)) (fun r => step pre l₁ r) hab
        have second := ih (pre ++ [b])
        simp only [List.append_assoc, List.singleton_append] at second
        exact first.trans second
  have whole := general []
  simp only [List.nil_append] at whole
  exact whole

end NameLaws

theorem nameLaws_of_eq {p q : Pattern} (same : p = q) : NameLaws p q := same ▸ NameLaws.refl p

/-- The relation is a congruence for every application. -/
theorem nameLaws_apply (c : String) {xs ys : List Pattern} (h : List.Forall₂ NameLaws xs ys) :
    NameLaws (.apply c xs) (.apply c ys) :=
  NameLaws.list (wrap := fun L => .apply c L) (fun pre post _ _ r => .apply c pre post r) h

/-- The relation is a congruence for every collection. -/
theorem nameLaws_collection (ct : CollType) (rest : Option String) {xs ys : List Pattern}
    (h : List.Forall₂ NameLaws xs ys) : NameLaws (.collection ct xs rest) (.collection ct ys rest) :=
  NameLaws.list (wrap := fun L => .collection ct L rest) (fun pre post _ _ r => .collection ct pre post rest r) h

/-- **Names are compared modulo the bag laws of the processes they quote.** -/
theorem nameLaws_nQuote {p q : Pattern} (h : BagLaws p q) : NameLaws (nQuote p) (nQuote q) :=
  NameLaws.of_rewrite (.quote (.inl rfl) h)

/-- The term form of a process too. -/
theorem nameLaws_tProc {p q : Pattern} (h : BagLaws p q) : NameLaws (tProc p) (tProc q) :=
  NameLaws.of_rewrite (.quote (.inr rfl) h)

/-- **The relation is contained in the bag laws.** -/
theorem bagLaws_of_nameRewrite {p q : Pattern} (h : NameRewrite p q) : BagLaws p q := by
  induction h with
  | quote _ same => exact bagLaws_apply _ (.cons same .nil)
  | apply c pre post _ ih => exact BagLaws.map (f := fun z => .apply c (pre ++ z :: post)) (fun r => .apply c pre post r) ih
  | lambda nm _ ih => exact BagLaws.map (f := .lambda nm) (fun r => .lambda nm r) ih
  | multiLambda n nms _ ih => exact BagLaws.map (f := .multiLambda n nms) (fun r => .multiLambda n nms r) ih
  | substBody repl _ ih => exact BagLaws.map (f := fun z => .subst z repl) (fun r => .substBody repl r) ih
  | substRepl body _ ih => exact BagLaws.map (f := fun z => .subst body z) (fun r => .substRepl body r) ih
  | collection ct pre post rest _ ih =>
      exact BagLaws.map (f := fun z => .collection ct (pre ++ z :: post) rest) (fun r => .collection ct pre post rest r) ih

theorem bagLaws_of_nameLaws {p q : Pattern} (h : NameLaws p q) : BagLaws p q := by
  induction h with
  | rel a b r => exact bagLaws_of_nameRewrite r
  | refl a => exact BagLaws.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Substitution respects the relation -/

/-- Substitution commutes with every context, and instances of the bag laws under a quote are such. -/
theorem nameRewrite_psubst (σ : PSubst) {p q : Pattern} (h : NameRewrite p q) :
    NameRewrite (psubst σ p) (psubst σ q) := by
  induction h with
  | quote quoting same =>
      simp only [psubst, psubstList_eq_map, List.map_cons, List.map_nil]
      exact .quote quoting (bagLaws_psubst σ same)
  | apply c pre post _ ih =>
      simp only [psubst, psubstList_eq_map, List.map_append, List.map_cons]
      exact .apply c _ _ ih
  | lambda nm _ ih =>
      simp only [psubst]
      exact .lambda nm ih
  | multiLambda n nms _ ih =>
      simp only [psubst]
      exact .multiLambda n nms ih
  | substBody repl _ ih =>
      simp only [psubst]
      exact .substBody _ ih
  | substRepl body _ ih =>
      simp only [psubst]
      exact .substRepl _ ih
  | collection ct pre post rest _ ih =>
      simp only [psubst, psubstList_eq_map, List.map_append, List.map_cons]
      exact .collection ct _ _ rest ih

/-- **Substitution respects equality modulo the bag laws of quoted processes**, for all terms. -/
theorem nameLaws_psubst (σ : PSubst) {p q : Pattern} (h : NameLaws p q) :
    NameLaws (psubst σ p) (psubst σ q) :=
  NameLaws.map (fun r => nameRewrite_psubst σ r) h

/-! ## The canonical form -/

mutual
/-- **The canonical form modulo the bag laws of quoted processes**: `bagCanon` under every quote, the spine
kept as written. -/
def nameCanon : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args =>
      if IsQuote c ∧ args.length = 1 then .apply c (args.map bagCanon) else .apply c (nameCanonList args)
  | .lambda nm body => .lambda nm (nameCanon body)
  | .multiLambda n nms body => .multiLambda n nms (nameCanon body)
  | .subst body repl => .subst (nameCanon body) (nameCanon repl)
  | .collection ct elems rest => .collection ct (nameCanonList elems) rest
/-- The canonical forms of a list, in order. -/
def nameCanonList : List Pattern → List Pattern
  | [] => []
  | p :: ps => nameCanon p :: nameCanonList ps
end

theorem nameCanonList_eq_map (ps : List Pattern) : nameCanonList ps = ps.map nameCanon := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [nameCanonList, ih]

theorem nameCanon_apply (c : String) (args : List Pattern) :
    nameCanon (.apply c args) =
      if IsQuote c ∧ args.length = 1 then .apply c (args.map bagCanon) else .apply c (args.map nameCanon) := by
  rw [nameCanon, nameCanonList_eq_map]

theorem nameCanon_quote {c : String} (quoting : IsQuote c) (p : Pattern) :
    nameCanon (.apply c [p]) = .apply c [bagCanon p] := by
  rw [nameCanon_apply, if_pos ⟨quoting, rfl⟩]
  rfl

theorem nameCanon_apply_of_not_quote {c : String} (other : ¬ IsQuote c) (args : List Pattern) :
    nameCanon (.apply c args) = .apply c (args.map nameCanon) := by
  rw [nameCanon_apply, if_neg fun h => other h.1]

theorem nameCanon_collection (ct : CollType) (elems : List Pattern) (rest : Option String) :
    nameCanon (.collection ct elems rest) = .collection ct (elems.map nameCanon) rest := by
  rw [nameCanon, nameCanonList_eq_map]

/-- One rewrite keeps the canonical form. -/
theorem nameCanon_nameRewrite {p q : Pattern} (h : NameRewrite p q) : nameCanon p = nameCanon q := by
  induction h with
  | quote quoting same => rw [nameCanon_quote quoting, nameCanon_quote quoting, bagCanon_eq_of_bagLaws same]
  | @apply c pre post a b r ih =>
      rw [nameCanon_apply, nameCanon_apply]
      have lengths : (IsQuote c ∧ (pre ++ a :: post).length = 1) ↔ (IsQuote c ∧ (pre ++ b :: post).length = 1) := by
        simp
      by_cases quoteOne : IsQuote c ∧ (pre ++ a :: post).length = 1
      · rw [if_pos quoteOne, if_pos (lengths.mp quoteOne)]
        simp only [List.map_append, List.map_cons, bagCanon_eq_of_bagLaws (bagLaws_of_nameRewrite r)]
      · rw [if_neg quoteOne, if_neg fun h => quoteOne (lengths.mpr h)]
        simp only [List.map_append, List.map_cons, ih]
  | lambda nm _ ih => simp only [nameCanon, ih]
  | multiLambda n nms _ ih => simp only [nameCanon, ih]
  | substBody repl _ ih => simp only [nameCanon, ih]
  | substRepl body _ ih => simp only [nameCanon, ih]
  | collection ct pre post rest _ ih =>
      simp only [nameCanon_collection, List.map_append, List.map_cons, ih]

theorem nameCanon_eq_of_nameLaws {p q : Pattern} (h : NameLaws p q) : nameCanon p = nameCanon q := by
  induction h with
  | rel a b r => exact nameCanon_nameRewrite r
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Members related to their images give the image list, position by position. -/
theorem forall₂_of_forall {f : Pattern → Pattern} :
    ∀ {xs : List Pattern}, (∀ q ∈ xs, NameLaws q (f q)) → List.Forall₂ NameLaws xs (xs.map f)
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self)
      (forall₂_of_forall fun q member => h q (List.mem_cons_of_mem _ member))

/-- **Every term is equal to its canonical form** modulo the bag laws of quoted processes. -/
theorem nameLaws_nameCanon (p : Pattern) : NameLaws p (nameCanon p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, NameLaws q (nameCanon q)) with
  | bvar n => exact NameLaws.refl _
  | fvar x => exact NameLaws.refl _
  | apply c args ih =>
      rw [nameCanon_apply]
      split_ifs with quoteOne
      · obtain ⟨quoting, one⟩ := quoteOne
        match args, one with
        | [p], _ => exact NameLaws.of_rewrite (.quote quoting (bagLaws_bagCanon p))
      · exact nameLaws_apply c (forall₂_of_forall ih)
  | lambda nm body ih => exact NameLaws.map (f := .lambda nm) (fun r => .lambda nm r) ih
  | multiLambda n nms body ih => exact NameLaws.map (f := .multiLambda n nms) (fun r => .multiLambda n nms r) ih
  | subst body repl ihb ihr =>
      exact (NameLaws.map (f := fun a => .subst a repl) (fun r => .substBody repl r) ihb).trans
        (NameLaws.map (f := fun a => .subst (nameCanon body) a) (fun r => .substRepl (nameCanon body) r) ihr)
  | collection ct elems rest ih =>
      rw [nameCanon_collection]
      exact nameLaws_collection ct rest (forall₂_of_forall ih)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-- **The canonical form decides the relation**, on all terms, unknowns included. -/
theorem nameLaws_iff (p q : Pattern) : NameLaws p q ↔ nameCanon p = nameCanon q := by
  refine ⟨nameCanon_eq_of_nameLaws, fun same => (nameLaws_nameCanon p).trans ?_⟩
  rw [same]
  exact (nameLaws_nameCanon q).symm

instance : DecidableRel NameLaws := fun p q => decidable_of_iff _ (nameLaws_iff p q).symm

/-! ## The frame -/

/-- **Structural substitution on patterns, names compared modulo the bag laws of the processes they
quote.** The same terms, substitutions and action as `patternAction`; the equality is `NameLaws`. -/
def nameAction : SubstitutionAction Pattern PSubst where
  E := NameLaws
  equivalence := NameLaws.equivalence
  apply := psubst
  identity := fun _ => none
  compose := pcomp
  apply_identity := psubst_none
  apply_compose outer inner t := (psubst_comp outer inner t).symm
  preserves σ {_ _} same := nameLaws_psubst σ same

/-- **The name frame**: the one frame of structural substitution on patterns, names compared modulo the
bag laws of the processes they quote. -/
abbrev QN : Interface.Frames (OneFrame.Terms Pattern) (fun _ _ : PUnit.{1} => PSubst) :=
  OneFrame.frames nameAction

/-- Firings at the name frame move along the identity. -/
abbrev QNE : Extensions.{0, 0, 0} (fun _ _ : PUnit.{1} => PSubst) := OneFrame.ext nameAction

/-- What a solution says at the name frame: the canonical forms of the two sides, read through it, agree. -/
theorem solves_iff (σ : PSubst) (e : Equation Pattern) :
    nameAction.Solves σ e ↔ nameCanon (psubst σ e.1) = nameCanon (psubst σ e.2) :=
  nameLaws_iff (psubst σ e.1) (psubst σ e.2)

/-! ## Inversions -/

/-- The canonical form of an application is an application of the same head. -/
theorem nameCanon_apply_head (c : String) (args : List Pattern) :
    ∃ args' : List Pattern, nameCanon (.apply c args) = .apply c args' := by
  rw [nameCanon_apply]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **An application is related only to an application of the same head.** -/
theorem nameLaws_heads {c d : String} {xs ys : List Pattern} (h : NameLaws (.apply c xs) (.apply d ys)) :
    c = d := by
  obtain ⟨xs', hx⟩ := nameCanon_apply_head c xs
  obtain ⟨ys', hy⟩ := nameCanon_apply_head d ys
  have same := nameCanon_eq_of_nameLaws h
  rw [hx, hy] at same
  exact (Pattern.apply.inj same).1

/-- Equal images under the canonical form, position by position. -/
theorem forall₂_of_map_eq : ∀ {xs ys : List Pattern}, xs.map nameCanon = ys.map nameCanon →
    List.Forall₂ NameLaws xs ys
  | [], [], _ => .nil
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | x :: xs, y :: ys, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      exact .cons ((nameLaws_iff x y).mpr same.1) (forall₂_of_map_eq same.2)

theorem map_eq_of_forall₂ : ∀ {xs ys : List Pattern}, List.Forall₂ NameLaws xs ys →
    xs.map nameCanon = ys.map nameCanon
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
      simp only [List.map_cons, nameCanon_eq_of_nameLaws head, map_eq_of_forall₂ tail]

/-- **Outside the quotes an application is related argument by argument.** -/
theorem nameLaws_apply_iff {c d : String} (other : ¬ IsQuote c) {xs ys : List Pattern} :
    NameLaws (.apply c xs) (.apply d ys) ↔ c = d ∧ List.Forall₂ NameLaws xs ys := by
  constructor
  · intro h
    have heads := nameLaws_heads h
    subst heads
    have same := nameCanon_eq_of_nameLaws h
    rw [nameCanon_apply_of_not_quote other, nameCanon_apply_of_not_quote other] at same
    exact ⟨rfl, forall₂_of_map_eq (Pattern.apply.inj same).2⟩
  · rintro ⟨rfl, args⟩
    exact nameLaws_apply c args

/-- The canonical form of a collection is a collection of the same kind and rest. -/
theorem eq_collection_of_nameCanon {q : Pattern} {ct : CollType} {elems : List Pattern} {rest : Option String}
    (h : nameCanon q = .collection ct elems rest) :
    ∃ elems' : List Pattern, q = .collection ct elems' rest ∧ elems'.map nameCanon = elems := by
  cases q with
  | bvar n => simp [nameCanon] at h
  | fvar x => simp [nameCanon] at h
  | apply c args =>
      obtain ⟨args', same⟩ := nameCanon_apply_head c args
      rw [same] at h
      cases h
  | lambda nm body => simp [nameCanon] at h
  | multiLambda n nms body => simp [nameCanon] at h
  | subst body repl => simp [nameCanon] at h
  | collection ct' elems' rest' =>
      rw [nameCanon_collection] at h
      obtain ⟨rfl, rfl, rfl⟩ := Pattern.collection.inj h
      exact ⟨elems', rfl, rfl⟩

/-- **A binary parallel bag is related only to a binary parallel bag**, member by member: the spine is
compared as written. -/
theorem nameLaws_pair_left {a b q : Pattern} (h : NameLaws (pPar [a, b]) q) :
    ∃ c d : Pattern, q = pPar [c, d] ∧ NameLaws a c ∧ NameLaws b d := by
  have same := (nameCanon_eq_of_nameLaws h).symm
  rw [pPar, nameCanon_collection] at same
  obtain ⟨elems', rfl, mapped⟩ := eq_collection_of_nameCanon same
  rcases elems' with _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
  · simp at mapped
  · simp at mapped
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
    exact ⟨c, d, rfl, (nameLaws_iff a c).mpr mapped.1.symm, (nameLaws_iff b d).mpr mapped.2.symm⟩
  · simp at mapped

theorem nameLaws_pair_iff {a b c d : Pattern} : NameLaws (pPar [a, b]) (pPar [c, d]) ↔ NameLaws a c ∧ NameLaws b d := by
  constructor
  · intro h
    obtain ⟨c', d', same, ac, bd⟩ := nameLaws_pair_left h
    simp only [pPar, Pattern.collection.injEq, List.cons.injEq, and_true, true_and] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨ac, bd⟩
  · rintro ⟨ac, bd⟩
    exact nameLaws_collection _ _ (.cons ac (.cons bd .nil))

/-- Constructor quotation retains exactly the deep bag equivalence of its
body. It has no rho-style name eta equation that erases a process origin. -/
theorem nameLaws_nQuote_iff {first second : Pattern} :
    NameLaws (nQuote first) (nQuote second) ↔ BagLaws first second := by
  refine ⟨fun same => ?_, nameLaws_nQuote⟩
  have keys := (nameLaws_iff (nQuote first) (nQuote second)).mp same
  change nameCanon (.apply "MQuote" [first]) = nameCanon (.apply "MQuote" [second]) at keys
  rw [nameCanon_quote (Or.inl rfl), nameCanon_quote (Or.inl rfl)] at keys
  exact (ReflQuotient.bagLaws_iff first second).mpr
    (List.singleton_inj.mp (Pattern.apply.inj keys).2)

/-! ## Positive and negative examples -/

/-- **Names are compared modulo the bag laws**: `@(a | b)` and `@(b | a)`. -/
theorem names_modulo_bag_laws : NameLaws (nQuote (par atomA atomB)) (nQuote (par atomB atomA)) := by
  exact nameLaws_nQuote_iff.mpr (ReflQuotient.bagLaws_par_comm atomA atomB)

/-- The term form of a process too: `@(a | b)` and `@(b | a)` as patterns. -/
theorem terms_modulo_bag_laws : NameLaws (tProc (par atomA atomB)) (tProc (par atomB atomA)) := by
  decide +kernel

/-- **The spine is compared as written**: `a | b` and `b | a` are not related. -/
theorem spine_as_written : ¬ NameLaws (par atomA atomB) (par atomB atomA) := by
  decide +kernel

/-- The process of a reflection steps; it is not quoted, so it is compared as written. -/
theorem reflected_process_as_written :
    ¬ NameLaws (pReflect demoChan (par atomA atomB)) (pReflect demoChan (par atomB atomA)) := by
  decide +kernel

/-- The frame modulo the bag laws at every position relates the spine. -/
theorem spine_related_at_bag_frame : BagLaws (par atomA atomB) (par atomB atomA) :=
  ReflQuotient.bagLaws_par_comm _ _

/-- Inside an input's pattern, names are compared modulo the bag laws. -/
theorem names_inside_pattern :
    NameLaws (pFor (nQuote (par atomA atomB)) demoChan pZero) (pFor (nQuote (par atomB atomA)) demoChan pZero) :=
  nameLaws_apply "MFor" (.cons names_modulo_bag_laws (.cons (NameLaws.refl _) (.cons (NameLaws.refl _) .nil)))

/-- Multiplicity is kept, under a quote as everywhere. -/
theorem names_keep_multiplicity : ¬ NameLaws (nQuote (par atomA atomA)) (nQuote atomA) := by
  exact fun same => ReflQuotient.not_bagLaws_twice (nameLaws_nQuote_iff.mp same)

#print axioms nameLaws_psubst
#print axioms nameLaws_nameCanon
#print axioms nameLaws_iff
#print axioms bagLaws_of_nameLaws
#print axioms nameAction
#print axioms solves_iff
#print axioms nameLaws_heads
#print axioms nameLaws_apply_iff
#print axioms nameLaws_pair_left
#print axioms nameLaws_pair_iff
#print axioms nameLaws_nQuote_iff
#print axioms names_modulo_bag_laws
#print axioms terms_modulo_bag_laws
#print axioms spine_as_written
#print axioms reflected_process_as_written
#print axioms spine_related_at_bag_frame
#print axioms names_inside_pattern
#print axioms names_keep_multiplicity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames
