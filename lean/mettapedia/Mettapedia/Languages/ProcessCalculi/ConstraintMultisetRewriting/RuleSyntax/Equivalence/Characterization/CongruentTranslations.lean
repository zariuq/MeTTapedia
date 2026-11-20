import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls

/-!
# A rule and a renamed copy of it: one program for the congruence, two rules for a count of words

For every frame action, extension and barb family.

* `Rule.along`: a rule with its unknowns renamed along a morphism of frames.
* `variant_fires`: every admitted firing of the renamed copy, with opening `ι`, is an admitted firing
  of the rule itself with opening `ι ∘ ρ`, at the same state, with the same result.
* `variant_congruent`: so `{r, r.along ρ} ∪ Q` and `{r} ∪ Q` are congruent at every state, beside every
  program `Q`, when `ρ` has a left inverse on the terms of `r`.
* `added_variant_congruent`: adding a renamed copy of one of its rules to a program changes nothing
  for the congruence.

At the one-frame first-order instance (`renamed`, `renamed_cong`, `renamed_ne`): for a permutation of
the unknowns that moves an unknown of the rule, the copy is another rule, and the two programs are
congruent beside every program at every state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.CongruentTranslations

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc uB

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A rule with its unknowns renamed along a morphism.** -/
def Rule.along (X : Frames Tm Hom) (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') : Rule Tm :=
  ⟨L', r.body.map (X.act ρ), r.collect.map (X.act ρ)⟩

theorem check_map_map {T U V : Type*} (f : T → U) (g : U → V) (c : Check T) :
    (c.map f).map g = c.map (fun t => g (f t)) := by
  cases c <;> rfl

theorem instance_map_map {T U V : Type*} (f : T → U) (g : U → V) (B : RuleInstance T) :
    (B.map f).map g = B.map (fun t => g (f t)) := by
  obtain ⟨take, read, tell, checks, produce⟩ := B
  simp only [RuleInstance.map, List.map_map, RuleInstance.mk.injEq]
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  apply List.map_congr_left
  intro c _
  exact check_map_map f g c

theorem checkTerms_map {T U : Type*} (f : T → U) (c : Check T) :
    checkTerms (c.map f) = (checkTerms c).map f := by
  cases c <;> rfl

variable (X : Frames Tm Hom)

/-- The terms of the renamed copy are the renamed terms. -/
theorem terms_along (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') :
    (Rule.along X r ρ).terms = r.terms.map (X.act ρ) := by
  obtain ⟨locals, ⟨take, read, tell, checks, produce⟩, collect⟩ := r
  simp only [Rule.terms, Rule.along, RuleInstance.map, List.map_append, List.map_map,
    List.map_flatMap, List.flatMap_map]
  congr 1
  congr 1
  congr 1
  apply List.flatMap_congr
  intro c _
  exact checkTerms_map (X.act ρ) c

variable {X} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

/-- **A firing of the renamed copy is a firing of the rule**: the same extension, selection and collect query
sets, the opening composed with the renaming; admitted at the same states, with the same result. -/
theorem variant_fires (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') (back : Hom L' r.locals)
    (inverse : ∀ t ∈ r.terms, X.act back (X.act ρ t) = t) {P P' : Program Tm}
    (memberP : Rule.along X r ρ ∈ P) (member : r ∈ P') {s : State Tm O} (ext : E.Ext s.frame)
    (ι : Hom L' (E.target ext)) (selection : Selection O) (seen : List (Finset O)) :
    let f' : Firing O E P s.frame := ⟨Rule.along X r ρ, memberP, ext, ι, selection, seen⟩
    let g : Firing O E P' s.frame := ⟨r, member, ext, X.comp ι ρ, selection, seen⟩
    f'.Admits X s → g.Admits X s ∧ g.result X s = f'.result X s := by
  intro f' g admitted
  have fn : X.act (X.comp ι ρ) = fun t => X.act ι (X.act ρ t) := funext (X.act_comp ι ρ)
  have hop : g.opened X = f'.opened X := by
    show r.body.map (X.act (X.comp ι ρ)) = (r.body.map (X.act ρ)).map (X.act ι)
    rw [instance_map_map, fn]
  have hcen : g.collectOpened X = f'.collectOpened X := by
    show r.collect.map (X.act (X.comp ι ρ)) = (r.collect.map (X.act ρ)).map (X.act ι)
    rw [List.map_map, fn]
    rfl
  have hinfo : g.information X s = f'.information X s := by
    unfold Firing.information Firing.matching
    rw [hop]
    rfl
  have hholds : ∀ (b : Obj) (σ : Hom (E.target ext) b), g.Holds X s σ ↔ f'.Holds X s σ := by
    intro b σ
    unfold Firing.Holds
    rw [hop, hcen]
    exact Iff.rfl
  have hresult : g.result X s = f'.result X s := by
    unfold Firing.result
    rw [hinfo, hop]
    rfl
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLength, readLength, produceLength, collectLength⟩,
    enabled, solvable, asks⟩ := admitted
  refine ⟨⟨⟨?_, takenNodup, madeNodup, ?_, ?_, ?_, ?_⟩, enabled, ?_, ?_⟩, hresult⟩
  · intro b g₀ h
    obtain ⟨u, state, rule⟩ := fresh b g₀ (X.comp h back)
    refine ⟨u, state, fun t inside => ?_⟩
    have renamed : X.act ρ t ∈ (Rule.along X r ρ).terms := by
      rw [terms_along]
      exact List.mem_map_of_mem inside
    have key := rule (X.act ρ t) renamed
    show X.E (X.act u (X.act (X.comp ι ρ) t)) (X.act h t)
    rw [X.act_comp ι ρ t]
    have value : X.act (X.comp h back) (X.act ρ t) = X.act h t := by
      rw [X.act_comp, inverse t inside]
    rw [← value]
    exact key
  · have same : (Rule.along X r ρ).body.take.length = r.body.take.length := List.length_map _
    exact same.symm.trans takeLength
  · have same : (Rule.along X r ρ).body.read.length = r.body.read.length := List.length_map _
    exact same.symm.trans readLength
  · have same : (Rule.along X r ρ).body.produce.length = r.body.produce.length := List.length_map _
    exact same.symm.trans produceLength
  · have same : (Rule.along X r ρ).collect.length = r.collect.length := List.length_map _
    exact same.symm.trans collectLength
  · rw [hinfo]
    exact solvable
  · intro b σ solved
    rw [hinfo] at solved
    exact (hholds b σ).mpr (asks b σ solved)

omit [DecidableEq O] in
theorem mem_terms_general {r : Rule Tm} {t : Tm r.locals}
    (inside : t ∈ r.body.take ∨ t ∈ r.body.read ∨ t ∈ r.body.tell.map Prod.fst ∨
      t ∈ r.body.tell.map Prod.snd ∨ t ∈ r.body.checks.flatMap checkTerms ∨ t ∈ r.body.produce ∨
      t ∈ r.collect) : t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

omit [DecidableEq O] in
/-- Two functions that agree on the terms of a rule map its body and its collect query alike. -/
theorem map_congr_general (r : Rule Tm) {U : Type*} {f g : Tm r.locals → U}
    (agree : ∀ t ∈ r.terms, f t = g t) :
    r.body.map f = r.body.map g ∧ r.collect.map f = r.collect.map g := by
  have collect : r.collect.map f = r.collect.map g :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms_general (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside)))))))
  refine ⟨?_, collect⟩
  have take : r.body.take.map f = r.body.take.map g :=
    List.map_congr_left fun t inside => agree t (mem_terms_general (Or.inl inside))
  have read : r.body.read.map f = r.body.read.map g :=
    List.map_congr_left fun t inside => agree t (mem_terms_general (Or.inr (Or.inl inside)))
  have tell : (r.body.tell.map fun pair => (f pair.1, f pair.2)) =
      r.body.tell.map fun pair => (g pair.1, g pair.2) := by
    refine List.map_congr_left fun e inside => ?_
    rw [agree e.1 (mem_terms_general (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))))),
      agree e.2 (mem_terms_general (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_map.mpr ⟨e, inside, rfl⟩))))))]
  have checks : r.body.checks.map (Check.map f) = r.body.checks.map (Check.map g) := by
    refine List.map_congr_left fun check inside => ?_
    have term : ∀ u ∈ checkTerms check, f u = g u := fun u member =>
      agree u (mem_terms_general (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨check, inside, member⟩)))))))
    cases check with
    | equal left right =>
        show Check.equal (f left) (f right) = Check.equal (g left) (g right)
        rw [term left (by simp [checkTerms]), term right (by simp [checkTerms])]
    | predicate quantifier pattern =>
        show Check.predicate quantifier (f pattern) = Check.predicate quantifier (g pattern)
        rw [term pattern (by simp [checkTerms])]
    | count pattern number =>
        show Check.count (f pattern) number = Check.count (g pattern) number
        rw [term pattern (by simp [checkTerms])]
  have produce : r.body.produce.map f = r.body.produce.map g :=
    List.map_congr_left fun t inside =>
      agree t (mem_terms_general (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside)))))))
  show (⟨_, _, _, _, _⟩ : RuleInstance U) = ⟨_, _, _, _, _⟩
  rw [take, read, tell, checks, produce]

/-- **A firing of the rule is a firing of its renamed copy**: the opening composed with the inverse of
the renaming; admitted at the same states, with the same result. -/
theorem variant_fires_back (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') (back : Hom L' r.locals)
    (inverse : ∀ t ∈ r.terms, X.act back (X.act ρ t) = t) {P P' : Program Tm}
    (memberP : r ∈ P) (member : Rule.along X r ρ ∈ P') {s : State Tm O} (ext : E.Ext s.frame)
    (ι : Hom r.locals (E.target ext)) (selection : Selection O) (seen : List (Finset O)) :
    let f : Firing O E P s.frame := ⟨r, memberP, ext, ι, selection, seen⟩
    let g : Firing O E P' s.frame := ⟨Rule.along X r ρ, member, ext, X.comp ι back, selection, seen⟩
    f.Admits X s → g.Admits X s ∧ g.result X s = f.result X s := by
  intro f g admitted
  have agree : ∀ t ∈ r.terms, X.act (X.comp ι back) (X.act ρ t) = X.act ι t := fun t inside => by
    rw [X.act_comp, inverse t inside]
  obtain ⟨bodyEq, collectEq⟩ := map_congr_general r
    (f := fun t => X.act (X.comp ι back) (X.act ρ t)) (g := X.act ι) agree
  have hop : g.opened X = f.opened X := by
    show (r.body.map (X.act ρ)).map (X.act (X.comp ι back)) = r.body.map (X.act ι)
    rw [instance_map_map]
    exact bodyEq
  have hcen : g.collectOpened X = f.collectOpened X := by
    show (r.collect.map (X.act ρ)).map (X.act (X.comp ι back)) = r.collect.map (X.act ι)
    rw [List.map_map]
    exact collectEq
  have hinfo : g.information X s = f.information X s := by
    unfold Firing.information Firing.matching
    rw [hop]
    rfl
  have hholds : ∀ (b : Obj) (σ : Hom (E.target ext) b), g.Holds X s σ ↔ f.Holds X s σ := by
    intro b σ
    unfold Firing.Holds
    rw [hop, hcen]
    exact Iff.rfl
  have hresult : g.result X s = f.result X s := by
    unfold Firing.result
    rw [hinfo, hop]
    rfl
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLength, readLength, produceLength, collectLength⟩,
    enabled, solvable, asks⟩ := admitted
  refine ⟨⟨⟨?_, takenNodup, madeNodup, ?_, ?_, ?_, ?_⟩, enabled, ?_, ?_⟩, hresult⟩
  · intro b g₀ h
    obtain ⟨u, state, rule⟩ := fresh b g₀ (X.comp h ρ)
    refine ⟨u, state, fun t' inside => ?_⟩
    rw [terms_along] at inside
    obtain ⟨t, member', rfl⟩ := List.mem_map.mp inside
    have key := rule t member'
    show X.E (X.act u (X.act (X.comp ι back) (X.act ρ t))) (X.act h (X.act ρ t))
    rw [agree t member', ← X.act_comp h ρ t]
    exact key
  · have same : (Rule.along X r ρ).body.take.length = r.body.take.length := List.length_map _
    exact same.trans takeLength
  · have same : (Rule.along X r ρ).body.read.length = r.body.read.length := List.length_map _
    exact same.trans readLength
  · have same : (Rule.along X r ρ).body.produce.length = r.body.produce.length := List.length_map _
    exact same.trans produceLength
  · have same : (Rule.along X r ρ).collect.length = r.collect.length := List.length_map _
    exact same.trans collectLength
  · rw [hinfo]
    exact solvable
  · intro b σ solved
    rw [hinfo] at solved
    exact (hholds b σ).mpr (asks b σ solved)

variable {B : Type uB} {obs : B → State Tm O → Prop}

/-- The rule and its renamed copy, as a program, are answered by the rule alone. -/
theorem variant_answers (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') (back : Hom L' r.locals)
    (inverse : ∀ t ∈ r.terms, X.act back (X.act ρ t) = t) :
    AnswersUpTo X O E obs {r, Rule.along X r ρ} {r} ∧ AnswersUpTo X O E obs {r} {r, Rule.along X r ρ} := by
  constructor
  · rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    by_cases isRule : rule = r
    · subst isRule
      exact ⟨⟨rule, Set.mem_singleton _, ext, ι, selection, seen⟩, admitted, Congruent.refl _⟩
    · have isCopy : rule = Rule.along X r ρ := by
        rcases member with same | same
        · exact absurd same isRule
        · exact same
      subst isCopy
      obtain ⟨admittedG, results⟩ := variant_fires r ρ back inverse member (Set.mem_singleton r)
        (P' := ({r} : Program Tm)) ext ι selection seen admitted
      have same : ∀ st st' : State Tm O, st' = st →
          Congruent X O E obs ⟨{r, Rule.along X r ρ}, st⟩ ⟨{r, Rule.along X r ρ}, st'⟩ := by
        intro st st' equal
        subst equal
        exact Congruent.refl _
      exact ⟨⟨r, Set.mem_singleton r, ext, X.comp ι ρ, selection, seen⟩, admittedG, same _ _ results⟩
  · intro s f admitted
    exact ⟨reprogram f (Or.inl f.member), admitted, Congruent.refl _⟩

/-- **A rule and a renamed copy of it are one program for the congruence**, beside every program, at
every state, for every barb family. -/
theorem variant_congruent (r : Rule Tm) {L' : Obj} (ρ : Hom r.locals L') (back : Hom L' r.locals)
    (inverse : ∀ t ∈ r.terms, X.act back (X.act ρ t) = t) (Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨{r, Rule.along X r ρ} ∪ Q, s⟩ ⟨{r} ∪ Q, s⟩ :=
  congruent_of_answersUpTo (variant_answers r ρ back inverse).1 (variant_answers r ρ back inverse).2 Q s

/-- **Adding a renamed copy of one of its rules to a program changes nothing for the congruence.** -/
theorem added_variant_congruent {Prog : Program Tm} {r : Rule Tm} (member : r ∈ Prog) {L' : Obj}
    (ρ : Hom r.locals L') (back : Hom L' r.locals)
    (inverse : ∀ t ∈ r.terms, X.act back (X.act ρ t) = t) (s : State Tm O) :
    Congruent X O E obs ⟨Prog ∪ {Rule.along X r ρ}, s⟩ ⟨Prog, s⟩ := by
  have both := variant_congruent (obs := obs) (E := E) r ρ back inverse Prog s
  have left : ({r, Rule.along X r ρ} : Program Tm) ∪ Prog = Prog ∪ {Rule.along X r ρ} := by
    ext q
    constructor
    · rintro ((isRule | isCopy) | inside)
      · exact Or.inl (isRule ▸ member)
      · exact Or.inr isCopy
      · exact Or.inl inside
    · rintro (inside | isCopy)
      · exact Or.inr inside
      · exact Or.inl (Or.inr isCopy)
  have right : ({r} : Program Tm) ∪ Prog = Prog := by
    ext q
    constructor
    · rintro (isRule | inside)
      · exact (isRule : q = r) ▸ member
      · exact inside
    · intro inside
      exact Or.inr inside
  rw [left, right] at both
  exact both

end General

/-! ## One frame, first-order atoms -/

section OneFrame

open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong)

/-- A permutation of the unknowns, as a substitution. -/
def permute (π : Equiv.Perm ℕ) : Subst atoms := fun v => .var (π v)

theorem permute_inverse (π : Equiv.Perm ℕ) (t : Term atoms) :
    Subst.applyTerm (permute π.symm) (Subst.applyTerm (permute π) t) = t := by
  cases t with
  | var v => exact congrArg Term.var (π.symm_apply_apply v)
  | const _ => rfl
  | app fn _ => exact nomatch fn

/-- **A rule with its unknowns permuted.** -/
def renamed (π : Equiv.Perm ℕ) (r : Rule Tm) : Rule Tm :=
  Rule.along X r (L' := PUnit.unit) (permute π)

/-- **A rule and its copy under a permutation of the unknowns are one program for the congruence**,
beside every program, at every state. -/
theorem renamed_cong (π : Equiv.Perm ℕ) (r : Rule Tm) (Q : Program Tm) (s : State Tm ℕ) :
    Cong ⟨{r, renamed π r} ∪ Q, s⟩ ⟨{r} ∪ Q, s⟩ :=
  variant_congruent (X := X) r (L' := PUnit.unit) (permute π) (permute π.symm)
    (fun t _ => permute_inverse π t) Q s

/-- The copy of "take `x`, make `x`" under the exchange of the unknowns `0` and `1` is another rule:
it takes the unknown `1`. -/
theorem renamed_touch_ne : renamed (Equiv.swap 0 1) touch ≠ touch := by
  intro same
  unfold renamed Rule.along touch at same
  injection same with _ body _
  injection body with take _ _ _ _
  have head : (Term.var ((Equiv.swap 0 1 : Equiv.Perm ℕ) 0) : Term atoms) = x :=
    List.head_eq_of_cons_eq take
  have unknown : (Equiv.swap 0 1 : Equiv.Perm ℕ) 0 = 0 := Term.var.inj head
  rw [Equiv.swap_apply_left] at unknown
  exact absurd unknown (by decide)

/-- **Two rules or one**: "take `x`, make `x`" with and without its copy at the unknown `1` are
congruent beside every program at every state, and the first program has two rules. -/
theorem touch_and_copy (Q : Program Tm) (s : State Tm ℕ) :
    renamed (Equiv.swap 0 1) touch ≠ touch ∧
      Cong ⟨{touch, renamed (Equiv.swap 0 1) touch} ∪ Q, s⟩ ⟨{touch} ∪ Q, s⟩ :=
  ⟨renamed_touch_ne, renamed_cong _ touch Q s⟩

end OneFrame

/-! ## The frames of the hosting: a copy of a rule gives every history through it a second word -/

section Hosted

set_option backward.isDefEq.respectTransparency false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Hosting (HostState translate retRule unmatchedRule choiceLeftRule choiceRightRule bindStartRule
  bindValueRule schema unk Unknown unknownArity controlFrame Nodes altN evalN retN bindN)
open Hosting.Alternatives (CRule CProgram FiresAt Chain HeadTag)

variable {S : Signature}

/-- **A firing by a rule and a firing by its renamed copy** join the same states, take the same row
and make the same row. -/
theorem firesAt_copy_iff {Prog : CProgram S} {r : CRule S} {L' : Interface.Frames.Frame S}
    (ρ : Assignment r.locals.arity L'.arity) (back : Assignment L'.arity r.locals.arity)
    (inverse : ∀ t ∈ r.terms, (Interface.Frames.contextual S).act back
      ((Interface.Frames.contextual S).act ρ t) = t)
    (member : r ∈ Prog) (memberCopy : Rule.along (Interface.Frames.contextual S) r ρ ∈ Prog)
    (s s' : HostState S) (o o' : ℕ) :
    FiresAt Prog r s o s' o' ↔
      FiresAt Prog (Rule.along (Interface.Frames.contextual S) r ρ) s o s' o' := by
  constructor
  · rintro ⟨⟨rule, mem, ext, ι, selection, seen⟩, isRule, admitted, taken, made, result⟩
    have same : r = rule := isRule.symm
    subst same
    obtain ⟨admittedG, resultG⟩ := variant_fires_back (X := Interface.Frames.contextual S)
      (E := Contextual.declarations S) (O := ℕ) r ρ back inverse mem memberCopy ext ι
      selection seen admitted
    exact ⟨⟨_, memberCopy, ext, (Interface.Frames.contextual S).comp ι back, selection, seen⟩, rfl,
      admittedG, taken, made, resultG.trans result⟩
  · rintro ⟨⟨rule, mem, ext, ι, selection, seen⟩, isCopy, admitted, taken, made, result⟩
    have same : rule = Rule.along (Interface.Frames.contextual S) r ρ := isCopy
    subst same
    obtain ⟨admittedG, resultG⟩ := variant_fires (X := Interface.Frames.contextual S)
      (E := Contextual.declarations S) (O := ℕ) r ρ back inverse mem member ext ι selection seen
      admitted
    exact ⟨⟨r, member, ext, (Interface.Frames.contextual S).comp ι ρ, selection, seen⟩, rfl,
      admittedG, taken, made, resultG.trans result⟩

open Classical in
/-- A word with every occurrence of one rule replaced by another. -/
noncomputable def twin (r copy : CRule S) (word : List (CRule S)) : List (CRule S) :=
  word.map fun q => if q = r then copy else q

/-- **Every history has a twin through the copy**: the same states, the word with the rule replaced
by its copy. -/
theorem chain_twin {Prog : CProgram S} {r : CRule S} {L' : Interface.Frames.Frame S}
    (ρ : Assignment r.locals.arity L'.arity) (back : Assignment L'.arity r.locals.arity)
    (inverse : ∀ t ∈ r.terms, (Interface.Frames.contextual S).act back
      ((Interface.Frames.contextual S).act ρ t) = t)
    (member : r ∈ Prog) (memberCopy : Rule.along (Interface.Frames.contextual S) r ρ ∈ Prog)
    {s s' : HostState S} {o o' : ℕ} {word : List (CRule S)}
    (chain : Chain (FiresAt Prog) s o word s' o') :
    Chain (FiresAt Prog) s o (twin r (Rule.along (Interface.Frames.contextual S) r ρ) word) s' o' := by
  classical
  unfold twin
  refine Chain.map _ (fun l s₁ o₁ s₂ o₂ fired => ?_) chain
  by_cases isRule : l = r
  · show FiresAt Prog (if l = r then Rule.along (Interface.Frames.contextual S) r ρ else l) s₁ o₁ s₂ o₂
    rw [if_pos isRule]
    rw [isRule] at fired
    exact (firesAt_copy_iff ρ back inverse member memberCopy s₁ s₂ o₁ o₂).mp fired
  · show FiresAt Prog (if l = r then Rule.along (Interface.Frames.contextual S) r ρ else l) s₁ o₁ s₂ o₂
    rw [if_neg isRule]
    exact fired

/-- A firing of a program is a firing of every larger program. -/
theorem firesAt_mono {Prog Prog' : CProgram S} (sub : Prog ⊆ Prog') {r : CRule S} {s s' : HostState S}
    {o o' : ℕ} (fired : FiresAt Prog r s o s' o') : FiresAt Prog' r s o s' o' := by
  obtain ⟨f, isRule, admitted, taken, made, result⟩ := fired
  exact ⟨reprogram f (sub f.member), isRule, admitted, taken, made, result⟩

theorem chain_mono {Prog Prog' : CProgram S} (sub : Prog ⊆ Prog') {s s' : HostState S} {o o' : ℕ}
    {word : List (CRule S)} (chain : Chain (FiresAt Prog) s o word s' o') :
    Chain (FiresAt Prog') s o word s' o' := by
  have mapped := Chain.map (fun q : CRule S => q)
    (fun l s₁ o₁ s₂ o₂ (fired : FiresAt Prog l s₁ o₁ s₂ o₂) => firesAt_mono sub fired) chain
  rw [List.map_id'] at mapped
  exact mapped

/-- **No firing of the program at the state.** -/
def Stuck (Prog : CProgram S) (s : HostState S) : Prop :=
  ∀ f : Firing ℕ (Contextual.declarations S) Prog s.frame, ¬ f.Admits (Interface.Frames.contextual S) s

/-- A state with no firing has none after a copy of a rule joins the program. -/
theorem stuck_with_copy {Prog : CProgram S} {r : CRule S} {L' : Interface.Frames.Frame S}
    (ρ : Assignment r.locals.arity L'.arity) (back : Assignment L'.arity r.locals.arity)
    (inverse : ∀ t ∈ r.terms, (Interface.Frames.contextual S).act back
      ((Interface.Frames.contextual S).act ρ t) = t)
    (member : r ∈ Prog) {s : HostState S} (stuck : Stuck Prog s) :
    Stuck (Prog ∪ {Rule.along (Interface.Frames.contextual S) r ρ}) s := by
  rintro ⟨rule, mem, ext, ι, selection, seen⟩ admitted
  by_cases inProg : rule ∈ Prog
  · exact stuck ⟨rule, inProg, ext, ι, selection, seen⟩ admitted
  · have isCopy : rule = Rule.along (Interface.Frames.contextual S) r ρ := by
      rcases mem with old | new
      · exact absurd old inProg
      · exact new
    subst isCopy
    obtain ⟨admittedG, -⟩ := variant_fires (X := Interface.Frames.contextual S)
      (E := Contextual.declarations S) (O := ℕ) r ρ back inverse mem member ext ι selection seen admitted
    exact stuck ⟨r, member, ext, (Interface.Frames.contextual S).comp ι ρ, selection, seen⟩ admittedG

variable {Γ : Ctx S} {star : S.Srt}

/-- Exchange the unknowns `datum` and `pattern` of a control rule. -/
def exchange : Unknown → Unknown
  | .datum => .pattern
  | .pattern => .datum
  | .first => .first
  | .second => .second
  | .stack => .stack

/-- The exchange, as an assignment of the frame of the control rules. -/
def exchangeAssignment : Assignment (unknownArity (S := S) Γ star) (unknownArity (S := S) Γ star) :=
  fun u => generator (unknownArity Γ star) (exchange u)

theorem exchange_twice :
    Assignment.compose (exchangeAssignment (S := S) (Γ := Γ) (star := star)) exchangeAssignment =
      generator (unknownArity Γ star) := by
  funext u
  cases u <;> exact instantiate_generator exchangeAssignment _

/-- The exchange is its own inverse on every term. -/
theorem exchange_inverse (t : Observation S (unknownArity Γ star)) :
    (Interface.Frames.contextual S).act (a := controlFrame Γ star) (b := controlFrame Γ star)
      exchangeAssignment ((Interface.Frames.contextual S).act (a := controlFrame Γ star)
        (b := controlFrame Γ star) exchangeAssignment t) = t := by
  show instantiateObservation exchangeAssignment (instantiateObservation exchangeAssignment t) = t
  rw [instantiateObservation_comp, exchange_twice]
  exact instantiateObservation_identity t

variable (N : Nodes S Γ star)

/-- **The rule `ret` with its unknown `datum` written as `pattern`.** -/
def copyRet : CRule S :=
  Rule.along (Interface.Frames.contextual S) (retRule N) (L' := controlFrame Γ star) exchangeAssignment

/-- **The copy is another rule.** -/
theorem copyRet_ne : copyRet N ≠ retRule N := by
  intro same
  unfold copyRet Rule.along retRule at same
  injection same with _ body _
  injection body with take _ _ _ _
  have head : instantiateObservation exchangeAssignment
      (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))) =
        observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)) := List.head_eq_of_cons_eq take
  rw [instantiateObservation_observe, Hosting.instantiate_altN N, Hosting.instantiate_evalN N,
    Hosting.instantiate_retN N] at head
  have outer := Hosting.vec2_inj (N.args_eq (observe_injective head))
  have inner := Hosting.vec1_inj (N.args_eq outer.1)
  have innermost := Hosting.vec1_inj (N.args_eq inner)
  have moved : instantiate exchangeAssignment (unk (S := S) (Γ := Γ) (star := star) .datum) =
      unk .pattern := instantiate_generator exchangeAssignment Unknown.datum
  rw [moved] at innermost
  exact absurd (Hosting.Alternatives.unk_injective innermost) (by decide)

/-- The copy takes an alternative that returns, as `ret` does. -/
theorem copyRet_headTag : HeadTag N (copyRet N) .ret := by
  intro pat member B h
  have isCopy : pat = instantiateObservation exchangeAssignment
      (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))) := List.mem_singleton.mp member
  rw [isCopy, instantiateObservation_comp]
  exact Hosting.Alternatives.retRule_headTag N _ (List.mem_singleton_self _) B
    (Assignment.compose h exchangeAssignment)

theorem bindStartRule_headTag : HeadTag N (bindStartRule N) .bind := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (unk .pattern), instantiate h (unk .first), instantiate h (unk .second)],
    instantiate h (unk .stack), ?_⟩
  change observe (instantiate h _) = _
  rw [Hosting.instantiate_altN, Hosting.instantiate_evalN, Hosting.instantiate_bindN]

/-- **The copy is a rule of no translated program.** -/
theorem copyRet_not_translated {κ : SourceLanguage.Keys S} {Ty : Type}
    (P : SourceLanguage.Program κ Γ star Ty) : copyRet N ∉ translate N P := by
  have take : (copyRet N).body.take ≠ [] := List.cons_ne_nil _ _
  intro member
  rcases (Hosting.mem_translate N).mp member with control | ⟨e, -, isSchema⟩
  · rcases (Hosting.mem_controlRules N).mp control with h | h | h | h | h | h
    · exact copyRet_ne N h
    · exact Hosting.Alternatives.checks_ne (by show (0 : ℕ) ≠ 1; omega) h
    · exact Hosting.Alternatives.ne_of_headTag N take (copyRet_headTag N)
        (Hosting.Alternatives.choiceLeftRule_headTag N) (by decide) h
    · exact Hosting.Alternatives.ne_of_headTag N take (copyRet_headTag N)
        (Hosting.Alternatives.choiceRightRule_headTag N) (by decide) h
    · exact Hosting.Alternatives.ne_of_headTag N take (copyRet_headTag N) (bindStartRule_headTag N)
        (by decide) h
    · have lengths : (copyRet N).body.tell.length = (bindValueRule N).body.tell.length := by rw [h]
      exact absurd lengths (by show (0 : ℕ) ≠ 1; omega)
  · exact Hosting.Alternatives.ne_of_headTag N take (copyRet_headTag N)
      (Hosting.Alternatives.schema_headTag N e) (by decide) isSchema

/-- **Adding the copy to a translated program changes nothing for the congruence**, at every state,
for every barb family. -/
theorem copyRet_congruent {κ : SourceLanguage.Keys S} {Ty : Type}
    (P : SourceLanguage.Program κ Γ star Ty) {B : Type uB} (obs : B → HostState S → Prop)
    (s : HostState S) :
    Congruent (Interface.Frames.contextual S) ℕ (Contextual.declarations S) obs
      ⟨translate N P ∪ {copyRet N}, s⟩ ⟨translate N P, s⟩ := by
  have member : retRule N ∈ translate N P :=
    (Hosting.mem_translate N).mpr (Or.inl ((Hosting.mem_controlRules N).mpr (Or.inl rfl)))
  unfold copyRet
  exact added_variant_congruent (X := Interface.Frames.contextual S) (E := Contextual.declarations S)
    (obs := obs) (Prog := translate N P) (r := retRule N) member (L' := controlFrame Γ star)
    exchangeAssignment exchangeAssignment (fun t _ => exchange_inverse t) s

/-- **A complete history of a translated program that ends with `ret` has a second word after the
copy joins**: the same states, the last rule replaced by the copy; the end state has no firing. -/
theorem copyRet_second_word {κ : SourceLanguage.Keys S} {Ty : Type}
    (P : SourceLanguage.Program κ Γ star Ty) {s₀ s : HostState S} {a₀ a : ℕ} {word : List (CRule S)}
    (chain : Chain (FiresAt (translate N P)) s₀ a₀ word s a) (stuck : Stuck (translate N P) s) :
    Chain (FiresAt (translate N P ∪ {copyRet N})) s₀ a₀ word s a ∧
      Chain (FiresAt (translate N P ∪ {copyRet N})) s₀ a₀ (twin (retRule N) (copyRet N) word) s a ∧
      Stuck (translate N P ∪ {copyRet N}) s := by
  have member : retRule N ∈ translate N P :=
    (Hosting.mem_translate N).mpr (Or.inl ((Hosting.mem_controlRules N).mpr (Or.inl rfl)))
  have lifted : Chain (FiresAt (translate N P ∪ {copyRet N})) s₀ a₀ word s a :=
    chain_mono Set.subset_union_left chain
  exact ⟨lifted,
    chain_twin (r := retRule N) (L' := controlFrame Γ star) exchangeAssignment exchangeAssignment
      (fun t _ => exchange_inverse t) (Or.inl member) (Or.inr rfl) lifted,
    stuck_with_copy (r := retRule N) (L' := controlFrame Γ star) exchangeAssignment
      exchangeAssignment (fun t _ => exchange_inverse t) member stuck⟩

end Hosted

/-! ## The instance: a translated program of the tree, with one history and two words -/

section Concrete

set_option backward.isDefEq.respectTransparency false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Hosting (HostState translate retRule schema)
open Hosting.Alternatives (CRule CProgram FiresAt Chain)
open Hosting.Alternatives.Controls (N dupP q3 eqAt)

/-- The translated program of the tree's control `dupP`. -/
abbrev hosted : CProgram SourceLanguage.Elaboration.MSig := translate N dupP

/-- The same program with the copy of `ret`. -/
abbrev hostedWithCopy : CProgram SourceLanguage.Elaboration.MSig := hosted ∪ {copyRet N}

theorem twin_word :
    twin (retRule N) (copyRet N) [schema N (eqAt [1]), retRule N] = [schema N (eqAt [1]), copyRet N] := by
  classical
  have other : schema N (eqAt [1]) ≠ retRule N := fun same =>
    Hosting.Alternatives.ne_of_headTag N (List.cons_ne_nil _ _) (Hosting.Alternatives.retRule_headTag N)
      (Hosting.Alternatives.schema_headTag N (eqAt [1])) (by decide) same.symm
  unfold twin
  show [if schema N (eqAt [1]) = retRule N then copyRet N else schema N (eqAt [1]),
    if retRule N = retRule N then copyRet N else retRule N] = _
  rw [if_neg other, if_pos rfl]

/-- **Congruent programs, one history, two words.** The translated program and the same program with
a renamed copy of `ret` are congruent at every state, for every barb family. From the start of the
query, the second program has a complete history with the word "schema, `ret`" and, between the same
states, one with the word "schema, copy of `ret`"; the two words differ. -/
theorem congruent_programs_two_words :
    (∀ (B : Type) (obs : B → HostState SourceLanguage.Elaboration.MSig → Prop)
        (s : HostState SourceLanguage.Elaboration.MSig),
        Congruent (Interface.Frames.contextual SourceLanguage.Elaboration.MSig) ℕ
          (Contextual.declarations SourceLanguage.Elaboration.MSig) obs ⟨hostedWithCopy, s⟩ ⟨hosted, s⟩) ∧
      ∃ (s : HostState SourceLanguage.Elaboration.MSig) (a : ℕ),
        Chain (FiresAt hostedWithCopy) (Hosting.start N dupP q3) 2 [schema N (eqAt [1]), retRule N] s a ∧
          Chain (FiresAt hostedWithCopy) (Hosting.start N dupP q3) 2
            [schema N (eqAt [1]), copyRet N] s a ∧
          Stuck hostedWithCopy s ∧
          ([schema N (eqAt [1]), retRule N] : List (CRule SourceLanguage.Elaboration.MSig)) ≠
            [schema N (eqAt [1]), copyRet N] ∧
          ¬ ∃ (s' : HostState SourceLanguage.Elaboration.MSig) (a' : ℕ),
            Chain (FiresAt hosted) (Hosting.start N dupP q3) 2 [schema N (eqAt [1]), copyRet N] s' a' := by
  refine ⟨fun B obs s => copyRet_congruent N dupP obs s, ?_⟩
  obtain ⟨s, a, reached, terminal⟩ := Hosting.Alternatives.Controls.dup_complete 0 [1] rfl
  have chain : Chain (FiresAt hosted) (Hosting.start N dupP q3) 2 [schema N (eqAt [1]), retRule N] s a :=
    Hosting.Alternatives.chain_forget N reached
  have stuck : Stuck hosted s := fun f admitted => terminal _ ⟨f, admitted, rfl⟩
  obtain ⟨first, second, stuckBoth⟩ := copyRet_second_word N dupP chain stuck
  rw [twin_word] at second
  refine ⟨s, a, first, second, stuckBoth, fun same => ?_, ?_⟩
  · injection same with _ tail
    injection tail with head _
    exact copyRet_ne N head.symm
  · rintro ⟨s', a', other⟩
    exact copyRet_not_translated N dupP
      (Hosting.Alternatives.chain_rules_mem other (copyRet N)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end Concrete

/-! ## Two programs of the source: one equation, and the same equation at two sites -/

section TwoSites

set_option backward.isDefEq.respectTransparency false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Hosting (HostState translate schema schemaArity schemaFrame schemaStack asUnknowns altN evalN applyN
  retN)
open Hosting.Alternatives (CRule CProgram)
open SourceLanguage (copyAt)
open SourceLanguage.Elaboration (MSig mkeys MTy noNames csym)
open SourceLanguage.Toolkit (fo foD closeNames live_nil answers_cons_finished answers_singleton
  answer_of_determines)
open Hosting.Alternatives.Controls (N D supply one W0 f q3)

/-- The equation `(= x one)` at a site, its variable named at that site. -/
def oneAt (site : List ℕ) : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨site, foD [] site 0, .ret one⟩

/-- The program with the equation once. -/
def onceV : SourceLanguage.Program mkeys [] () MTy := ⟨[oneAt [1]], fun t => .apply t⟩

/-- The program with the equation at two sites. -/
def twiceV : SourceLanguage.Program mkeys [] () MTy := ⟨[oneAt [1], oneAt [2]], fun t => .apply t⟩

/-! ### The translations are congruent -/

/-- Exchange the sites `[1]` and `[2]`. -/
def swapSite (site : List ℕ) : List ℕ := if site = [1] then [2] else if site = [2] then [1] else site

theorem swapSite_twice (site : List ℕ) : swapSite (swapSite site) = site := by
  by_cases first : site = [1]
  · rw [first]
    decide
  · by_cases second : site = [2]
    · rw [second]
      decide
    · unfold swapSite
      rw [if_neg first, if_neg second, if_neg first, if_neg second]

/-- A name with its site exchanged; its arity is kept. -/
def swapName (x : SourceLanguage.Name mkeys) : SourceLanguage.Name mkeys :=
  ⟨x.scopes, ⟨swapSite x.key.site, x.key.index, x.key.arity⟩⟩

theorem swapName_twice (x : SourceLanguage.Name mkeys) : swapName (swapName x) = x := by
  obtain ⟨scopes, ⟨site, index, arity⟩⟩ := x
  show (⟨scopes, ⟨swapSite (swapSite site), index, arity⟩⟩ : SourceLanguage.Name mkeys) = _
  rw [swapSite_twice]

theorem swapName_first : swapName (fo [] [1] 0) = fo [] [2] 0 := by
  show (⟨[], ⟨swapSite [1], 0, ([], ())⟩⟩ : SourceLanguage.Name mkeys) = _
  rw [show swapSite [1] = [2] from by decide]

/-- The exchange of the two sites, as an assignment of the frame of a schema. -/
def siteSwap : Assignment (schemaArity [] () mkeys) (schemaArity [] () mkeys)
  | .inl x => generator (schemaArity [] () mkeys) (.inl (swapName x))
  | .inr () => generator (schemaArity [] () mkeys) (.inr ())

theorem siteSwap_twice : Assignment.compose siteSwap siteSwap = generator (schemaArity [] () mkeys) := by
  funext n
  cases n with
  | inl x =>
      have moved : instantiate siteSwap (siteSwap (.inl x)) = siteSwap (.inl (swapName x)) :=
        instantiate_generator siteSwap _
      show instantiate siteSwap (siteSwap (.inl x)) = generator (schemaArity [] () mkeys) (.inl x)
      rw [moved]
      have key : HEq (generator (schemaArity [] () mkeys) (Sum.inl (swapName (swapName x))))
          (generator (schemaArity [] () mkeys) (Sum.inl x)) := by rw [swapName_twice]
      exact eq_of_heq key
  | inr u =>
      cases u
      exact instantiate_generator siteSwap _

theorem siteSwap_inverse (t : Observation MSig (schemaArity [] () mkeys)) :
    (Interface.Frames.contextual MSig).act (a := schemaFrame [] () mkeys) (b := schemaFrame [] () mkeys)
      siteSwap ((Interface.Frames.contextual MSig).act (a := schemaFrame [] () mkeys)
        (b := schemaFrame [] () mkeys) siteSwap t) = t := by
  show instantiateObservation siteSwap (instantiateObservation siteSwap t) = t
  rw [instantiateObservation_comp, siteSwap_twice]
  exact instantiateObservation_identity t

/-- **The schema at the second site is the schema at the first, renamed.** -/
theorem along_schema :
    Rule.along (Interface.Frames.contextual MSig) (schema N (oneAt [1])) (L' := schemaFrame [] () mkeys)
      siteSwap = schema N (oneAt [2]) := by
  have unknown : instantiate siteSwap (instantiate (asUnknowns (Γ := []) (star := ())) (foD [] [1] 0)) =
      instantiate asUnknowns (foD [] [2] 0) := by
    rw [SourceLanguage.Toolkit.instantiate_foD, SourceLanguage.Toolkit.instantiate_foD]
    have moved : instantiate siteSwap (asUnknowns (Γ := []) (star := ()) (fo [] [1] 0)) =
        siteSwap (.inl (fo [] [1] 0)) := instantiate_generator siteSwap _
    rw [moved]
    have key : HEq (generator (schemaArity [] () mkeys) (Sum.inl (swapName (fo [] [1] 0))))
        (generator (schemaArity [] () mkeys) (Sum.inl (fo [] [2] 0))) := by rw [swapName_first]
    exact eq_of_heq key
  have stack : instantiate siteSwap (schemaStack (S := MSig) (Γ := []) (star := ()) (κ := mkeys)) =
      schemaStack := instantiate_generator siteSwap (Sum.inr ())
  have take : instantiateObservation siteSwap
      (observe (altN N (evalN N (applyN N (instantiate asUnknowns (foD [] [1] 0)))) schemaStack)) =
        observe (altN N (evalN N (applyN N (instantiate asUnknowns (foD [] [2] 0)))) schemaStack) := by
    rw [instantiateObservation_observe, Hosting.instantiate_altN N, Hosting.instantiate_evalN N,
      Hosting.instantiate_applyN N, unknown, stack]
  have closed : instantiate siteSwap (instantiate (asUnknowns (Γ := []) (star := ())) one) =
      instantiate asUnknowns one := rfl
  have produce : instantiateObservation siteSwap
      (observe (altN N (evalN N (retN N (instantiate asUnknowns one))) schemaStack)) =
        observe (altN N (evalN N (retN N (instantiate asUnknowns one))) schemaStack) := by
    rw [instantiateObservation_observe, Hosting.instantiate_altN N, Hosting.instantiate_evalN N,
      Hosting.instantiate_retN N, closed, stack]
  show (⟨schemaFrame [] () mkeys,
      ⟨[instantiateObservation siteSwap
          (observe (altN N (evalN N (applyN N (instantiate asUnknowns (foD [] [1] 0)))) schemaStack))],
        [], [], [],
        [instantiateObservation siteSwap
          (observe (altN N (evalN N (retN N (instantiate asUnknowns one))) schemaStack))]⟩, []⟩ :
        CRule MSig) =
    ⟨schemaFrame [] () mkeys,
      ⟨[observe (altN N (evalN N (applyN N (instantiate asUnknowns (foD [] [2] 0)))) schemaStack)],
        [], [], [],
        [observe (altN N (evalN N (retN N (instantiate asUnknowns one))) schemaStack)]⟩, []⟩
  rw [take, produce]

theorem twiceV_translate : translate N twiceV = translate N onceV ∪ {schema N (oneAt [2])} := by
  ext r
  constructor
  · rintro (control | ⟨e, member, rfl⟩)
    · exact Or.inl (Or.inl control)
    · rcases List.mem_cons.mp member with rfl | rest
      · exact Or.inl (Or.inr ⟨_, List.mem_singleton_self _, rfl⟩)
      · rw [List.mem_singleton.mp rest]
        exact Or.inr rfl
  · rintro ((control | ⟨e, member, rfl⟩) | isCopy)
    · exact Or.inl control
    · rw [List.mem_singleton.mp member]
      exact Or.inr ⟨oneAt [1], List.mem_cons_self, rfl⟩
    · have same : r = schema N (oneAt [2]) := isCopy
      rw [same]
      exact Or.inr ⟨oneAt [2], List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩

/-- **The translations of the two programs are congruent**, at every state, for every barb family. -/
theorem two_sites_congruent {B : Type uB} (obs : B → HostState MSig → Prop) (s : HostState MSig) :
    Congruent (Interface.Frames.contextual MSig) ℕ (Contextual.declarations MSig) obs
      ⟨translate N twiceV, s⟩ ⟨translate N onceV, s⟩ := by
  have member : schema N (oneAt [1]) ∈ translate N onceV :=
    Or.inr ⟨oneAt [1], List.mem_singleton_self _, rfl⟩
  rw [twiceV_translate, ← along_schema]
  exact added_variant_congruent (X := Interface.Frames.contextual MSig)
    (E := Contextual.declarations MSig) (obs := obs) (Prog := translate N onceV)
    (r := schema N (oneAt [1])) member (L' := schemaFrame [] () mkeys) siteSwap siteSwap
    (fun t _ => siteSwap_inverse t) s

/-! ### Both programs are within the hypotheses of the bag theorem -/

/-- The equation at the two sites has two schemas. -/
theorem oneAt_schema_ne : schema N (oneAt [1]) ≠ schema N (oneAt [2]) := by
  intro same
  unfold schema oneAt at same
  injection same with _ body _
  injection body with take _ _ _ _
  injection take with made
  have outer := Hosting.vec2_inj (N.args_eq (observe_injective made))
  have inner := Hosting.vec1_inj (N.args_eq outer.1)
  have applied : instantiate (asUnknowns (Γ := []) (star := ())) (foD [] [1] 0) =
      instantiate asUnknowns (foD [] [2] 0) := Hosting.vec1_inj (N.args_eq inner)
  rw [SourceLanguage.Toolkit.instantiate_foD, SourceLanguage.Toolkit.instantiate_foD] at applied
  unfold asUnknowns generator at applied
  injection applied with _ _ operator _
  injection operator with made'
  injection made' with name
  have unknown : (Sum.inl (fo [] [1] 0) : SourceLanguage.Name mkeys ⊕ Unit) = Sum.inl (fo [] [2] 0) := name
  have key : fo [] [1] 0 = fo [] [2] 0 := Sum.inl.inj unknown
  have site : ([1] : List ℕ) = [2] := congrArg (fun x : SourceLanguage.Name mkeys => x.key.site) key
  exact absurd site (by decide)

/-- **Both programs are in the fragment and have pairwise distinct schemas.** -/
theorem both_within :
    Hosting.PlainProgram onceV ∧ (onceV.equations.map (schema N)).Nodup ∧
      Hosting.PlainProgram twiceV ∧ (twiceV.equations.map (schema N)).Nodup := by
  refine ⟨fun e member => ?_, List.nodup_singleton _, fun e member => ?_,
    List.nodup_cons.mpr ⟨fun inside => oneAt_schema_ne (List.mem_singleton.mp inside),
      List.nodup_singleton _⟩⟩
  · rw [List.mem_singleton.mp member]
    trivial
  · rcases List.mem_cons.mp member with rfl | rest
    · trivial
    · rw [List.mem_singleton.mp rest]
      trivial

/-! ### The bags of the source differ -/

/-- The store after the copy of the equation at a site matched the call `f`. -/
def storeAt (site : List ℕ) : List (SourceLanguage.Constraint mkeys [] ()) :=
  [] ++ [(instantiate (copyAt mkeys 0) (foD [] site 0), f)]

theorem storeAt_first_live : SourceLanguage.Solvable (storeAt [1]) :=
  ⟨Empty, noNames, closeNames [(([0], [1], 0), csym "f")] (csym "a"), by decide⟩

theorem storeAt_second_live : SourceLanguage.Solvable (storeAt [2]) :=
  ⟨Empty, noNames, closeNames [(([0], [2], 0), csym "f")] (csym "a"), by decide⟩

/-- The alternative a copy of the equation at a site makes. -/
abbrev calledAt (site : List ℕ) : SourceLanguage.Branch mkeys [] () MTy :=
  SourceLanguage.callBranch D W0.scope [] f [] [] (oneAt site)

/-- The finished alternative after it returns. -/
abbrev doneAt (site : List ℕ) : SourceLanguage.Branch mkeys [] () MTy :=
  ⟨storeAt site, .value (instantiate (copyAt mkeys 0) one), [], []⟩

theorem doneAt_finished (site : List ℕ) : SourceLanguage.Branch.Finished (D := D) (doneAt site) :=
  ⟨rfl, _, rfl⟩

theorem doneAt_answer {site : List ℕ} (live : SourceLanguage.Solvable (storeAt site)) :
    (doneAt site).answer (D := D) = {csym "one"} :=
  answer_of_determines rfl ⟨live, fun _ _ _ => rfl⟩

theorem onceV_source :
    ∃ C : SourceLanguage.Config mkeys [] () MTy,
      SourceLanguage.Runs D onceV supply (SourceLanguage.Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) onceV supply ∧ C.answers (D := D) = {{csym "one"}} := by
  refine ⟨⟨W0.fresh, {doneAt [1]}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D onceV supply (SourceLanguage.Config.initial (fun _ => 0) q3)
        ⟨W0.fresh, {calledAt [1]}⟩ :=
      SourceLanguage.Step.single live_nil
        (.apply W0 [] f [] [] ⟨oneAt [1], List.mem_singleton_self _, storeAt_first_live⟩)
    have s2 : SourceLanguage.Step D onceV supply ⟨W0.fresh, {calledAt [1]}⟩ ⟨W0.fresh, {doneAt [1]}⟩ :=
      SourceLanguage.Step.of_eq (rest := 0) rfl rfl storeAt_first_live
        (.ret W0.fresh (storeAt [1]) _ [] [])
    exact (Relation.ReflTransGen.single s1).tail s2
  · refine SourceLanguage.Config.quiescent_of_finished fun b member _ => ?_
    rw [Multiset.mem_singleton.mp member]
    exact doneAt_finished [1]
  · show SourceLanguage.Config.answers (D := D) ⟨W0.fresh, {doneAt [1]}⟩ = _
    rw [answers_singleton (doneAt_finished [1]) storeAt_first_live, doneAt_answer storeAt_first_live]

theorem twiceV_source :
    ∃ C : SourceLanguage.Config mkeys [] () MTy,
      SourceLanguage.Runs D twiceV supply (SourceLanguage.Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) twiceV supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  refine ⟨⟨W0.fresh, {doneAt [2], doneAt [1]}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D twiceV supply (SourceLanguage.Config.initial (fun _ => 0) q3)
        ⟨W0.fresh, {calledAt [1], calledAt [2]}⟩ :=
      SourceLanguage.Step.single live_nil
        (.apply W0 [] f [] [] ⟨oneAt [1], List.mem_cons_self, storeAt_first_live⟩)
    have s2 : SourceLanguage.Step D twiceV supply ⟨W0.fresh, {calledAt [1], calledAt [2]}⟩
        ⟨W0.fresh, {doneAt [1], calledAt [2]}⟩ :=
      SourceLanguage.Step.of_eq (rest := {calledAt [2]}) rfl rfl storeAt_first_live
        (.ret W0.fresh (storeAt [1]) _ [] [])
    have s3 : SourceLanguage.Step D twiceV supply ⟨W0.fresh, {doneAt [1], calledAt [2]}⟩
        ⟨W0.fresh, {doneAt [2], doneAt [1]}⟩ :=
      SourceLanguage.Step.of_eq (rest := {doneAt [1]}) (Multiset.cons_swap _ _ _) rfl
        storeAt_second_live (.ret W0.fresh (storeAt [2]) _ [] [])
    exact ((Relation.ReflTransGen.single s1).tail s2).tail s3
  · refine SourceLanguage.Config.quiescent_of_finished fun b member _ => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact doneAt_finished [2]
    · exact doneAt_finished [1]
  · show SourceLanguage.Config.answers (D := D) ⟨W0.fresh, doneAt [2] ::ₘ {doneAt [1]}⟩ = _
    rw [answers_cons_finished (doneAt_finished [2]) storeAt_second_live,
      answers_singleton (doneAt_finished [1]) storeAt_first_live, doneAt_answer storeAt_second_live,
      doneAt_answer storeAt_first_live]
    rfl

/-- **Congruent translations, different bags.** Two programs of the source, both in the first
fragment and with pairwise distinct schemas (the hypotheses of `bag_of_rule_classes`): the equation
`(= x one)` once, and at two sites. Their translations are congruent at every state for every barb
family; on the query `(f)` the first answers `{one}` and the second `{one, one}`. -/
theorem congruent_translations_two_bags :
    (Hosting.PlainProgram onceV ∧ (onceV.equations.map (schema N)).Nodup ∧
      Hosting.PlainProgram twiceV ∧ (twiceV.equations.map (schema N)).Nodup) ∧
    (∀ (B : Type) (obs : B → HostState MSig → Prop) (s : HostState MSig),
      Congruent (Interface.Frames.contextual MSig) ℕ (Contextual.declarations MSig) obs
        ⟨translate N twiceV, s⟩ ⟨translate N onceV, s⟩) ∧
    (∃ C : SourceLanguage.Config mkeys [] () MTy,
      SourceLanguage.Runs D onceV supply (SourceLanguage.Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) onceV supply ∧ C.answers (D := D) = {{csym "one"}}) ∧
    (∃ C : SourceLanguage.Config mkeys [] () MTy,
      SourceLanguage.Runs D twiceV supply (SourceLanguage.Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) twiceV supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}}) :=
  ⟨both_within, fun _ obs s => two_sites_congruent obs s, onceV_source, twiceV_source⟩

/-! ### At one and the same state: congruent systems, one class less -/

open Hosting.Alternatives (Chain FiresAt NamedMove RuleName)

/-- The schema at the second site is a rule of the first program's translation only if it is the
schema at the first site, which it is not. -/
theorem second_schema_not_translated : schema N (oneAt [2]) ∉ translate N onceV := by
  have take : (schema N (oneAt [2])).body.take ≠ [] := List.cons_ne_nil _ _
  have headed := Hosting.Alternatives.schema_headTag N (oneAt [2])
  intro member
  rcases (Hosting.mem_translate N).mp member with control | ⟨e, inside, isSchema⟩
  · rcases (Hosting.mem_controlRules N).mp control with h | h | h | h | h | h
    · exact Hosting.Alternatives.ne_of_headTag N take headed (Hosting.Alternatives.retRule_headTag N)
        (by decide) h
    · exact Hosting.Alternatives.checks_ne (by show (0 : ℕ) ≠ 1; omega) h
    · exact Hosting.Alternatives.ne_of_headTag N take headed
        (Hosting.Alternatives.choiceLeftRule_headTag N) (by decide) h
    · exact Hosting.Alternatives.ne_of_headTag N take headed
        (Hosting.Alternatives.choiceRightRule_headTag N) (by decide) h
    · exact Hosting.Alternatives.ne_of_headTag N take headed (bindStartRule_headTag N) (by decide) h
    · have lengths : (schema N (oneAt [2])).body.tell.length =
          (Hosting.bindValueRule N).body.tell.length := by rw [h]
      exact absurd lengths (by show (0 : ℕ) ≠ 1; omega)
  · rw [List.mem_singleton.mp inside] at isSchema
    exact oneAt_schema_ne isSchema.symm

/-- **The history of the second program through the equation at the second site**: a complete
history from the start of the query, with the word "schema of the second site, `ret`", ending in a
finished state that shows `one`. -/
theorem second_site_history :
    ∃ (s : HostState MSig) (a : ℕ),
      Chain (FiresAt (translate N twiceV)) (Hosting.start N twiceV q3) 2
          [schema N (oneAt [2]), Hosting.retRule N] s a ∧
        Stuck (translate N twiceV) s ∧ Hosting.StateFinished N s a ∧
        Hosting.stateAnswer N s a = {csym "one"} := by
  have plainP : Hosting.PlainProgram twiceV := both_within.2.2.1
  have rep : Hosting.Represents N twiceV 0 (Hosting.initialBranch q3) (Hosting.start N twiceV q3) 2 :=
    Hosting.start_represents N twiceV q3 (by
      intro t member x inside
      simp only [q3, SourceLanguage.Comp.data, List.mem_singleton] at member
      subst member
      simp [f, SourceLanguage.Elaboration.sym, support, supportArgs] at inside)
  have plain : Hosting.PlainBranch (Hosting.initialBranch (Ty := MTy) q3) :=
    ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have move : NamedMove (D := D) twiceV W0 (Hosting.initialBranch q3) (.eqn 1) W0.fresh
      (calledAt [2]) :=
    NamedMove.eqn (D := D) (P := twiceV) (w := W0) [] f [] [] 1 (oneAt [2]) rfl
      ⟨oneAt [1], List.mem_cons_self, storeAt_first_live⟩
  obtain ⟨s₁, fired₁, rep₁, _⟩ := Hosting.Alternatives.simulation_named N plainP move rep plain
    storeAt_second_live (k := 3) (by rw [rep.present]; simp [twiceV])
  have retMove : NamedMove (D := D) twiceV W0.fresh (calledAt [2]) .ret W0.fresh (doneAt [2]) :=
    NamedMove.ret (D := D) (P := twiceV) (w := W0.fresh) (storeAt [2])
      (instantiate (copyAt mkeys 0) one) [] []
  have fresh : (4 : ℕ) ∉ s₁.present := by
    rw [rep₁.present]
    simp [twiceV]
  obtain ⟨s₂, fired₂, rep₂, _⟩ := Hosting.Alternatives.simulation_named N plainP retMove rep₁
    (⟨rfl, .inl ⟨_, rfl, trivial⟩⟩ : Hosting.PlainBranch (calledAt [2])) storeAt_second_live (k := 4) fresh
  have named : Chain (Hosting.Alternatives.FiresNamed N twiceV) (Hosting.start N twiceV q3) 2
      [.eqn 1, .ret] s₂ 4 := Chain.snoc (Chain.single fired₁) fired₂
  have donePlain : Hosting.PlainBranch (doneAt [2]) := ⟨rfl, .inr ⟨_, rfl⟩⟩
  refine ⟨s₂, 4, Hosting.Alternatives.chain_forget N named, fun g admitted => ?_,
    (Hosting.finished_iff N rep₂).mp ⟨doneAt_finished [2], storeAt_second_live⟩, ?_⟩
  · exact Hosting.finished_still N (D := D) (supply := supply) (w := W0.fresh) plainP rep₂ donePlain
      (doneAt_finished [2]) ⟨g, admitted, rfl⟩
  · rw [Hosting.answer_eq N rep₂ (doneAt_finished [2])]
    exact doneAt_answer storeAt_second_live

/-- **At one and the same state: congruent systems, and one of them has a class the other has not.**
From the start state of the second program, the system with the second program's translation and
the system with the first program's translation are congruent for every barb family. Every complete
history of the second system is a complete history of the first with the same word and the same
states. The first has one more: through the schema of the second site, ending finished and showing
`one`; the second system has no history with that word. -/
theorem congruent_systems_one_class_less :
    (∀ (B : Type) (obs : B → HostState MSig → Prop),
      Congruent (Interface.Frames.contextual MSig) ℕ (Contextual.declarations MSig) obs
        ⟨translate N twiceV, Hosting.start N twiceV q3⟩ ⟨translate N onceV, Hosting.start N twiceV q3⟩) ∧
    (∀ (word : List (CRule MSig)) (s : HostState MSig) (a : ℕ),
      Chain (FiresAt (translate N onceV)) (Hosting.start N twiceV q3) 2 word s a →
        Stuck (translate N onceV) s →
          Chain (FiresAt (translate N twiceV)) (Hosting.start N twiceV q3) 2 word s a ∧
            Stuck (translate N twiceV) s) ∧
    ∃ (s : HostState MSig) (a : ℕ),
      Chain (FiresAt (translate N twiceV)) (Hosting.start N twiceV q3) 2
          [schema N (oneAt [2]), Hosting.retRule N] s a ∧
        Stuck (translate N twiceV) s ∧ Hosting.StateFinished N s a ∧
        Hosting.stateAnswer N s a = {csym "one"} ∧
        ¬ ∃ (s' : HostState MSig) (a' : ℕ),
          Chain (FiresAt (translate N onceV)) (Hosting.start N twiceV q3) 2
            [schema N (oneAt [2]), Hosting.retRule N] s' a' := by
  have member : schema N (oneAt [1]) ∈ translate N onceV :=
    Or.inr ⟨oneAt [1], List.mem_singleton_self _, rfl⟩
  have sub : translate N onceV ⊆ translate N twiceV := by
    rw [twiceV_translate]
    exact Set.subset_union_left
  refine ⟨fun _ obs => two_sites_congruent obs _, fun word s a chain stuck => ⟨chain_mono sub chain, ?_⟩, ?_⟩
  · rw [twiceV_translate, ← along_schema]
    exact stuck_with_copy (r := schema N (oneAt [1])) (L' := schemaFrame [] () mkeys) siteSwap siteSwap
      (fun t _ => siteSwap_inverse t) member stuck
  · obtain ⟨s, a, chain, stuck, finished, answer⟩ := second_site_history
    refine ⟨s, a, chain, stuck, finished, answer, ?_⟩
    rintro ⟨s', a', other⟩
    exact second_schema_not_translated
      (Hosting.Alternatives.chain_rules_mem other (schema N (oneAt [2])) List.mem_cons_self)

end TwoSites

#print axioms along_schema
#print axioms two_sites_congruent
#print axioms both_within
#print axioms onceV_source
#print axioms twiceV_source
#print axioms congruent_translations_two_bags
#print axioms second_schema_not_translated
#print axioms second_site_history
#print axioms congruent_systems_one_class_less
#print axioms copyRet_not_translated
#print axioms twin_word
#print axioms congruent_programs_two_words
#print axioms firesAt_copy_iff
#print axioms chain_twin
#print axioms stuck_with_copy
#print axioms exchange_inverse
#print axioms copyRet_ne
#print axioms copyRet_congruent
#print axioms copyRet_second_word
#print axioms terms_along
#print axioms map_congr_general
#print axioms variant_fires_back
#print axioms variant_fires
#print axioms variant_answers
#print axioms variant_congruent
#print axioms added_variant_congruent
#print axioms renamed_cong
#print axioms renamed_touch_ne
#print axioms touch_and_copy

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.CongruentTranslations
