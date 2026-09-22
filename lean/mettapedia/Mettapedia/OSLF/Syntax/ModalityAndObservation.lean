import Mettapedia.OSLF.Syntax.GSLTBridge
import Mettapedia.OSLF.Syntax.UniqueDecompositionRepaired

/-!
# The generated modalities inside the observational logic

Two modal layers now sit over the same presentation, and leaving them unrelated
would be its own defect.  The generated logic's possibility is a root-level
statement indexed by a rule; the observational logic's diamond is a statement
about the presentation's transition system, which closes the rule under contexts
and under the equations.  This module relates them, and finds a strict
refinement rather than a coincidence.

That is the expected answer.  If the two agreed there would be no work for the
contextual closure to do, and the source's chapter on labelled transitions would
add nothing to its chapter on the generator.  What the refinement says is that
inhabiting a generated modality is a *stronger* claim than satisfying the
corresponding diamond: it names the rule, and it names the redex, whereas the
diamond only asserts that the state can move.

The second half of the module separates the layers in the other direction.  The
structural type formers generated at the term formers are predicates on *terms*;
the observations of the transition system are predicates on *classes*.  These
cannot be the same thing as soon as the equations identify terms with different
heads, and that is proved rather than remarked.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.GSLT

set_option autoImplicit false

variable {S : Signature}

namespace Presentation

/-- A root step at rule `i` is a transition at label `i`. -/
theorem act_of_rootStep (Pr : Presentation S) {s : S.Srt}
    (i : Fin Pr.rules.length) (hs : (Pr.rules.get i).sort = s)
    {t u : Term S [] (Pr.rules.get i).sort}
    (h : RootStep (Pr.rules.get i) t u) :
    (Pr.classSeparatingHMSystem s).act i (hs ▸ t) (hs ▸ u) := by
  subst hs
  exact stepModE_of_step (step_of_rootStep _ h)

/-- **The generated possibility inhabits the diamond.**  A rule's possibility at
the rule's own sort gives the transition at that rule's label. -/
theorem sat_dia_of_poss (Pr : Presentation S)
    (i : Fin Pr.rules.length)
    (formula : HennessyMilner.Formula (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Atom
      (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Label)
    {t : Term S [] (Pr.rules.get i).sort}
    (h : Poss (Pr.rules.get i)
      (fun u => (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat formula u) t) :
    (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat
      (HennessyMilner.Formula.dia i formula) t := by
  obtain ⟨u, hstep, hB⟩ := h
  exact ⟨u, stepModE_of_step (step_of_rootStep _ hstep), hB⟩

/-- **The modality at a chosen position inhabits a diamond somewhere.**  Its
subject lives at the position's carrier rather than at the rule's sort, so what
it delivers is a state that can move, not a modal claim about its own subject --
which is the type-theoretic content of placing the modality at the carrier. -/
theorem exists_sat_dia_of_stepsFromPosition (Pr : Presentation S)
    (i : Fin Pr.rules.length)
    (formula : HennessyMilner.Formula (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Atom
      (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Label)
    {t : Term S [] (Pr.rules.get i).position.carrier}
    (h : StepsFromPosition (Pr.rules.get i)
      (fun u => (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat formula u) t) :
    ∃ a, (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat
      (HennessyMilner.Formula.dia i formula) a := by
  obtain ⟨a, b, hstep, hB⟩ := stepsFromPosition_step h
  exact ⟨a, b, stepModE_of_step (step_of_rootStep _ hstep), hB⟩

/-- And the rely-indexed modality does the same, once a rely environment meeting
its assumptions is supplied. -/
theorem exists_sat_dia_of_relyPossibly (Pr : Presentation S)
    (i : Fin Pr.rules.length)
    {A : RelyTyping (Pr.rules.get i)}
    (formula : HennessyMilner.Formula (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Atom
      (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).Label)
    {t : Term S [] (Pr.rules.get i).position.carrier}
    (h : RelyPossibly (Pr.rules.get i) A
      (fun u => (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat formula u) t)
    (env : RelyEnv (Pr.rules.get i))
    (henv : ∀ (s : S.Srt) (x : Var (Pr.rules.get i).ctx s)
      (hx : (Pr.rules.get i).RelyParameter x), A s x (env s x hx)) :
    ∃ a, (Pr.classSeparatingHMSystem (Pr.rules.get i).sort).sat
      (HennessyMilner.Formula.dia i formula) a := by
  obtain ⟨a, b, hstep, hB⟩ := relyPossibly_step h env henv
  exact ⟨a, b, stepModE_of_step (step_of_rootStep _ hstep), hB⟩

end Presentation

/-! ## The refinement is strict

A presentation over the structural signature with one rule, exhibiting a state
that satisfies a diamond and does not inhabit the corresponding possibility.  The
transition is available in a context; the rule cannot produce it at the root. -/

namespace ParallelFragment

abbrev pmetas : List (MetaArity psig) := []

abbrev pSig : Signature := withMetas psig pmetas

/-- `x | y ~> x`: parallel composition may drop its right parand.  The chosen
position is the left parand. -/
def dropRight : PositionedRewrite pSig where
  ctx := [PSrt.proc, PSrt.proc]
  sort := PSrt.proc
  lhs := Term.op (S := pSig) (Sum.inl POp.par)
    (.cons (Term.var Var.zero) (.cons (Term.var (Var.succ Var.zero)) .nil))
  rhs := Term.var Var.zero
  position :=
    { carrier := PSrt.proc
      ctxt := Term.op (S := pSig) (Sum.inl POp.par)
        (.cons (Term.var Var.zero)
          (.cons (Term.var (Var.succ (Var.succ Var.zero))) .nil))
      redex := Term.var Var.zero
      plugs := rfl
      linear := rfl }

/-- The presentation: the structural equations and that one rule. -/
def dropping : Presentation psig where
  metas := pmetas
  eqs := ac1
  rules := [dropRight]

/-- The instance that fires at the outer composition. -/
def dropInstance (a b : Term psig [] PSrt.proc) : RuleInstance pmetas dropRight where
  body := fun i => i.elim0
  close := sub2 a b

theorem dropRight_rootStep (a b : Term psig [] PSrt.proc) :
    RootStep dropRight (parT a b) a :=
  ⟨dropInstance a b, rfl, rfl⟩

/-- The one-hole context `[] | c`. -/
def rightCtxt (c : Term psig [] PSrt.proc) : Term psig [PSrt.proc] PSrt.proc :=
  Term.op (S := psig) POp.par
    (.cons (Term.var Var.zero) (.cons (weaken c) .nil))

theorem holeCount_rightCtxt (c : Term psig [] PSrt.proc) :
    holeCount (rightCtxt c) = 1 := by
  have h1 : countVar (weakenVar [] (Var.zero : Var [PSrt.proc] PSrt.proc))
      (weaken (t := PSrt.proc) c) = 0 := holeCount_weaken c
  simp only [rightCtxt, holeCount, countVar, countVarArgs, h1]
  rfl

/-- **A contextual step**: the rule fires inside the left parand. -/
theorem contextual_step (a b c : Term psig [] PSrt.proc) :
    Mettapedia.OSLF.Binding.Step dropRight (parT (parT a b) c) (parT a c) := by
  refine ⟨rightCtxt c, parT a b, a, holeCount_rightCtxt c,
    dropRight_rootStep a b, ?_, ?_⟩
  · have h : bind (extend (parT a b)) (weaken (t := PSrt.proc) c) = c :=
      inst_weaken c (parT a b)
    show Term.op (S := psig) POp.par
      (.cons (parT a b)
        (.cons (bind (extend (parT a b)) (weaken (t := PSrt.proc) c)) .nil))
      = parT (parT a b) c
    rw [h]
    rfl
  · have h : bind (extend a) (weaken (t := PSrt.proc) c) = c := inst_weaken c a
    show Term.op (S := psig) POp.par
      (.cons a (.cons (bind (extend a) (weaken (t := PSrt.proc) c)) .nil))
      = parT a c
    rw [h]
    rfl

/-- ... so the composite satisfies the diamond at the rule's label. -/
theorem sat_dia_contextual (a b c : Term psig [] PSrt.proc) :
    (dropping.classSeparatingHMSystem PSrt.proc).sat
      (HennessyMilner.Formula.dia ⟨0, by decide⟩
        (HennessyMilner.Formula.atom (parT a c)))
      (parT (parT a b) c) :=
  ⟨parT a c, stepModE_of_step (contextual_step a b c), EqClosure.refl _⟩

/-- Head test and left projection, since the term type is indexed and its
constructors cannot be compared or destructured directly. -/
def headIsPar : {Γ : Ctx psig} → Term psig Γ PSrt.proc → Bool
  | _, .var _ => false
  | _, .op POp.par _ => true
  | _, .op POp.nul _ => false
  | _, .op (POp.out _) _ => false

def leftParand : {Γ : Ctx psig} → Term psig Γ PSrt.proc → Term psig Γ PSrt.proc
  | _, .var v => .var v
  | _, .op POp.par (.cons a _) => a
  | _, .op POp.nul args => .op POp.nul args
  | _, .op (POp.out n) args => .op (POp.out n) args

/-- **But the rule cannot produce that state at the root.**  A root step of this
rule returns the left parand, and the left parand of the composite is not the
state the diamond names. -/
theorem not_poss_contextual :
    ¬ Poss dropRight
        (fun v => (dropping.classSeparatingHMSystem PSrt.proc).sat
          (HennessyMilner.Formula.atom (parT (u 0) (u 2))) v)
        (parT (parT (u 0) (u 1)) (u 2)) := by
  rintro ⟨v, ⟨I, hl, hr⟩, hB⟩
  have hclose : I.close PSrt.proc Var.zero = parT (u 0) (u 1) := by
    have h0 : Term.op (S := psig) POp.par
        (.cons (I.close PSrt.proc Var.zero)
          (.cons (I.close PSrt.proc (Var.succ Var.zero)) .nil))
        = parT (parT (u 0) (u 1)) (u 2) := hl
    exact congrArg leftParand h0
  have hv : v = parT (u 0) (u 1) := by rw [← hr]; exact hclose
  subst hv
  have hcount := countOut_invariant 1 hB
  simp [parT, u, countOut, countOutArgs, headCount] at hcount

/-- **The generated possibility strictly refines the diamond.**  One state, one
label: the diamond holds and the possibility does not. -/
theorem poss_strictly_refines_dia :
    (dropping.classSeparatingHMSystem PSrt.proc).sat
        (HennessyMilner.Formula.dia ⟨0, by decide⟩
          (HennessyMilner.Formula.atom (parT (u 0) (u 2))))
        (parT (parT (u 0) (u 1)) (u 2))
      ∧ ¬ Poss dropRight
          (fun v => (dropping.classSeparatingHMSystem PSrt.proc).sat
            (HennessyMilner.Formula.atom (parT (u 0) (u 2))) v)
          (parT (parT (u 0) (u 1)) (u 2)) :=
  ⟨sat_dia_contextual (u 0) (u 1) (u 2), not_poss_contextual⟩

/-! ## The structural layer is about terms, not classes

The generator adds one type former per term former, and those formers read the
head of a term.  The observations of a transition system cannot, because the
equations identify terms with different heads.  The general statement comes
first; the signature below supplies the witness that its hypothesis is
satisfiable. -/

/-- One predicate per argument slot, all trivially satisfied: the structural
former with no condition on its arguments. -/
def truePreds (S : Signature) : (as : List (List S.Srt × S.Srt)) → (Γ : Ctx S) →
    PredArgs S as Γ
  | [], _ => .nil
  | _ :: as, Γ => .cons (fun _ => True) (truePreds S as Γ)

theorem satArgs_truePreds : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (args : Args S as Γ), SatArgs (truePreds S as Γ) args
  | [], _, .nil => trivial
  | _ :: _, _, .cons _ tail => ⟨trivial, satArgs_truePreds tail⟩

/-- Being headed by a given operator. -/
def HeadedBy {Γ : Ctx S} {s : S.Srt} (o : S.Op s) (t : Term S Γ s) : Prop :=
  ∃ args : Args S (S.arity o) Γ, t = Term.op o args

/-- **The structural layer reads heads.**  With no condition on the arguments,
the generated type former at an operator is exactly the head test. -/
theorem structural_truePreds_iff_headedBy {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (t : Term S Γ s) :
    structural o (truePreds S (S.arity o) Γ) t ↔ HeadedBy o t := by
  constructor
  · rintro ⟨args, h, -⟩
    exact ⟨args, h⟩
  · rintro ⟨args, h⟩
    exact ⟨args, h, satArgs_truePreds args⟩

/-- **No observation reads a head, as soon as the theory relates heads.**  If an
equation identifies a term headed by `o` with one that is not, then no predicate
invariant under the equations agrees with the head test at `o`.  So the
structural layer of the generator speaks about terms and the observations of a
transition system about classes, and they are not interchangeable -- not on this
signature in particular, but wherever the equational theory is not
head-preserving, which is the usual case. -/
theorem no_invariant_predicate_is_headedBy {M : List (MetaArity S)}
    {E : List (EqAxiom S M)} {Γ : Ctx S} {s : S.Srt} {o : S.Op s}
    {t u : Term S Γ s} (he : EqClosure E t u)
    (ht : HeadedBy o t) (hu : ¬ HeadedBy o u) :
    ¬ ∃ Q : Term S Γ s → Prop,
        (∀ v w, EqClosure E v w → (Q v ↔ Q w)) ∧ (∀ v, Q v ↔ HeadedBy o v) := by
  rintro ⟨Q, hinv, hQ⟩
  exact hu ((hQ u).mp ((hinv t u he).mp ((hQ t).mpr ht)))

/-! The hypothesis is satisfiable precisely when the theory is not
head-preserving; a unit law is the smallest way to fail that, and the structural
signature supplies one. -/
/-- The structural former at `par`, with no condition on the arguments. -/
def isPar : Pred psig [] PSrt.proc :=
  structural POp.par (truePreds psig (psig.arity POp.par) [])

theorem isPar_iff_headedBy (t : Term psig [] PSrt.proc) :
    isPar t ↔ HeadedBy POp.par t := by
  show structural POp.par (truePreds psig (psig.arity POp.par) []) t ↔ _
  exact structural_truePreds_iff_headedBy POp.par t

theorem isPar_parT (a b : Term psig [] PSrt.proc) : isPar (parT a b) :=
  (isPar_iff_headedBy _).mpr ⟨.cons a (.cons b .nil), rfl⟩

theorem not_isPar_u (n : Fin 3) : ¬ isPar (u n) := by
  rintro ⟨args, heq, -⟩
  have h : headIsPar (u n) = headIsPar (Term.op (S := psig) POp.par args) :=
    congrArg headIsPar heq
  simp only [u, headIsPar] at h
  exact absurd h (by decide)

/-- **A structural type former is not an observation.**  The unit law identifies
a composition with its own left parand, and the former separates them. -/
theorem structural_not_equation_invariant :
    EqClosure ac1 (parT (u 0) nulT) (u 0)
      ∧ isPar (parT (u 0) nulT) ∧ ¬ isPar (u 0) :=
  ⟨parUnitR (u 0), isPar_parT (u 0) nulT, not_isPar_u 0⟩

/-- So no atom of the generated transition system can agree with it: every atom
is invariant under the equations, and this predicate is not. -/
theorem no_atom_is_isPar :
    ¬ ∃ a : Term psig [] PSrt.proc,
        ∀ t, (dropping.classSeparatingHMSystem PSrt.proc).observes a t ↔ isPar t := by
  rintro ⟨a, ha⟩
  refine no_invariant_predicate_is_headedBy (E := ac1) (o := POp.par)
    (parUnitR (u 0)) ⟨.cons (u 0) (.cons nulT .nil), rfl⟩
    (fun h => not_isPar_u 0 ((isPar_iff_headedBy _).mpr h))
    ⟨(dropping.classSeparatingHMSystem PSrt.proc).observes a, ?_, ?_⟩
  · intro v w hvw
    exact (dropping.classSeparatingHMSystem PSrt.proc).observes_resp a hvw
  · intro v
    exact (ha v).trans (isPar_iff_headedBy v)

/-! ## Observation policy changes classes, not transitions -/

/-- The same nonempty rule system, without additional atomic observations. -/
def unobservedDropping : HennessyMilner.System (dropping.toGSLT PSrt.proc) :=
  dropping.toHMSystem PSrt.proc PEmpty (fun atom => atom.elim)
    (fun atom => atom.elim)

/-- Every term has a transition under the actual dropping rule: the unit law
exposes `t | 0`, whose root reduction returns `t`. -/
theorem unobservedDropping_self_step (label : unobservedDropping.Label)
    (t : Term psig [] PSrt.proc) : unobservedDropping.act label t t := by
  have bounded : label.val < 1 := label.isLt
  have atZero : label = ⟨0, by decide⟩ := by
    apply Fin.ext
    change label.val = 0
    omega
  subst label
  change Mettapedia.OSLF.Binding.StepModE ac1 dropRight t t
  exact stepModE_resp_left (EqClosure.symm (parUnitR t))
    (stepModE_of_step (step_of_rootStep _ (dropRight_rootStep t nulT)))

/-- With no atoms, this serial one-label system merges all states behaviorally.
The bisimulation uses actual rule transitions, not an empty relation. -/
theorem unobservedDropping_bisimilar (t v : Term psig [] PSrt.proc) :
    unobservedDropping.Bisimilar t v := by
  refine ⟨fun _ _ => True, ⟨?_, ?_, ?_⟩, trivial⟩
  · intro _ right _ label _ _
    exact ⟨right, unobservedDropping_self_step label right, trivial⟩
  · intro left _ _ label _ _
    exact ⟨left, unobservedDropping_self_step label left, trivial⟩
  · intro _ _ _ atom
    exact atom.elim

/-- Distinct equation classes can be bisimilar under coarser observations.
The explicitly class-separating policy on the same transitions distinguishes
them.  Thus that policy is not forced by equation invariance. -/
theorem observation_policy_changes_bisimilarity :
    unobservedDropping.Bisimilar (u 0) (u 1) ∧
      ¬ EqClosure ac1 (u 0) (u 1) ∧
      ¬ (dropping.classSeparatingHMSystem PSrt.proc).Bisimilar (u 0) (u 1) := by
  have different : ¬ EqClosure ac1 (u 0) (u 1) :=
    fun same => countOut_separates (countOut_invariant 1 same).symm
  exact ⟨unobservedDropping_bisimilar _ _, different,
    fun related => different (dropping.equiv_of_bisimilar related)⟩

end ParallelFragment

end Mettapedia.OSLF.Binding
