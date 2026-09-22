import Mettapedia.OSLF.Decidability

/-!
# The source's own generator, as a formula of this language

The scope generator of the source material is

    N = µX. @((φ ∨ *X) | (ψ ∨ *X))

and until now it could not be written here: the fixpoint lived in one formula
language and the cut in another, so the formula had no home.  It has one now.
`OSLFFormula` carries the binder, the cut, the empty collection and a unary
declared former, and the generator below is that display transcribed — a quote
around a parallel composition each of whose parts is an atom or the drop of a
name the generator already has.

**What the frame decides.**  The cut's parts are collections, so in the ambient
frame a part is a *singleton collection* rather than the process inside it.  The
equation frame is where that wrapper goes away, because a presentation declaring
a collection algebra derives the singleton law; the atoms of the specimen below
are therefore stated at singleton collections, and saying so is the content of
the reading being frame-relative rather than a defect to be hidden.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SourceGenerator

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula

/-- **The source's generator**, transcribed.  `quoteLabel` and `dropLabel` are
the presentation's own reflection formers; `leftAtom` and `rightAtom` are the
two part predicates the display calls φ and ψ. -/
def sourceScope (quoteLabel dropLabel leftAtom rightAtom : String) : OSLFFormula :=
  .mu (.headed quoteLabel
    (.cut .hashBag
      (.or (.atom leftAtom) (.headed dropLabel (.var 0)))
      (.or (.atom rightAtom) (.headed dropLabel (.var 0)))))

/-- Rho's spelling of it. -/
abbrev rhoScope (leftAtom rightAtom : String) : OSLFFormula :=
  sourceScope "NQuote" "PDrop" leftAtom rightAtom

/-! ## It is a formula, and the fixed point law applies to it -/

/-- Eleven nodes, and the count does not grow with what the scope contains. -/
theorem sourceScope_size (quoteLabel dropLabel leftAtom rightAtom : String) :
    (sourceScope quoteLabel dropLabel leftAtom rightAtom).size = 11 := rfl

/-- It is closed: the only scope variable is the one its own binder binds. -/
theorem sourceScope_closed (quoteLabel dropLabel leftAtom rightAtom : String) :
    OSLFFormula.closedAt 0 (sourceScope quoteLabel dropLabel leftAtom rightAtom) = true :=
  rfl

/-- And the bound variable occurs positively, which is the hypothesis of the
fixed point law. -/
theorem sourceScope_positive (quoteLabel dropLabel leftAtom rightAtom : String) :
    OSLFFormula.positiveIn 0
      (.headed quoteLabel
        (.cut .hashBag
          (.or (.atom leftAtom) (.headed dropLabel (.var 0)))
          (.or (.atom rightAtom) (.headed dropLabel (.var 0))))) = true := rfl

/-- **So the generator unfolds.**  Its reading is the reading of one unfolding,
which is what makes it a fixed point rather than a lower bound. -/
theorem sourceScope_unfold (R : Pattern → Pattern → Prop) (I : AtomSem)
    (quoteLabel dropLabel leftAtom rightAtom : String) :
    sem R I (sourceScope quoteLabel dropLabel leftAtom rightAtom)
      = sem R I (OSLFFormula.unfold
          (.headed quoteLabel
            (.cut .hashBag
              (.or (.atom leftAtom) (.headed dropLabel (.var 0)))
              (.or (.atom rightAtom) (.headed dropLabel (.var 0)))))) :=
  sem_mu_eq_unfold R I _ (sourceScope_closed quoteLabel dropLabel leftAtom rightAtom)
    (sourceScope_positive quoteLabel dropLabel leftAtom rightAtom)

/-- **And it is outside the modal fragment**, which is exactly why it could not
be written before: the fragment the older theorems range over has neither a
binder nor a structural connective, and this formula needs both. -/
theorem sourceScope_not_modalOnly (quoteLabel dropLabel leftAtom rightAtom : String) :
    OSLFFormula.modalOnly (sourceScope quoteLabel dropLabel leftAtom rightAtom) = false :=
  rfl

theorem sourceScope_not_muFree (quoteLabel dropLabel leftAtom rightAtom : String) :
    OSLFFormula.muFree (sourceScope quoteLabel dropLabel leftAtom rightAtom) = false :=
  rfl

theorem sourceScope_not_spatialFree (quoteLabel dropLabel leftAtom rightAtom : String) :
    OSLFFormula.spatialFree (sourceScope quoteLabel dropLabel leftAtom rightAtom) = false :=
  rfl

/-! ## What the scope contains, and what it does not

The generator is an intersection, so it is below every candidate of the frame
its body does not leave.  Two such candidates settle the shape question in each
frame, and the second of them is what makes the ambient reading *inert*: it
shows the recursive disjunct unreachable there, which is the content behind the
checker's silence in `droppedName_not_positional`. -/

/-- The pointwise form of the fixed point law, which is what a membership proof
uses. -/
theorem sem_sourceScope_iff (R : Pattern → Pattern → Prop) (I : AtomSem)
    (quoteLabel dropLabel leftAtom rightAtom : String) (term : Pattern) :
    sem R I (sourceScope quoteLabel dropLabel leftAtom rightAtom) term ↔
      sem R I (OSLFFormula.unfold
        (.headed quoteLabel
          (.cut .hashBag
            (.or (.atom leftAtom) (.headed dropLabel (.var 0)))
            (.or (.atom rightAtom) (.headed dropLabel (.var 0)))))) term :=
  iff_of_eq
    (congrFun (sourceScope_unfold R I quoteLabel dropLabel leftAtom rightAtom) term)

/-- **Everything the scope contains is a quote.**  "Is a quote" is a candidate
the body does not leave, because the body's outermost former is the quote
itself. -/
theorem sourceScope_is_quote (R : Pattern → Pattern → Prop) (I : AtomSem)
    (quoteLabel dropLabel leftAtom rightAtom : String) {term : Pattern}
    (holds : sem R I (sourceScope quoteLabel dropLabel leftAtom rightAtom) term) :
    ∃ inner, term = .apply quoteLabel [inner] := by
  refine holds (fun t => ∃ inner, t = .apply quoteLabel [inner]) trivial ?_
  rintro t ⟨inner, shape, -⟩
  exact ⟨inner, shape⟩

/-- **A composition is not an application.**  So in the ambient powerset a
declared former matches no part of a cut, since the cut presents every part as a
one-element composition.  This is a fact about the frame rather than about any
checker, and it is the obstruction the equation frame removes. -/
theorem not_semEnv_headed_collection
    (R : Pattern → Pattern → Prop) (I : AtomSem) (env : ScopeEnv)
    (label : String) (body : OSLFFormula) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    ¬ semEnv R fullFrame I env (.headed label body)
        (.collection kind elements rest) := by
  rintro ⟨code, shape, -⟩
  exact Pattern.noConfusion shape

/-! ## The coercion step, in the frame that has the singleton law

The recursive disjunct asks a part to be a drop, and a part is a one-element
composition.  What identifies the two is the singleton law, which a
presentation declaring a collection algebra derives and the ambient powerset
does not have.  Nothing about the formula changes below; what changes is the
frame it is read in, which is the whole point of the reading being
frame-relative. -/

section Equational

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ### At the generality the argument has

Everything in this section is about a frame a setoid selects, and about nothing
else: the closure operator reads a declared former up to that setoid, the
positional split satisfies the cut under it, and the generator unfolds in any
frame closed under the semantics.  The readings this tree uses are instances,
and they are derived below rather than proved again. -/

/-- **A declared former is read up to the setoid.**  A term satisfies
`headed label body` as soon as *some* equivalent presentation of it is a
`label`-application whose argument satisfies `body`.  This is the frame's
closure operator doing the only work it is there to do. -/
theorem semEnv_headed_of_equiv_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (env : ScopeEnv) (label : String) (body : OSLFFormula) {term inner : Pattern}
    (presentation : equations.r term (.apply label [inner]))
    (holds : semEnv R (setoidFrame equations) I env body inner) :
    semEnv R (setoidFrame equations) I env (.headed label body) term :=
  ⟨.apply label [inner], presentation, inner, rfl, holds⟩

/-- **A positional split satisfies the cut.**  The closure only ever adds
decompositions, so a term written as a composition of two parts satisfies the
cut of their readings with no equation needed. -/
theorem semEnv_cut_of_split_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (env : ScopeEnv) (kind : CollType) (left right : OSLFFormula)
    (leftParts rightParts : List Pattern)
    (leftHolds : semEnv R (setoidFrame equations) I env left
      (.collection kind leftParts none))
    (rightHolds : semEnv R (setoidFrame equations) I env right
      (.collection kind rightParts none)) :
    semEnv R (setoidFrame equations) I env (.cut kind left right)
      (.collection kind (leftParts ++ rightParts) none) :=
  (setoidFrame equations).le_close _ _
    ⟨leftParts, rightParts, rfl, leftHolds, rightHolds⟩

/-- **The generator unfolds in any frame closed under the semantics.**  The
unfolding is displayed rather than abbreviated because it is what the step below
walks. -/
theorem sourceScope_unfold_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (frameClosed : FrameClosed R (setoidFrame equations) I)
    (env : ScopeEnv) (envMem : ∀ index, (setoidFrame equations).Mem (env index))
    (quoteLabel dropLabel leftAtom rightAtom : String) :
    semEnv R (setoidFrame equations) I env
        (sourceScope quoteLabel dropLabel leftAtom rightAtom)
      = semEnv R (setoidFrame equations) I env
          (.headed quoteLabel
            (.cut .hashBag
              (.or (.atom leftAtom)
                (.headed dropLabel
                  (sourceScope quoteLabel dropLabel leftAtom rightAtom)))
              (.or (.atom rightAtom)
                (.headed dropLabel
                  (sourceScope quoteLabel dropLabel leftAtom rightAtom))))) :=
  semEnv_mu_eq_unfold _ _ _ frameClosed _
    (sourceScope_closed quoteLabel dropLabel leftAtom rightAtom)
    (sourceScope_positive quoteLabel dropLabel leftAtom rightAtom) env envMem

/-- **The recursive step of the source's generator**, at that generality.  A
name already in the scope, dropped and composed with a part the right-hand
predicate accepts, quotes to a name in the scope again.  The drop is reached
through the setoid's identification of a one-element composition with its
element and through nothing else: that hypothesis is the one the ambient
powerset cannot supply, and `not_semEnv_headed_collection` is the record of its
absence there. -/
theorem sourceScope_step_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (frameClosed : FrameClosed R (setoidFrame equations) I)
    (quoteLabel dropLabel leftAtom rightAtom : String)
    {name rightPart : Pattern}
    (singletonLaw : equations.r
      (.collection .hashBag [.apply dropLabel [name]] none)
      (.apply dropLabel [name]))
    (inScope : semEnv R (setoidFrame equations) I ScopeEnv.empty
      (sourceScope quoteLabel dropLabel leftAtom rightAtom) name)
    (rightHolds : I rightAtom (.collection .hashBag [rightPart] none)) :
    semEnv R (setoidFrame equations) I ScopeEnv.empty
      (sourceScope quoteLabel dropLabel leftAtom rightAtom)
      (.apply quoteLabel
        [.collection .hashBag [.apply dropLabel [name], rightPart] none]) := by
  rw [sourceScope_unfold_setoid equations R I frameClosed ScopeEnv.empty
    (fun _ _ _ _ => Iff.rfl) quoteLabel dropLabel leftAtom rightAtom]
  refine (setoidFrame equations).le_close _ _
    ⟨.collection .hashBag [.apply dropLabel [name], rightPart] none, rfl, ?_⟩
  exact semEnv_cut_of_split_setoid equations R I ScopeEnv.empty .hashBag _ _
    [.apply dropLabel [name]] [rightPart]
    (Or.inr (semEnv_headed_of_equiv_setoid equations R I ScopeEnv.empty dropLabel _
      singletonLaw inScope))
    (Or.inl rightHolds)


variable (relEnv : RelationEnv) (lang : LanguageDef)

/-- **A declared former is read up to the equations.**  In the frame of the
generated logic a term satisfies `headed label body` as soon as *some*
presentation of it equivalent under the language's equations is a
`label`-application whose argument satisfies `body`.  This is the frame's
closure operator doing the only work it is there to do. -/
theorem semEnv_headed_of_equiv
    (I : EquationAtomSemUsing relEnv lang) (env : ScopeEnv)
    (label : String) (body : OSLFFormula) {term inner : Pattern}
    (presentation : (langGSLTUsing relEnv lang).Equiv term (.apply label [inner]))
    (holds : semEnv (langSemanticReducesUsing relEnv lang)
      (equationFrameUsing relEnv lang) (fun atom => (I atom).1) env body inner) :
    semEnv (langSemanticReducesUsing relEnv lang)
      (equationFrameUsing relEnv lang) (fun atom => (I atom).1) env
      (.headed label body) term :=
  semEnv_headed_of_equiv_setoid (langGSLTUsing relEnv lang).equations _ _ env label body
    presentation holds

/-- **A positional split satisfies the cut.**  The closure only ever adds
decompositions, so a term written as a composition of two parts satisfies the
cut of their readings with no equation needed. -/
theorem semEnv_cut_of_split
    (I : EquationAtomSemUsing relEnv lang) (env : ScopeEnv)
    (kind : CollType) (left right : OSLFFormula)
    (leftParts rightParts : List Pattern)
    (leftHolds : semEnv (langSemanticReducesUsing relEnv lang)
      (equationFrameUsing relEnv lang) (fun atom => (I atom).1) env left
      (.collection kind leftParts none))
    (rightHolds : semEnv (langSemanticReducesUsing relEnv lang)
      (equationFrameUsing relEnv lang) (fun atom => (I atom).1) env right
      (.collection kind rightParts none)) :
    semEnv (langSemanticReducesUsing relEnv lang)
      (equationFrameUsing relEnv lang) (fun atom => (I atom).1) env
      (.cut kind left right) (.collection kind (leftParts ++ rightParts) none) :=
  semEnv_cut_of_split_setoid (langGSLTUsing relEnv lang).equations _ _ env kind left right
    leftParts rightParts leftHolds rightHolds

/-- **The generator unfolds in the generated logic too**, where the frame is the
one the presentation's equations select.  The unfolding is displayed rather than
abbreviated because it is what the step below walks. -/
theorem sourceScope_unfold_equational
    (I : EquationAtomSemUsing relEnv lang)
    (quoteLabel dropLabel leftAtom rightAtom : String) :
    langSemUsing relEnv lang I (sourceScope quoteLabel dropLabel leftAtom rightAtom)
      = langSemUsing relEnv lang I
          (.headed quoteLabel
            (.cut .hashBag
              (.or (.atom leftAtom)
                (.headed dropLabel
                  (sourceScope quoteLabel dropLabel leftAtom rightAtom)))
              (.or (.atom rightAtom)
                (.headed dropLabel
                  (sourceScope quoteLabel dropLabel leftAtom rightAtom))))) :=
  sourceScope_unfold_setoid (langGSLTUsing relEnv lang).equations _ _
    (frameClosed_equationFrameUsing relEnv lang I) ScopeEnv.empty
    (equationInvariant_scopeEnv_empty relEnv lang)
    quoteLabel dropLabel leftAtom rightAtom

/-- **The recursive step of the source's generator.**  A name already in the
scope, dropped and composed with a part the right-hand predicate accepts, quotes
to a name in the scope again.  The drop is reached through the presentation's
singleton law and through nothing else: that hypothesis is the one the ambient
powerset cannot supply, and `not_semEnv_headed_collection` is the record of its
absence there. -/
theorem sourceScope_step
    (I : EquationAtomSemUsing relEnv lang)
    (quoteLabel dropLabel leftAtom rightAtom : String)
    {name rightPart : Pattern}
    (singletonLaw : (langGSLTUsing relEnv lang).Equiv
      (.collection .hashBag [.apply dropLabel [name]] none)
      (.apply dropLabel [name]))
    (inScope : langSemUsing relEnv lang I
      (sourceScope quoteLabel dropLabel leftAtom rightAtom) name)
    (rightHolds : (I rightAtom).1 (.collection .hashBag [rightPart] none)) :
    langSemUsing relEnv lang I
      (sourceScope quoteLabel dropLabel leftAtom rightAtom)
      (.apply quoteLabel
        [.collection .hashBag [.apply dropLabel [name], rightPart] none]) :=
  sourceScope_step_setoid (langGSLTUsing relEnv lang).equations _ _
    (frameClosed_equationFrameUsing relEnv lang I)
    quoteLabel dropLabel leftAtom rightAtom singletonLaw inScope rightHolds

/-- **A reading in the frame a setoid selects also sees only quotes**, this
time up to that setoid.  Stated at the setoid rather than at one presentation's
equations, because the argument is the same in every frame of that shape and
both of the readings this tree uses are of it. -/
theorem sourceScope_is_quote_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (quoteLabel dropLabel leftAtom rightAtom : String) {term : Pattern}
    (holds : semEnv R (setoidFrame equations) I ScopeEnv.empty
      (sourceScope quoteLabel dropLabel leftAtom rightAtom) term) :
    ∃ inner, equations.r term (.apply quoteLabel [inner]) := by
  refine holds (fun t => ∃ inner, equations.r t (.apply quoteLabel [inner]))
    ?invariant ?closed
  · rintro left right equivalent
    constructor
    · rintro ⟨inner, presentation⟩
      exact ⟨inner, equations.iseqv.trans (equations.iseqv.symm equivalent) presentation⟩
    · rintro ⟨inner, presentation⟩
      exact ⟨inner, equations.iseqv.trans equivalent presentation⟩
  · rintro t ⟨representative, equivalent, inner, shape, -⟩
    exact ⟨inner, shape ▸ equivalent⟩

/-- The generated logic's reading, as one instance of it.  **What this says
about a given presentation depends entirely on that presentation's equations**,
and on one of them it says nothing at all -- see the platform's record of an
equation theory in which every term is equivalent to a quote. -/
theorem sourceScope_is_quote_equational
    (I : EquationAtomSemUsing relEnv lang)
    (quoteLabel dropLabel leftAtom rightAtom : String) {term : Pattern}
    (holds : langSemUsing relEnv lang I
      (sourceScope quoteLabel dropLabel leftAtom rightAtom) term) :
    ∃ inner, (langGSLTUsing relEnv lang).Equiv term (.apply quoteLabel [inner]) :=
  sourceScope_is_quote_setoid (langGSLTUsing relEnv lang).equations
    (langSemanticReducesUsing relEnv lang) (fun atom => (I atom).1)
    quoteLabel dropLabel leftAtom rightAtom holds

end Equational

/-! ## A specimen -/

namespace Specimen

/-- The two atoms of the scope. -/
def atomA : Pattern := .apply "A" []
def atomB : Pattern := .apply "B" []

/-- A part, as the cut presents it. -/
def part (term : Pattern) : Pattern := .collection .hashBag [term] none

/-- The atom reading: each atom accepts its own part. -/
def atoms : AtomCheck := fun name term =>
  (name == "A" && term == part atomA) || (name == "B" && term == part atomB)

/-- Nothing reduces here; the scope is about shape, not about steps. -/
def inert : Pattern → List Pattern := fun _ => []

/-- The quote of a composition of the two atoms. -/
def baseName : Pattern :=
  .apply "NQuote" [.collection .hashBag [atomA, atomB] none]

/-- **The base case is in the scope**, checked in the kernel. -/
theorem baseName_in_scope :
    check inert atoms 8 baseName (rhoScope "A" "B") = .sat := by
  decide +kernel

/-- **The recursive step does not fire in the ambient frame, and the reason is
exactly the one the header names.**  The cut presents a part as a *singleton
collection*, so the drop former — which asks for a term headed by `PDrop` — does
not match `{PDrop n}`.  What identifies the two is the singleton law, which a
presentation declaring a collection algebra derives and the ambient powerset
does not have.  So the coercion step of the source's generator is a statement
about the equation frame, and the checker, being positional, cannot answer it. -/
theorem droppedName_not_positional :
    check inert atoms 8
        (.apply "NQuote"
          [.collection .hashBag [.apply "PDrop" [baseName], atomB] none])
        (rhoScope "A" "B") = .unknown := by
  decide +kernel

/-- **Soundness**: what the checker answers, the semantics holds. -/
theorem baseName_sem (R : Pattern → Pattern → Prop) (I : AtomSem)
    (agree : ∀ name term, atoms name term = true → I name term)
    (steps : ∀ source target, target ∈ inert source → R source target) :
    sem R I (rhoScope "A" "B") baseName :=
  check_sat_sound agree steps baseName_in_scope

/-- **Negative.**  A term that is not a quote at all the checker cannot place in
the scope. -/
theorem atomA_not_placed :
    check inert atoms 8 atomA (rhoScope "A" "B") = .unknown := by
  decide +kernel

end Specimen

end Mettapedia.OSLF.Framework.SourceGenerator
