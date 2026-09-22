import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofFamily
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDeclarationSpine

/-!
# Conversion separation for the native HOL proof decoder

A concrete untyped expansion sends the two proof-decoder equations to pure
beta conversion. Because this expansion preserves Pi, Sigma and universe
heads, the pure conversion theorem establishes their separation in the full
decoder presentation. The expansion is only a sound observation of conversion:
it is not a typing interpretation or a conversion-reflecting embedding.

Consequently the separation theorems below do not claim Pi/Sigma component
injectivity, arbitrary subject reduction, normalization or consistency.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofConversion

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLProofFamily ConstantExpansion

def decoderBody : Tower.Tm 0 := .lam (.var 0)

def implicationBody : Tower.Tm 0 := .lam (.lam (.pi (.var 1) (.var 1)))

def universalBody : Tower.Tm 0 :=
  .lam (.lam (.pi (.var 1) (.app (.var 1) (.var 0))))

/-- These bodies are an auxiliary conversion observation. They are not
installed as source definitions and are not asserted to have source types. -/
def bodies : Bodies Tower.Head := fun name =>
  if name = proofName then decoderBody
  else if name = `HOLUniformList.implication then implicationBody
  else if name = `HOLUniformList.universal then universalBody
  else .const name

abbrev observe {n : Nat} (term : Tower.Tm n) : Tower.Tm n := expand bodies term

private theorem opaque_insert (signature : Signature Tower.Head) (name : DeclName)
    (type : Tower.Tm 0) (noValues : ∀ candidate, signature.valueOf? candidate = none) :
    ∀ candidate, (signature.insert name ⟨type, none⟩).valueOf? candidate = none := by
  intro candidate
  by_cases equal : candidate = name
  · subst candidate
    exact Signature.valueOf_insert_eq signature name ⟨type, none⟩
  · simpa only [Signature.valueOf?, Signature.insert, if_neg equal] using noValues candidate

theorem declarations_opaque (name : DeclName) : declarations.valueOf? name = none := by
  have source : ∀ candidate, FormationSensitiveHOLUniformList.declarations.valueOf? candidate = none := by
    unfold FormationSensitiveHOLUniformList.declarations Signature.ofList
    simp only [List.foldr]
    repeat' apply opaque_insert
    intro candidate
    rfl
  exact opaque_insert _ proofName proofType source name

@[simp] theorem bodies_proof : bodies proofName = decoderBody := by decide
@[simp] theorem bodies_implication : bodies `HOLUniformList.implication = implicationBody := by decide
@[simp] theorem bodies_universal : bodies `HOLUniformList.universal = universalBody := by decide

private theorem decoder_beta {n : Nat} (term : Tower.Tm n) :
    Conv Tower.HeadEq (.app (liftClosed decoderBody) term) term := by
  simpa only [decoderBody, liftClosed, rename, liftRen, Fin.cases_zero,
    inst0, subst, subst0, consSub] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (headEq := Tower.HeadEq)
      (.var (0 : Fin (n + 1))) term))

private theorem implication_beta {n : Nat} (p q : Tower.Tm n) :
    Conv Tower.HeadEq (.app (.app (liftClosed implicationBody) p) q)
      (.pi p (rename wk q)) := by
  change Conv Tower.HeadEq (.app (.app (.lam (.lam (.pi (.var 1) (.var 1)))) p) q) _
  refine .trans _ _ _ (Conv.congApp (.rel _ _ (.betaPi _ _)) (.refl _)) ?_
  change Conv Tower.HeadEq (.app (.lam (.pi (rename wk p) (.var 1))) q) _
  have opened : inst0 q (.pi (rename wk p) (.var 1)) = .pi p (rename wk q) := by
    change Tm.pi (inst0 q (rename wk p)) _ = Tm.pi p (rename wk q)
    rw [inst0_rename_wk]
    rfl
  simpa only [opened] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (headEq := Tower.HeadEq) (root := RootComputation.empty)
      (.pi (rename wk p) (.var 1)) q))

private theorem universal_beta {n : Nat} (a f : Tower.Tm n) :
    Conv Tower.HeadEq (.app (.app (liftClosed universalBody) a) f)
      (.pi a (.app (rename wk f) (.var 0))) := by
  change Conv Tower.HeadEq
    (.app (.app (.lam (.lam (.pi (.var 1) (.app (.var 1) (.var 0))))) a) f) _
  refine .trans _ _ _ (Conv.congApp (.rel _ _ (.betaPi _ _)) (.refl _)) ?_
  change Conv Tower.HeadEq (.app (.lam (.pi (rename wk a) (.app (.var 1) (.var 0)))) f) _
  have opened : inst0 f (.pi (rename wk a) (.app (.var 1) (.var 0))) =
      .pi a (.app (rename wk f) (.var 0)) := by
    change Tm.pi (inst0 f (rename wk a)) _ = Tm.pi a (.app (rename wk f) (.var 0))
    rw [inst0_rename_wk]
    rfl
  simpa only [opened] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (headEq := Tower.HeadEq) (root := RootComputation.empty)
      (.pi (rename wk a) (.app (.var 1) (.var 0))) f))

theorem observe_proof {n : Nat} (p : Tower.Tm n) :
    Conv Tower.HeadEq (observe (proof p)) (observe p) := by
  simpa only [observe, proof, expand, bodies_proof] using decoder_beta (observe p)

theorem observe_implication {n : Nat} (p q : Tower.Tm n) :
    Conv Tower.HeadEq (observe (FormationSensitiveHOLUniformList.rawImp p q))
      (.pi (observe p) (rename wk (observe q))) := by
  simpa only [observe, FormationSensitiveHOLUniformList.rawImp, expand, bodies_implication]
    using implication_beta (observe p) (observe q)

theorem observe_universal {n : Nat} (a f : Tower.Tm n) :
    Conv Tower.HeadEq (observe (universalProposition a f))
      (.pi (observe a) (.app (rename wk (observe f)) (.var 0))) := by
  simpa only [observe, universalProposition, expand, bodies_universal]
    using universal_beta (observe a) (observe f)

theorem decoder_expansion {n : Nat} {left right : Tower.Tm n}
    (step : DecoderStep left right) : Conv Tower.HeadEq (observe left) (observe right) := by
  cases step with
  | implication p q =>
      refine .trans _ _ _ (observe_proof _) (.trans _ _ _ (observe_implication p q) ?_)
      exact .symm _ _ (Conv.congPi (observe_proof p)
        (by simpa only [expand_rename] using (observe_proof q).renameTerms wk))
  | universal a f =>
      refine .trans _ _ _ (observe_proof _) (.trans _ _ _ (observe_universal a f) ?_)
      exact .symm _ _ (Conv.congPi (.refl _)
        (by simpa only [expand, expand_rename] using observe_proof (.app (rename wk f) (.var 0))))

theorem root_expansion {n : Nat} {left right : Tower.Tm n}
    (step : rules.computation.step left right) :
    Conv Tower.HeadEq (observe left) (observe right) := by
  cases step with
  | inherited impossible => exact impossible.elim
  | @delta name value lookup => rw [declarations_opaque] at lookup; cases lookup
  | declared decoder => exact decoder_expansion decoder

theorem conversion_observed {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv rules.headEq left right rules.computation) :
    Conv Tower.HeadEq (observe left) (observe right) :=
  conv_expand bodies root_expansion conversion

/-- No decoder-mediated conversion path can collapse a Pi into a universe head. -/
theorem pi_head_separated {n : Nat} (a : Tower.Tm n) (b : Tower.Tm (n + 1))
    (head : Tower.Head) : ¬ Conv rules.headEq (.pi a b) (.head head) rules.computation := by
  intro conversion
  exact Tower.piConversionBoundary.headDisjoint (conversion_observed conversion)

theorem sigma_head_separated {n : Nat} (a : Tower.Tm n) (b : Tower.Tm (n + 1))
    (head : Tower.Head) : ¬ Conv rules.headEq (.sigma a b) (.head head) rules.computation := by
  intro conversion
  exact (EmptyRootConversion.sigmaConversionBoundary Tower.rules rfl Tower.headEq_symmetric).headDisjoint
    (conversion_observed conversion)

private theorem pure_sort_step {n : Nat} {level : LevelExpr} {target : Tower.Tm n}
    (step : Step Tower.HeadEq (sortTm level) target) :
    ∃ finalLevel, target = sortTm finalLevel ∧
      ∀ valuation, LevelExpr.eval valuation finalLevel = LevelExpr.eval valuation level := by
  cases step with
  | head related =>
      rename_i right
      cases right with
      | legacyGround => cases related
      | sort finalLevel => exact ⟨finalLevel, rfl, fun valuation => (related valuation).symm⟩
  | root impossible => cases impossible

private theorem pure_sort_path {n : Nat} {level : LevelExpr} {target : Tower.Tm n}
    (steps : ConversionCoherence.StepStar Tower.rules (sortTm level) target) :
    ∃ finalLevel, target = sortTm finalLevel ∧
      ∀ valuation, LevelExpr.eval valuation finalLevel = LevelExpr.eval valuation level := by
  induction steps with
  | refl => exact ⟨level, rfl, fun _ => rfl⟩
  | tail previous step ih =>
      obtain ⟨middle, rfl, previousMeaning⟩ := ih
      obtain ⟨finalLevel, rfl, finalMeaning⟩ := pure_sort_step step
      exact ⟨finalLevel, rfl, fun valuation => (finalMeaning valuation).trans (previousMeaning valuation)⟩

/-- Decoder conversion adds no new equalities between universe levels. -/
theorem sort_conversion_iff {n : Nat} (first second : LevelExpr) :
    Conv rules.headEq (sortTm (n := n) first) (sortTm second) rules.computation ↔
      ∀ valuation, LevelExpr.eval valuation first = LevelExpr.eval valuation second := by
  constructor
  · intro conversion
    obtain ⟨common, firstPath, secondPath⟩ := Tower.churchRosser (conversion_observed conversion)
    obtain ⟨firstEnd, firstShape, firstMeaning⟩ := pure_sort_path firstPath
    obtain ⟨secondEnd, secondShape, secondMeaning⟩ := pure_sort_path secondPath
    have ends : firstEnd = secondEnd := Tower.Head.sort.inj
      (Tm.head.inj (firstShape.symm.trans secondShape))
    intro valuation
    exact (firstMeaning valuation).symm.trans
      ((congrArg (LevelExpr.eval valuation) ends).trans (secondMeaning valuation))
  · intro same
    exact .rel _ _ (.head same)

theorem zero_not_successor {n : Nat} :
    ¬ Conv rules.headEq (sortTm (n := n) Tower.zero) (sortTm (.succ Tower.zero))
      rules.computation := by
  intro conversion
  have impossible := (sort_conversion_iff Tower.zero (.succ Tower.zero)).mp conversion (fun _ => 0)
  simp [LevelExpr.eval, Tower.zero] at impossible

/-- In particular, cumulativity cannot hide a sort step in a type adjustment
whose final type is a dependent product. No Pi-injectivity premise is needed. -/
theorem adjustment_to_pi {n : Nat} {source a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (adjustment : TypeAdjustment rules source (.pi a b)) :
    Conv rules.headEq source (.pi a b) rules.computation :=
  adjustment.toConvOfTargetDisjointHeads (pi_head_separated a b)

theorem adjustment_to_sigma {n : Nat} {source a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (adjustment : TypeAdjustment rules source (.sigma a b)) :
    Conv rules.headEq source (.sigma a b) rules.computation :=
  adjustment.toConvOfTargetDisjointHeads (sigma_head_separated a b)

/-- For the actual translated implication introduction/elimination pair,
substitution constructs the contractum at the same proof family. This does
not require arbitrary target Pi-conversion injectivity. -/
theorem implication_beta_preserves {n : Nat} {gamma : Tower.Ctx n}
    {p q argument : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (hp : Typing rules gamma p (.const `HOLUniformList.prop))
    (hq : Typing rules gamma q (.const `HOLUniformList.prop))
    (hb : Typing rules (.snoc gamma (proof p)) body (rename wk (proof q)))
    (ha : Typing rules gamma argument (proof p)) :
    Typing rules gamma (.app (.lam body) argument) (proof q) ∧
    Step rules.headEq (.app (.lam body) argument) (inst0 argument body) rules.computation ∧
    Typing rules gamma (inst0 argument body) (proof q) := by
  refine ⟨implication_elim hp hq (implication_intro hp hq hb) ha, .betaPi body argument, ?_⟩
  simpa only [inst0_rename_wk] using hb.instantiate ha

/-- Universal proof specialization genuinely substitutes the argument into
the proposition family as well as the proof body. -/
theorem universal_beta_preserves {n : Nat} {gamma : Tower.Ctx n}
    {a argument : Tower.Tm n} {p body : Tower.Tm (n + 1)}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hp : Typing rules (.snoc gamma a) p (.const `HOLUniformList.prop))
    (hb : Typing rules (.snoc gamma a) body (proof p))
    (ht : Typing rules gamma argument a) :
    Typing rules gamma (.app (.lam body) argument) (proof (inst0 argument p)) ∧
    Step rules.headEq (.app (.lam body) argument) (inst0 argument body) rules.computation ∧
    Typing rules gamma (inst0 argument body) (proof (inst0 argument p)) := by
  refine ⟨universal_elim ha hp (universal_intro ha hp hb) ht, .betaPi body argument, ?_⟩
  simpa only [inst0, proof_subst] using hb.instantiate ht

/-- The observation forgets syntax: even a neutral, undecoded proof family
has the same observed conversion value as its proposition argument. This
does not claim those source terms are convertible. -/
theorem observation_forgets_neutral_decoder :
    (proof (.var (0 : Fin 1)) : Tower.Tm 1) ≠ .var 0 ∧
    (∀ target : Tower.Tm 1, ¬ DecoderStep (proof (.var 0)) target) ∧
    Conv Tower.HeadEq (observe (proof (.var (0 : Fin 1)))) (observe (.var 0)) := by
  refine ⟨?_, ?_, observe_proof _⟩
  · intro equality
    cases equality
  · exact variable_has_no_decoder_step _

#print axioms decoder_expansion
#print axioms conversion_observed
#print axioms pi_head_separated
#print axioms sigma_head_separated
#print axioms sort_conversion_iff
#print axioms zero_not_successor
#print axioms adjustment_to_pi
#print axioms adjustment_to_sigma
#print axioms implication_beta_preserves
#print axioms universal_beta_preserves
#print axioms observation_forgets_neutral_decoder

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofConversion
