import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Housekeeping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

/-!
# The reflective calculus on the step of a program, by ordinary instantiation

The step is `RuleSyntax.step` of the four-rule `program` at the contextual frames of the
twin-binder signature (`theStep`). Its transitions are `Succ theStep.toStep`.

* `succ_iff`: every transition is a communication or a housekeeping firing.
* existence: `canonical_admits`, `copair_solves`, and the firings of each rule at every state that
  has the row it takes (`heat_exists`, `clearBag_exists`, `clearZero_exists`, `comm_exists`).
* `heats_to_primes`: housekeeping firings reach a state whose rows are primes.
* `communication_complete`: every source reduction is matched by housekeeping firings and one
  communication.
* **`reflective_calculus_by_instantiation`**: the representation is a weak bisimulation between
  the source reduction modulo the equations, for all closed processes, and the step of the
  program, whose made row of communication is the continuation instantiated at the received name
  and process; housekeeping runs are bounded by the spine weight.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-! ## Transitions -/

/-- A communication firing. -/
def Communicates (s s' : State) : Prop :=
  ∃ f : Firing s, f.rule = commRule ∧ f.Admits knowledge s ∧ f.result knowledge s = s'

/-- A housekeeping firing: heating or clearing. -/
def Administers (s s' : State) : Prop :=
  ∃ f : Firing s, (f.rule = heatRule ∨ f.rule = clearBagRule ∨ f.rule = clearZeroRule) ∧
    f.Admits knowledge s ∧ f.result knowledge s = s'

/-- **Every transition of the step is a communication or housekeeping.** -/
theorem succ_iff (s s' : State) :
    LogicOverTheStep.StepSpan.Succ theStep.toStep s s' ↔ Communicates s s' ∨ Administers s s' := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    rcases mem_program.mp f.member with isComm | isHeat | isBag | isZero
    · exact .inl ⟨f, isComm, admitted, rfl⟩
    · exact .inr ⟨f, .inl isHeat, admitted, rfl⟩
    · exact .inr ⟨f, .inr (.inl isBag), admitted, rfl⟩
    · exact .inr ⟨f, .inr (.inr isZero), admitted, rfl⟩
  · rintro (⟨f, _, admitted, rfl⟩ | ⟨f, _, admitted, rfl⟩)
    · exact ⟨f, admitted, rfl⟩
    · exact ⟨f, admitted, rfl⟩

/-- **Housekeeping keeps the represented process and decreases the weight.** -/
theorem administration_decreases {s s' : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (fires : Administers s s') :
    ∃ value' : ℕ → G [] .pr, RepresentsBy s' P value' ∧
      weightOf s'.present value' < weightOf s.present value := by
  obtain ⟨f, kind, admitted, rfl⟩ := fires
  rcases kind with isHeat | isBag | isZero
  · exact heat_effect represented f isHeat admitted
  · exact ⟨value, clearBag_effect represented f isBag admitted⟩
  · exact ⟨value, clearZero_effect represented f isZero admitted⟩

/-- Runs of exactly `k` housekeeping firings. -/
inductive AdministrativeRun : ℕ → State → State → Prop
  | refl (s : State) : AdministrativeRun 0 s s
  | head {k : ℕ} {s t u : State} : Administers s t → AdministrativeRun k t u →
      AdministrativeRun (k + 1) s u

/-- **Housekeeping is bounded** by the spine weight. -/
theorem administration_bounded {s e : State} {P : RhoProcess} {value : ℕ → G [] .pr} {k : ℕ}
    (represented : RepresentsBy s P value) (run : AdministrativeRun k s e) :
    k ≤ weightOf s.present value := by
  induction run generalizing value with
  | refl => exact Nat.zero_le _
  | head fires _ earlier =>
      obtain ⟨value', represented', lighter⟩ := administration_decreases represented fires
      have bound := earlier represented'
      omega

/-- **Every communication firing is a source reduction.** -/
theorem communication_sound {s s' : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (fires : Communicates s s') :
    ∃ (P' : RhoProcess) (value' : ℕ → G [] .pr),
      rhoLanguageDefGSLT.Step P P' ∧ RepresentsBy s' P' value' := by
  obtain ⟨f, isComm, admitted, rfl⟩ := fires
  obtain ⟨o₁, o₂, rule, value', _, _, _, source, target⟩ := comm_effect represented f isComm admitted
  have restPrimes : ∀ pattern ∈ inventoryOf (s.present \ {o₁, o₂}) value, IsPrime pattern := by
    have whole : ∀ pattern ∈ (fromProcess P).1, IsPrime pattern := (fromProcess P).2
    intro pattern member
    exact whole pattern (by rw [source]; exact Multiset.mem_add.mpr (.inr member))
  let rest : Bag := ⟨inventoryOf (s.present \ {o₁, o₂}) value, restPrimes⟩
  let P' := toProcess (append rule.reactum rest)
  have readP' : (fromProcess P').1 = rule.reactum.1 + inventoryOf (s.present \ {o₁, o₂}) value := by
    simp only [P', fromProcess_toProcess, append_inventory]
    rfl
  refine ⟨P', value', ?_, target P' readP'⟩
  apply (publicStep_iff P P').mpr
  refine ⟨rule, rest, ?_, by simp only [P', fromProcess_toProcess]⟩
  apply Subtype.ext
  rw [source, append_inventory]

/-! ## Existence of firings -/

/-- **A canonically opened rule with a well-shaped selection is admitted** once a grounding solves
its information. -/
theorem canonical_admits {s : State} (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig))
    (member : r ∈ program) (selection : Selection ℕ) (noRead : selection.read = [])
    (noChecks : r.body.checks = []) (noCollect : r.collect = [])
    (takenNodup : selection.taken.Nodup) (madeNodup : selection.made.Nodup)
    (takeLen : r.body.take.length = selection.taken.length) (readLen : r.body.read.length = 0)
    (produceLen : r.body.produce.length = selection.made.length)
    (takenPresent : ∀ o ∈ selection.taken, o ∈ s.present)
    (madeFresh : ∀ o ∈ selection.made, o ∉ s.present)
    (solved : ∃ g, GroundSolves g
      ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information knowledge s)) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Admits knowledge s := by
  refine ⟨⟨canonical_fresh_here s r member selection [], takenNodup, madeNodup, takeLen, ?_, produceLen,
    by simp [RuleSyntax.Contextual.canonical, noCollect]⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    (solvable_iff _).mpr solved, ?_⟩
  · show r.body.read.length = selection.read.length
    rw [readLen, noRead]
    rfl
  · intro o inside
    exact takenPresent o (by simpa [RuleSyntax.Contextual.canonical, Selection.commit] using inside)
  · intro o inside
    simp [RuleSyntax.Contextual.canonical, Selection.commit, noRead] at inside
  · simp [RuleSyntax.Contextual.canonical, Selection.commit, noRead]
  · rw [Finset.disjoint_left]
    intro o inside
    exact madeFresh o (by simpa [RuleSyntax.Contextual.canonical, Selection.commit] using inside)
  · intro query inside
    simp [RuleSyntax.Contextual.canonical, Selection.commit] at inside
  · intro _ _ _
    have noOpenedChecks : (RuleSyntax.Firing.opened knowledge
        (RuleSyntax.Contextual.canonical (F := s.frame) r member selection [])).checks = [] := by
      simp [RuleSyntax.Firing.opened, RuleInstance.map, RuleSyntax.Contextual.canonical, noChecks]
    have noOpenedCollect : (RuleSyntax.Firing.collectOpened knowledge
        (RuleSyntax.Contextual.canonical (F := s.frame) r member selection [])) = [] := by
      simp [RuleSyntax.Firing.collectOpened, RuleSyntax.Contextual.canonical, noCollect]
    refine ⟨fun c inside => ?_, fun q inside => ?_⟩
    · rw [noOpenedChecks] at inside
      exact nomatch inside
    · rw [noOpenedCollect] at inside
      exact nomatch inside

/-- **The grounding of a canonical firing**: a solution of the knowledge and an assignment of the
rule's unknowns that equates each take pattern with its row. -/
theorem copair_solves {s : State} (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig))
    (member : r ∈ program) (selection : Selection ℕ) (noRead : selection.read = [])
    (noTell : r.body.tell = []) (g₀ : Grounding s.frame) (known : GroundSolves g₀ s.knowledge)
    (h : Grounding r.locals)
    (takes : ∀ p o, (p, o) ∈ r.body.take.zip selection.taken →
      ObsSimilar (instantiateObservation h p) (instantiateObservation g₀ (s.label o))) :
    GroundSolves (RuleSyntax.Contextual.copair sig (B := groundFrame) g₀ h)
      ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
        knowledge s) := by
  intro e inside
  unfold RuleSyntax.Firing.information at inside
  rcases List.mem_append.mp inside with inside | tellPart
  rotate_left
  · simp [RuleSyntax.Firing.opened, RuleInstance.map, RuleSyntax.Contextual.canonical,
      noTell] at tellPart
    exact nomatch tellPart
  rcases List.mem_append.mp inside with inside | readPart
  rotate_left
  · simp [RuleSyntax.Firing.matching, RuleSyntax.Contextual.canonical, noRead] at readPart
    exact nomatch readPart
  rcases List.mem_append.mp inside with old | taken
  · obtain ⟨e₀, inKnowledge, rfl⟩ := List.mem_map.mp old
    change ObsSimilar (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) g₀ h)
        (instantiateObservation (RuleSyntax.Contextual.weakenNames sig s.frame r.locals) e₀.1))
      (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) g₀ h)
        (instantiateObservation (RuleSyntax.Contextual.weakenNames sig s.frame r.locals) e₀.2))
    rw [RuleSyntax.Contextual.copair_weaken, RuleSyntax.Contextual.copair_weaken]
    exact known e₀ inKnowledge
  · unfold RuleSyntax.Firing.matching at taken
    rw [← List.map_uncurry_zip_eq_zipWith] at taken
    obtain ⟨⟨p, o⟩, pair, rfl⟩ := List.mem_map.mp taken
    simp only [RuleSyntax.Firing.opened, RuleInstance.map, RuleSyntax.Contextual.canonical,
      List.zip_map_left] at pair
    obtain ⟨⟨p₀, o₀⟩, pair₀, same⟩ := List.mem_map.mp pair
    have hp : knowledge.act (RuleSyntax.Contextual.canonicalOpening sig s.frame r.locals) p₀ = p :=
      congrArg Prod.fst same
    have ho : o₀ = o := congrArg Prod.snd same
    subst hp
    subst ho
    change ObsSimilar (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) g₀ h)
        (instantiateObservation (RuleSyntax.Contextual.canonicalOpening sig s.frame r.locals) p₀))
      (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) g₀ h)
        (instantiateObservation (RuleSyntax.Contextual.weakenNames sig s.frame r.locals) (s.label o₀)))
    rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_weaken]
    exact takes p₀ o₀ pair₀

/-- Two occurrence identities not in a set, and different. -/
theorem two_fresh (present : Finset ℕ) :
    ∃ o₄ o₅ : ℕ, o₄ ∉ present ∧ o₅ ∉ present ∧ o₄ ≠ o₅ := by
  classical
  obtain ⟨o₄, fresh₄⟩ := Infinite.exists_notMem_finset present
  obtain ⟨o₅, fresh₅⟩ := Infinite.exists_notMem_finset (insert o₄ present)
  exact ⟨o₄, o₅, fresh₄, fun inside => fresh₅ (Finset.mem_insert_of_mem inside),
    fun same => fresh₅ (same ▸ Finset.mem_insert_self o₄ present)⟩

/-- The row a value is, under a solution of the knowledge, as an observation similar to it. -/
theorem row_similar {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {g₀ : Grounding s.frame}
    (known : GroundSolves g₀ s.knowledge) {o : ℕ} (present : o ∈ s.present) {t : G [] .pr}
    (similar : Similar t (value o)) :
    ObsSimilar ⟨[], .pr, t⟩ (instantiateObservation g₀ (s.label o)) := by
  obtain ⟨u, at', related⟩ := represented.determined g₀ known o present
  rw [at']
  exact .mk (similar_trans similar (similar_symm related))

/-- **Heating fires at every row whose value is a bag with a first component.** -/
theorem heat_exists {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o : ℕ} (present : o ∈ s.present) {a : G [] .pr}
    {r : G [] .ps} (shape : value o = bagT (pconsT a r)) : ∃ s', Administers s s' := by
  classical
  obtain ⟨g₀, known⟩ := represented.solvable
  obtain ⟨o₄, o₅, fresh₄, fresh₅, distinct⟩ := two_fresh s.present
  let h : Grounding heatFrame := fun
    | .first => a
    | .rest => r
  let selection : Selection ℕ := ⟨[o], [], [o₄, o₅]⟩
  have admitted := canonical_admits (s := s) heatRule heatRule_mem selection rfl rfl rfl
    (by simp [selection]) (by simp [selection, distinct]) rfl rfl rfl
    (by simp [selection, present]) (by
      intro x inside
      simp only [selection, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact fresh₄
      · exact fresh₅)
    ⟨_, copair_solves heatRule heatRule_mem selection rfl rfl g₀ known h (by
      intro p x inside
      simp only [selection, heatRule, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at inside
      obtain ⟨rfl, rfl⟩ := inside
      have instantiated : instantiate h heatBag = bagT (pconsT a r) := instantiate_heatBag h
      change ObsSimilar ⟨[], .pr, instantiate h heatBag⟩ _
      rw [instantiated]
      exact row_similar represented known present (by rw [shape]; exact similar_refl _))⟩
  exact ⟨_, _, .inl rfl, admitted, rfl⟩

/-- **Clearing fires at every row whose value is the empty bag.** -/
theorem clearBag_exists {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o : ℕ} (present : o ∈ s.present)
    (shape : value o = bagT pnilT) : ∃ s', Administers s s' := by
  classical
  obtain ⟨g₀, known⟩ := represented.solvable
  let h : Grounding groundFrame := fun e => nomatch e
  let selection : Selection ℕ := ⟨[o], [], []⟩
  have admitted := canonical_admits (s := s) clearBagRule clearBagRule_mem selection rfl rfl rfl
    (by simp [selection]) (by simp [selection]) rfl rfl rfl
    (by simp [selection, present]) (by simp [selection])
    ⟨_, copair_solves clearBagRule clearBagRule_mem selection rfl rfl g₀ known h (by
      intro p x inside
      simp only [selection, clearBagRule, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at inside
      obtain ⟨rfl, rfl⟩ := inside
      exact row_similar represented known present (by rw [shape]; exact similar_refl _))⟩
  exact ⟨_, _, .inr (.inl rfl), admitted, rfl⟩

/-- **Clearing fires at every row whose value is the null process.** -/
theorem clearZero_exists {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o : ℕ} (present : o ∈ s.present)
    (shape : value o = zeroT) : ∃ s', Administers s s' := by
  classical
  obtain ⟨g₀, known⟩ := represented.solvable
  let h : Grounding groundFrame := fun e => nomatch e
  let selection : Selection ℕ := ⟨[o], [], []⟩
  have admitted := canonical_admits (s := s) clearZeroRule clearZeroRule_mem selection rfl rfl rfl
    (by simp [selection]) (by simp [selection]) rfl rfl rfl
    (by simp [selection, present]) (by simp [selection])
    ⟨_, copair_solves clearZeroRule clearZeroRule_mem selection rfl rfl g₀ known h (by
      intro p x inside
      simp only [selection, clearZeroRule, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at inside
      obtain ⟨rfl, rfl⟩ := inside
      exact row_similar represented known present (by rw [shape]; exact similar_refl _))⟩
  exact ⟨_, _, .inr (.inr rfl), admitted, rfl⟩

/-- **Communication fires between an input row and an output row on similar channels.** -/
theorem comm_exists {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) {c₁ c₂ : G [] .nm} {b₁ : G [.nm, .pr] .pr}
    {q₂ : G [] .pr} (shape₁ : value o₁ = inputT c₁ b₁) (shape₂ : value o₂ = outputT c₂ q₂)
    (channels : Similar c₁ c₂) :
    ∃ f : Firing s, f.rule = commRule ∧ f.Admits knowledge s ∧ f.selection.taken = [o₁, o₂] := by
  classical
  obtain ⟨g₀, known⟩ := represented.solvable
  obtain ⟨o₃, fresh₃⟩ := Infinite.exists_notMem_finset s.present
  let h : Grounding commFrame := fun
    | .channel => c₁
    | .body => b₁
    | .payload => q₂
  let selection : Selection ℕ := ⟨[o₁, o₂], [], [o₃]⟩
  have admitted := canonical_admits (s := s) commRule commRule_mem selection rfl rfl rfl
    (by simp [selection, distinct]) (by simp [selection]) rfl rfl rfl
    (by simp [selection, present₁, present₂]) (by simp [selection, fresh₃])
    ⟨_, copair_solves commRule commRule_mem selection rfl rfl g₀ known h (by
      intro p x inside
      simp only [selection, commRule, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at inside
      rcases inside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have instantiated : instantiate h commInput = inputT c₁ b₁ := instantiate_commInput h
        change ObsSimilar ⟨[], .pr, instantiate h commInput⟩ _
        rw [instantiated]
        exact row_similar represented known present₁ (by rw [shape₁]; exact similar_refl _)
      · have instantiated : instantiate h commOutput = outputT c₁ q₂ := instantiate_commOutput h
        change ObsSimilar ⟨[], .pr, instantiate h commOutput⟩ _
        rw [instantiated]
        exact row_similar represented known present₂
          (by rw [shape₂]; exact .output channels (similar_refl _)))⟩
  exact ⟨_, rfl, admitted, rfl⟩

/-! ## Heating to primes -/

/-- A closed value with a positive spine is the null process or a bag. -/
theorem spine_pos_shape : ∀ (v : G [] .pr), spine v ≠ 0 →
    v = zeroT ∨ v = bagT pnilT ∨ ∃ a r, v = bagT (pconsT a r)
  | .op (.inl .zero) .nil, _ => .inl rfl
  | .op (.inl .bag) (.cons (.op (.inl .pnil) .nil) .nil), _ => .inr (.inl rfl)
  | .op (.inl .bag) (.cons (.op (.inl .pcons) (.cons a (.cons r .nil))) .nil), _ =>
      .inr (.inr ⟨a, r, rfl⟩)
  | .op (.inl .bag) (.cons (.op (.inr o) _) .nil), _ => o.key.elim
  | .op (.inl .input) _, positive => absurd rfl positive
  | .op (.inl .output) _, positive => absurd rfl positive
  | .op (.inl .dropq) _, positive => absurd rfl positive
  | .op (.inr o) _, _ => o.key.elim

/-- **Heating reaches primes**: housekeeping firings reach a state representing the same process
whose rows all have spine zero. -/
theorem heats_to_primes {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) :
    ∃ (s' : State) (value' : ℕ → G [] .pr), Relation.ReflTransGen Administers s s' ∧
      RepresentsBy s' P value' ∧ ∀ o ∈ s'.present, spine (value' o) = 0 := by
  classical
  induction hw : weightOf s.present value using Nat.strong_induction_on generalizing s value with
  | _ w earlier =>
    by_cases heated : ∀ o ∈ s.present, spine (value o) = 0
    · exact ⟨s, value, .refl, represented, heated⟩
    · simp only [not_forall] at heated
      obtain ⟨o, present, positive⟩ := heated
      obtain ⟨s₁, fires⟩ : ∃ s₁, Administers s s₁ := by
        rcases spine_pos_shape (value o) positive with zero | empty | ⟨a, r, bag⟩
        · exact clearZero_exists represented present zero
        · exact clearBag_exists represented present empty
        · exact heat_exists represented present bag
      obtain ⟨value₁, represented₁, lighter⟩ := administration_decreases represented fires
      obtain ⟨s', value', run, represented', heated'⟩ :=
        earlier _ (hw ▸ lighter) represented₁ rfl
      exact ⟨s', value', .head fires run, represented', heated'⟩

/-! ## Completeness -/

/-- A closed value of spine zero is an input, an output or a drop of quoted code. -/
theorem flat_shape : ∀ (v : G [] .pr), spine v = 0 →
    (∃ c b, v = inputT c b) ∨ (∃ c p, v = outputT c p) ∨ ∃ p, v = dropqT p
  | .var v, _ => nomatch v
  | .op (.inl .zero) .nil, flat => absurd flat Nat.one_ne_zero
  | .op (.inl .bag) (.cons l .nil), flat => absurd flat (Nat.succ_ne_zero (spine l))
  | .op (.inl .input) (.cons c (.cons b .nil)), _ => .inl ⟨c, b, rfl⟩
  | .op (.inl .output) (.cons c (.cons p .nil)), _ => .inr (.inl ⟨c, p, rfl⟩)
  | .op (.inl .dropq) (.cons p .nil), _ => .inr (.inr ⟨p, rfl⟩)
  | .op (.inr o) _, _ => o.key.elim

theorem canonical_dropqT (p : G [] .pr) :
    ∃ name, canonicalize (read (dropqT p)) = .apply "PDrop" [name] := by
  show ∃ name, canonicalize (.apply "PDrop" [.apply "NQuote" [read p]]) = _
  rw [Canonical.canonicalize_apply_general "PDrop" _ (by simp)]
  exact ⟨_, rfl⟩

theorem prime_value {v : G [] .pr} (closed : Closed v) (flat : spine v = 0) :
    IsPrime (canonicalize (read v)) := by
  obtain ⟨typed, canonical⟩ := canonical_row v closed
  refine ⟨typed, canonical, ?_, ?_⟩
  · rcases flat_shape v flat with ⟨c, b, rfl⟩ | ⟨c, p, rfl⟩ | ⟨p, rfl⟩
    · rw [canonical_inputT]
      simp [input]
    · rw [canonical_outputT]
      simp [output]
    · obtain ⟨name, same⟩ := canonical_dropqT p
      rw [same]
      simp
  · intro elements
    rcases flat_shape v flat with ⟨c, b, rfl⟩ | ⟨c, p, rfl⟩ | ⟨p, rfl⟩
    · rw [canonical_inputT]
      simp [input]
    · rw [canonical_outputT]
      simp [output]
    · obtain ⟨name, same⟩ := canonical_dropqT p
      rw [same]
      simp

/-- On a heated state, the inventory is the canonical forms of the values. -/
theorem inventory_heated {present : Finset ℕ} {value : ℕ → G [] .pr}
    (closed : ∀ o ∈ present, Closed (value o)) (heated : ∀ o ∈ present, spine (value o) = 0) :
    inventoryOf present value = present.val.map fun o => canonicalize (read (value o)) := by
  unfold inventoryOf
  rw [Finset.sum_congr rfl fun o member =>
      primes_of_canonical_prime rfl (prime_value (closed o member) (heated o member)),
    Finset.sum_eq_multiset_sum,
    show (fun o => ({canonicalize (read (value o))} : Multiset Pattern)) =
      (fun pattern : Pattern => ({pattern} : Multiset Pattern)) ∘
        (fun o => canonicalize (read (value o))) from rfl,
    ← Multiset.map_map, Multiset.sum_map_singleton]

/-- A heated value whose canonical read-back is an input is an input term. -/
theorem input_value {v : G [] .pr} (flat : spine v = 0) {C B : Pattern}
    (shape : canonicalize (read v) = input C B) :
    ∃ c b, v = inputT c b ∧ canonicalize (read c) = C ∧ canonicalize (read b) = B := by
  rcases flat_shape v flat with ⟨c, b, rfl⟩ | ⟨c, p, rfl⟩ | ⟨p, rfl⟩
  · rw [canonical_inputT] at shape
    simp only [input, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and,
      and_true] at shape
    exact ⟨c, b, rfl, shape.1, shape.2⟩
  · rw [canonical_outputT] at shape
    simp [input, output] at shape
  · obtain ⟨name, same⟩ := canonical_dropqT p
    rw [same] at shape
    simp [input] at shape

/-- A heated value whose canonical read-back is an output is an output term. -/
theorem output_value {v : G [] .pr} (flat : spine v = 0) {C Q : Pattern}
    (shape : canonicalize (read v) = output C Q) :
    ∃ c q, v = outputT c q ∧ canonicalize (read c) = C ∧ canonicalize (read q) = Q := by
  rcases flat_shape v flat with ⟨c, b, rfl⟩ | ⟨c, p, rfl⟩ | ⟨p, rfl⟩
  · rw [canonical_inputT] at shape
    simp [input, output] at shape
  · rw [canonical_outputT] at shape
    simp only [output, Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at shape
    exact ⟨c, p, rfl, shape.1, shape.2⟩
  · obtain ⟨name, same⟩ := canonical_dropqT p
    rw [same] at shape
    simp [output] at shape

/-- **Every source reduction is matched**: housekeeping firings, then one communication. -/
theorem communication_complete {s : State} {P P' : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (step : rhoLanguageDefGSLT.Step P P') :
    ∃ (s₁ s₂ : State) (value₂ : ℕ → G [] .pr), Relation.ReflTransGen Administers s s₁ ∧
      Communicates s₁ s₂ ∧ RepresentsBy s₂ P' value₂ := by
  classical
  obtain ⟨s₁, value₁, run, represented₁, heated⟩ := heats_to_primes represented
  obtain ⟨rule, rest, source, target⟩ := (publicStep_iff P P').mp step
  let meaning : ℕ → Pattern := fun o => canonicalize (read (value₁ o))
  have rows : s₁.present.val.map meaning =
      input rule.inputChannel rule.body ::ₘ output rule.outputChannel rule.payload ::ₘ rest.1 := by
    rw [← inventory_heated represented₁.closed heated, represented₁.inventory_eq, source,
      redex_append]
  obtain ⟨o₁, member₁, at₁⟩ : ∃ o₁ ∈ s₁.present, meaning o₁ = input rule.inputChannel rule.body := by
    have found : input rule.inputChannel rule.body ∈ s₁.present.val.map meaning := by
      rw [rows]; exact Multiset.mem_cons_self _ _
    obtain ⟨o₁, member, same⟩ := Multiset.mem_map.mp found
    exact ⟨o₁, member, same⟩
  obtain ⟨o₂, member₂, distinct, at₂⟩ : ∃ o₂ ∈ s₁.present, o₂ ≠ o₁ ∧
      meaning o₂ = output rule.outputChannel rule.payload := by
    have split : s₁.present.val.map meaning =
        meaning o₁ ::ₘ (s₁.present.erase o₁).val.map meaning := by
      rw [← Multiset.map_cons meaning o₁,
        ← Finset.insert_val_of_notMem (Finset.notMem_erase o₁ s₁.present),
        Finset.insert_erase member₁]
    rw [split, at₁] at rows
    have others := Multiset.cons_inj_right _ |>.mp rows
    have found : output rule.outputChannel rule.payload ∈
        (s₁.present.erase o₁).val.map meaning := by
      rw [others]; exact Multiset.mem_cons_self _ _
    obtain ⟨o₂, member, same⟩ := Multiset.mem_map.mp found
    have inErase := Finset.mem_erase.mp member
    exact ⟨o₂, inErase.2, inErase.1, same⟩
  obtain ⟨c₁, b₁, shape₁, channel₁, body₁⟩ := input_value (heated o₁ member₁) at₁
  obtain ⟨c₂, q₂, shape₂, channel₂, payload₂⟩ := output_value (heated o₂ member₂) at₂
  have closed₁ := represented₁.closed o₁ member₁
  have closed₂ := represented₁.closed o₂ member₂
  rw [shape₁] at closed₁
  rw [shape₂] at closed₂
  have closedChannel₁ : Closed c₁ := by
    have unfolded : binderSafeAt "NQuote" 0
        (.apply "PInput" [read c₁, .lambda none (read b₁)]) = true := closed₁
    simp only [binderSafeAt, binderSafeListAt, Bool.and_eq_true] at unfolded
    exact unfolded.1
  have closedChannel₂ : Closed c₂ := by
    have unfolded : binderSafeAt "NQuote" 0 (.apply "POutput" [read c₂, read q₂]) = true := closed₂
    simp only [binderSafeAt, binderSafeListAt, Bool.and_eq_true] at unfolded
    exact unfolded.1
  have canonicalChannels : canonicalize (read c₁) = canonicalize (read c₂) := by
    rw [channel₁, channel₂]
    have equal := rule.channels
    rwa [Canonical.canonicalize_eq_of_isCanonical rule.inputPrime.2.1.1,
      Canonical.canonicalize_eq_of_isCanonical rule.outputPrime.2.1.1] at equal
  have channels : Similar c₁ c₂ := .name closedChannel₁ closedChannel₂
    (StructuralCongruence.trans _ _ _ (Canonical.canonicalize_sound _)
      (canonicalChannels ▸ StructuralCongruence.symm _ _ (Canonical.canonicalize_sound _)))
  obtain ⟨f, isComm, admitted, taken⟩ :=
    comm_exists represented₁ member₁ member₂ distinct.symm shape₁ shape₂ channels
  obtain ⟨o₁', o₂', rule', value₂, taken', at₁', at₂', source', target'⟩ :=
    comm_effect represented₁ f isComm admitted
  have pair : o₁' = o₁ ∧ o₂' = o₂ := by
    have same : [o₁', o₂'] = [o₁, o₂] := taken'.symm.trans taken
    simpa using same
  obtain ⟨rfl, rfl⟩ := pair
  have inputSame := at₁'.symm.trans at₁
  have outputSame := at₂'.symm.trans at₂
  simp only [input, output, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq,
    true_and, and_true] at inputSame outputSame
  have redexSame : rule'.redex.1 = rule.redex.1 := by
    simp only [GroundComm.redex, inputSame.1, inputSame.2, outputSame.1, outputSame.2]
  have reactumSame : rule'.reactum.1 = rule.reactum.1 := by
    simp only [GroundComm.reactum, GroundComm.result, ← primes_process, inputSame.2,
      outputSame.2]
  have restSame : inventoryOf (s₁.present \ {o₁', o₂'}) value₁ = rest.1 := by
    have both : rule'.redex.1 + inventoryOf (s₁.present \ {o₁', o₂'}) value₁ =
        rule.redex.1 + rest.1 := by
      rw [← source', source]
      rfl
    rw [redexSame] at both
    exact add_left_cancel both
  refine ⟨s₁, _, value₂, run, ⟨f, isComm, admitted, rfl⟩, target' P' ?_⟩
  rw [target, append_inventory, reactumSame, restSame]

/-! ## The theorem -/

/-- The initial state of a closed process: one row, its representation, no unknowns. -/
abbrev initialState (t : G [] .pr) : State :=
  ⟨groundFrame, [], {0}, fun _ => ⟨[], .pr, t⟩⟩

theorem initial_represents (P : RhoProcess) {t : G [] .pr} (same : read t = P.1) :
    RepresentsBy (initialState t) P (fun _ => t) := by
  refine ⟨⟨(fun e => nomatch e : Grounding groundFrame), fun _ inside => nomatch inside⟩, ?_, ?_,
    ?_⟩
  · intro g _ o _
    refine ⟨t, ?_, similar_refl t⟩
    show (⟨[], .pr, instantiate g t⟩ : Observation sig noUnknowns) = ⟨[], .pr, t⟩
    rw [instantiate_ground]
  · intro _ _
    exact represent_closed_safe same
  · unfold inventoryOf
    simp only [Finset.sum_singleton]
    rw [same]
    rfl

theorem every_process_represented (P : RhoProcess) : ∃ s, Represents s P := by
  obtain ⟨t, same⟩ := represent_closed P
  exact ⟨initialState t, _, initial_represents P same⟩

/-- **The reflective higher-order calculus on the step of a program, by ordinary instantiation,
for all closed processes.**

The step is `RuleSyntax.step` of the fixed four-rule `program`; its communication rule makes
`K⟨@Q, Q⟩`, so the made row is the continuation instantiated at the received name and process.
Through `Represents`:

1. every closed process is represented;
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented process;
4. a communication is a source reduction (no extra behaviour);
5. every source reduction is matched by housekeeping firings and one communication;
6. a run of `k` housekeeping firings from a state represented through `value` has `k` at most the
   spine weight of its rows. -/
theorem reflective_calculus_by_instantiation :
    (∀ P : RhoProcess, ∃ s, Represents s P) ∧
    (∀ s s' : State,
      LogicOverTheStep.StepSpan.Succ theStep.toStep s s' ↔ Communicates s s' ∨ Administers s s') ∧
    (∀ {s s' : State} {P : RhoProcess}, Represents s P → Administers s s' → Represents s' P) ∧
    (∀ {s s' : State} {P : RhoProcess}, Represents s P → Communicates s s' →
      ∃ P', rhoLanguageDefGSLT.Step P P' ∧ Represents s' P') ∧
    (∀ {s : State} {P P' : RhoProcess}, Represents s P → rhoLanguageDefGSLT.Step P P' →
      ∃ s₁ s₂, Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧ Represents s₂ P') ∧
    (∀ {s e : State} {P : RhoProcess} {value : ℕ → G [] .pr} {k : ℕ},
      RepresentsBy s P value → AdministrativeRun k s e → k ≤ weightOf s.present value) := by
  refine ⟨every_process_represented, succ_iff, ?_, ?_, ?_,
    fun represented run => administration_bounded represented run⟩
  · intro s s' P represented fires
    obtain ⟨value, represented⟩ := represented
    obtain ⟨value', represented', _⟩ := administration_decreases represented fires
    exact ⟨value', represented'⟩
  · intro s s' P represented fires
    obtain ⟨value, represented⟩ := represented
    obtain ⟨P', value', step, represented'⟩ := communication_sound represented fires
    exact ⟨P', step, value', represented'⟩
  · intro s P P' represented step
    obtain ⟨value, represented⟩ := represented
    obtain ⟨s₁, s₂, value₂, run, fires, represented₂⟩ := communication_complete represented step
    exact ⟨s₁, s₂, run, fires, value₂, represented₂⟩

#print axioms succ_iff
#print axioms administration_bounded
#print axioms communication_sound
#print axioms heats_to_primes
#print axioms communication_complete
#print axioms reflective_calculus_by_instantiation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
