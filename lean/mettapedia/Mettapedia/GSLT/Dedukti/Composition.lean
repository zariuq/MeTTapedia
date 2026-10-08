import Mettapedia.GSLT.Dedukti.Phenomena
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation

/-!
# Composing translations and gluing theories

## Composition

Maps of theories compose, and hosting composes (existing
`ContextMap.comp`, `ContextMap.Hosting.comp`).  Interpretations of constants
compose with both of their obligations (`Interpretation.Respects.comp`,
`Interpretation.Typed.comp`).  One composite is computed here: the
Cousineau–Dowek embedding followed by its back translation is the erasure of
the annotations, up to beta (`embedding_then_back`), and it is hosting
(`embedding_then_back_hosting`).

## Gluing along shared declarations

Two modules that declare rewrite rules over shared constants are joined as
sets of declarations by the existing `ModuleAlgebra.join`, which exists
exactly when the declarations are compatible: a shared origin has one body
and one label names one origin.  That is a statement about declarations.
Three further conditions are needed before the joined theory has what the
parts had, and each is witnessed.

* **Rules.**  The two modules `c ⟶ a` and `c ⟶ b` are compatible and their
  join exists (`choiceModules_join`).  Each is confluent at `c`
  (`leftModule_confluentAt`, `rightModule_confluentAt`); the join is not
  (`joined_not_confluentAt`).  The two modules `f ⟶ g` and `g ⟶ f` are
  compatible; each terminates at `f` (`forth_terminates`, `back_terminates`);
  the join does not (`loop_not_terminates`).  Confluence and termination of
  a join are properties of the union of the rules.
* **Substitution.**  A map on constants extends to a map of theories only if
  its images are closed.  An image with a free variable does not commute with
  substitution (`openImage_breaks_substitution`) and sends a conversion to
  two terms with no common reduct (`openImage_breaks_conversion`).
* **The chosen observations.**  The inclusion of a theory into its extension
  by a choice symbol is hosting on the terms without the symbol
  (`includeAvoiding_hosting`) and is not hosting on all terms
  (`includeAll_not_hosting`).  Whether a join hosts a part depends on which
  terms and contexts the part is taken to have.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Composition

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra (Entry Presentation)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Composition -/

/-- The embedding of a pure type system followed by the back translation. -/
def embeddingThenBack {profile : Profile} (respects : RespectsErasure profile) :
    ContextMap (rawTheory profile) (conversionTheory Theory.empty) :=
  (back.contextMap (back_respects profile)).comp (cdRawMap respects)

/-- **The composite is the erasure of the annotations**, up to beta. -/
theorem embedding_then_back {profile : Profile} (respects : RespectsErasure profile)
    (term : ValidTerm profile) :
    Conv Theory.empty ((embeddingThenBack respects).term (origin := ()) term) term.1.erase :=
  backTranslate_translate term.1

/-- **The composite is hosting.** -/
theorem embedding_then_back_hosting {profile : Profile} (respects : RespectsErasure profile) :
    (embeddingThenBack respects).Hosting := by
  rw [ContextMap.hosting_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro _ first second convertible
    exact .trans _ _ _ (.symm _ _ (embedding_then_back respects first))
      (.trans _ _ _ convertible (embedding_then_back respects second))
  · intro _ _ _ _ _ step
    exact step.elim
  · intro _ _ _ _ _ step
    exact step.elim

/-! ## Gluing: the rules -/

/-- A theory whose rules rewrite constants to constants: `holds c d` declares
`c ⟶ d`. -/
def constantRules (holds : String → String → Prop) : Theory where
  constType := fun _ => none
  body := fun _ => none
  rule := fun rule => ∃ source target, holds source target ∧ rule = ⟨.con source, .con target⟩

theorem constantRules_headed (holds : String → String → Prop) : (constantRules holds).Headed := by
  rintro rule ⟨source, target, _, rfl⟩
  exact ⟨source, rfl⟩

/-- The steps of a constant. -/
theorem constantRules_step {holds : String → String → Prop} {name : String} {next : Term}
    (step : Step (constantRules holds) (.con name) next) :
    ∃ target, holds name target ∧ next = .con target := by
  rcases step.con_inv.con_inv with defined | ⟨rule, assignment, ⟨source, target, declared, rfl⟩,
    same, rfl⟩
  · cases defined
  · have equal : source = name := Term.con.inj same
    exact ⟨target, equal ▸ declared, rfl⟩

/-- A declaration of a rule between constants, as an entry of a module: its
origin, its label, and the two constants. -/
abbrev RuleEntry : Type := Entry String String (String × String)

/-- The rules that a set of entries declares. -/
def declared (entries : Finset RuleEntry) (source target : String) : Prop :=
  ∃ entry ∈ entries, entry.body = (source, target)

/-- The theory of a set of entries. -/
def moduleTheory (entries : Finset RuleEntry) : Theory := constantRules (declared entries)

/-- Confluence at one term. -/
def ConfluentAt (theory : Theory) (term : Term) : Prop :=
  ∀ left right, Reduces theory term left → Reduces theory term right → Joinable theory left right

def leftEntry : RuleEntry := ⟨"left.choice", "choose_a", ("c", "a")⟩

def rightEntry : RuleEntry := ⟨"right.choice", "choose_b", ("c", "b")⟩

theorem singleton_valid (entry : RuleEntry) : ModuleAlgebra.Valid ({entry} : Finset RuleEntry) := by
  intro first firstMember second secondMember _
  rw [Finset.mem_singleton.mp firstMember, Finset.mem_singleton.mp secondMember]

/-- The module that declares `c ⟶ a`. -/
def leftModule : Presentation String String (String × String) := ⟨{leftEntry}, singleton_valid _⟩

/-- The module that declares `c ⟶ b`. -/
def rightModule : Presentation String String (String × String) := ⟨{rightEntry}, singleton_valid _⟩

/-- **The two modules are compatible as declarations, and their join
exists.** -/
theorem choiceModules_join :
    ∃ joined, ModuleAlgebra.join leftModule rightModule = some joined ∧
      joined.val = {leftEntry, rightEntry} := by
  have compatible : ModuleAlgebra.Compatible leftModule.val rightModule.val := by
    intro first firstMember second secondMember overlap
    have firstSame := Finset.mem_singleton.mp firstMember
    have secondSame := Finset.mem_singleton.mp secondMember
    subst firstSame
    subst secondSame
    exact absurd overlap (by decide)
  cases joined : ModuleAlgebra.join leftModule rightModule with
  | none => exact absurd compatible ((ModuleAlgebra.join_eq_none_iff _ _).mp joined)
  | some value =>
      refine ⟨value, rfl, ?_⟩
      have union := ModuleAlgebra.join_eq_some_iff.mp joined
      rw [← union]
      rfl

theorem declared_left {source target : String} :
    declared {leftEntry} source target ↔ source = "c" ∧ target = "a" := by
  constructor
  · rintro ⟨entry, member, same⟩
    rw [Finset.mem_singleton.mp member] at same
    cases same
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨leftEntry, Finset.mem_singleton_self _, rfl⟩

theorem declared_right {source target : String} :
    declared {rightEntry} source target ↔ source = "c" ∧ target = "b" := by
  constructor
  · rintro ⟨entry, member, same⟩
    rw [Finset.mem_singleton.mp member] at same
    cases same
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rightEntry, Finset.mem_singleton_self _, rfl⟩

/-- A module with the one rule `c ⟶ d`, for `d` other than `c`, is confluent
at `c`. -/
theorem confluentAt_of_one_rule {holds : String → String → Prop} {origin result : String}
    (only : ∀ source target, holds source target ↔ source = origin ∧ target = result)
    (distinct : result ≠ origin) : ConfluentAt (constantRules holds) (.con origin) := by
  have step : Step (constantRules holds) (.con origin) (.con result) :=
    Step.root (.rule (theory := constantRules holds) (rule := ⟨.con origin, .con result⟩)
      (fun _ => .srt .type) ⟨origin, result, (only _ _).mpr ⟨rfl, rfl⟩, rfl⟩)
  have reducts : ∀ {final : Term}, Reduces (constantRules holds) (.con origin) final →
      final = .con origin ∨ final = .con result := by
    intro final reduces
    induction reduces with
    | refl => exact Or.inl rfl
    | tail _ last ih =>
        rcases ih with rfl | rfl
        · obtain ⟨target, isRule, rfl⟩ := constantRules_step last
          exact Or.inr (congrArg Term.con ((only _ _).mp isRule).2)
        · obtain ⟨target, isRule, rfl⟩ := constantRules_step last
          exact absurd ((only _ _).mp isRule).1 distinct
  intro left right leftReduces rightReduces
  rcases reducts leftReduces with rfl | rfl <;> rcases reducts rightReduces with rfl | rfl
  · exact ⟨_, .refl, .refl⟩
  · exact ⟨_, .single step, .refl⟩
  · exact ⟨_, .refl, .single step⟩
  · exact ⟨_, .refl, .refl⟩

/-- **The first module is confluent at the shared constant.** -/
theorem leftModule_confluentAt : ConfluentAt (moduleTheory leftModule.val) (.con "c") :=
  confluentAt_of_one_rule (fun _ _ => declared_left) (by decide)

/-- **So is the second.** -/
theorem rightModule_confluentAt : ConfluentAt (moduleTheory rightModule.val) (.con "c") :=
  confluentAt_of_one_rule (fun _ _ => declared_right) (by decide)

/-- **Their join is not**: the shared constant reduces to two normal
constants. -/
theorem joined_not_confluentAt :
    ¬ ConfluentAt (moduleTheory {leftEntry, rightEntry}) (.con "c") := by
  intro confluent
  have isDeclared : ∀ {source target : String},
      declared {leftEntry, rightEntry} source target → source = "c" := by
    rintro source target ⟨entry, member, same⟩
    rcases Finset.mem_insert.mp member with rfl | member
    · cases same
      rfl
    · rw [Finset.mem_singleton.mp member] at same
      cases same
      rfl
  have toA : Step (moduleTheory {leftEntry, rightEntry}) (.con "c") (.con "a") :=
    Step.root (.rule (theory := moduleTheory {leftEntry, rightEntry})
      (rule := ⟨.con "c", .con "a"⟩) (fun _ => .srt .type)
      ⟨"c", "a", ⟨leftEntry, by simp, rfl⟩, rfl⟩)
  have toB : Step (moduleTheory {leftEntry, rightEntry}) (.con "c") (.con "b") :=
    Step.root (.rule (theory := moduleTheory {leftEntry, rightEntry})
      (rule := ⟨.con "c", .con "b"⟩) (fun _ => .srt .type)
      ⟨"c", "b", ⟨rightEntry, by simp, rfl⟩, rfl⟩)
  have normal : ∀ name : String, name ≠ "c" →
      IsNormal (Step (moduleTheory {leftEntry, rightEntry})) (.con name) := by
    intro name distinct next step
    obtain ⟨_, isRule, _⟩ := constantRules_step step
    exact distinct (isDeclared isRule)
  exact not_joinable_of_normal (normal "a" (by decide)) (normal "b" (by decide)) (by decide)
    (confluent _ _ (.single toA) (.single toB))

/-! ### Termination -/

def forthEntry : RuleEntry := ⟨"forth.rule", "forth", ("f", "g")⟩

def backEntry : RuleEntry := ⟨"back.rule", "back", ("g", "f")⟩

theorem declared_forth {source target : String} :
    declared {forthEntry} source target ↔ source = "f" ∧ target = "g" := by
  constructor
  · rintro ⟨entry, member, same⟩
    rw [Finset.mem_singleton.mp member] at same
    cases same
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨forthEntry, Finset.mem_singleton_self _, rfl⟩

theorem declared_back {source target : String} :
    declared {backEntry} source target ↔ source = "g" ∧ target = "f" := by
  constructor
  · rintro ⟨entry, member, same⟩
    rw [Finset.mem_singleton.mp member] at same
    cases same
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨backEntry, Finset.mem_singleton_self _, rfl⟩

/-- A module with the one rule `c ⟶ d`, for `d` other than `c`, terminates at
every constant. -/
theorem terminates_of_one_rule {holds : String → String → Prop} {origin result : String}
    (only : ∀ source target, holds source target ↔ source = origin ∧ target = result)
    (distinct : result ≠ origin) (name : String) :
    Acc (fun next term => Step (constantRules holds) term next) (.con name) := by
  have resultNormal : Acc (fun next term => Step (constantRules holds) term next)
      (.con result) := by
    refine ⟨_, fun next step => ?_⟩
    obtain ⟨_, isRule, _⟩ := constantRules_step step
    exact absurd ((only _ _).mp isRule).1 distinct
  refine ⟨_, fun next step => ?_⟩
  obtain ⟨target, isRule, rfl⟩ := constantRules_step step
  rw [((only _ _).mp isRule).2]
  exact resultNormal

/-- **The module `f ⟶ g` terminates at `f`.** -/
theorem forth_terminates :
    Acc (fun next term => Step (moduleTheory {forthEntry}) term next) (.con "f") :=
  terminates_of_one_rule (fun _ _ => declared_forth) (by decide) "f"

/-- **The module `g ⟶ f` terminates at `f`.** -/
theorem back_terminates :
    Acc (fun next term => Step (moduleTheory {backEntry}) term next) (.con "f") :=
  terminates_of_one_rule (fun _ _ => declared_back) (by decide) "f"

/-- **Their join does not**: `f ⟶ g ⟶ f`. -/
theorem loop_not_terminates :
    ¬ Acc (fun next term => Step (moduleTheory {forthEntry, backEntry}) term next) (.con "f") := by
  intro terminates
  have forth : Step (moduleTheory {forthEntry, backEntry}) (.con "f") (.con "g") :=
    Step.root (.rule (theory := moduleTheory {forthEntry, backEntry})
      (rule := ⟨.con "f", .con "g"⟩) (fun _ => .srt .type)
      ⟨"f", "g", ⟨forthEntry, by simp, rfl⟩, rfl⟩)
  have backward : Step (moduleTheory {forthEntry, backEntry}) (.con "g") (.con "f") :=
    Step.root (.rule (theory := moduleTheory {forthEntry, backEntry})
      (rule := ⟨.con "g", .con "f"⟩) (fun _ => .srt .type)
      ⟨"g", "f", ⟨backEntry, by simp, rfl⟩, rfl⟩)
  have cycle : Relation.TransGen (Step (moduleTheory {forthEntry, backEntry})) (.con "f") (.con "f") :=
    .tail (.single forth) backward
  exact not_rel_self_of_acc (acc_transGen terminates) (Relation.transGen_swap.mpr cycle)

/-! ## Gluing: substitution -/

/-- A map on constants whose image has a free variable. -/
def openImage : String → Term := fun _ => .var 0

/-- **An open image does not commute with substitution.** -/
theorem openImage_breaks_substitution :
    interpret openImage (subst0 (.srt .kind) (.con "c")) ≠
      subst0 (interpret openImage (.srt .kind)) (interpret openImage (.con "c")) := by
  decide

/-- The redex `(λ x : Type. c) Kind`, which reduces to `c`. -/
def constantRedex : Term := .app (.lam (.srt .type) (.con "c")) (.srt .kind)

theorem constantRedex_conv : Conv Theory.empty constantRedex (.con "c") :=
  Conv.beta (.srt .type) (.con "c") (.srt .kind)

/-- A root contraction of the theory with no rule is beta. -/
theorem rootStep_empty_inv {source target : Term} (step : RootStep Theory.empty source target) :
    ∃ domain body argument, source = .app (.lam domain body) argument ∧
      target = subst0 argument body := by
  cases step with
  | beta domain body argument => exact ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => cases defined
  | rule assignment member => exact member.elim

/-- Every reduct of the image of the redex. -/
theorem openImage_reducts {final : Term}
    (reduces : Reduces Theory.empty (interpret openImage constantRedex) final) :
    final = interpret openImage constantRedex ∨ final = .srt .kind := by
  induction reduces with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
      rcases ih with rfl | rfl
      · rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
        · obtain ⟨domain, body, argument, same, rfl⟩ := rootStep_empty_inv root
          have shape : Term.app (.lam (.srt .type) (.var 0)) (.srt .kind) =
              .app (.lam domain body) argument := same
          cases shape
          exact Or.inr rfl
        · rcases inner.lam_inv with root | ⟨_, deeper, _⟩ | ⟨_, deeper, _⟩
          · exact (RootStep.not_lam Theory.empty_headed root).elim
          · exact (srt_normal Theory.empty_headed _ _ deeper).elim
          · exact (var_normal Theory.empty_headed _ _ deeper).elim
        · exact (srt_normal Theory.empty_headed _ _ inner).elim
      · exact (srt_normal Theory.empty_headed _ _ step).elim

/-- **An open image does not preserve conversion**: the redex is convertible
to the constant, and their images have no common reduct. -/
theorem openImage_breaks_conversion :
    ¬ Joinable Theory.empty (interpret openImage constantRedex) (interpret openImage (.con "c")) := by
  rintro ⟨common, leftReduces, rightReduces⟩
  have right : common = .var 0 := (var_normal Theory.empty_headed 0).reflTransGen_eq rightReduces
  rcases openImage_reducts leftReduces with left | left
  · rw [left] at right
    cases right
  · rw [left] at right
    cases right

/-! ## Gluing: the chosen observations -/

/-- The inclusion of a theory into its extension by choice, on all terms. -/
def includeAll (theory : Theory) :
    ContextMap (rewritingTheory theory) (rewritingTheory (withChoice theory)) where
  interface := fun _ => ()
  term := fun term => term
  context := fun context => context
  term_resp := fun same => same
  equivariant := fun _ _ => rfl

/-- A choice between two sorts has no step in a theory that does not define
the choice symbol. -/
theorem choose_normal {theory : Theory} (headed : theory.Headed)
    (rigid : ¬ theory.Defines chooseName) :
    IsNormal (Step theory) (choose (.srt .type) (.srt .kind)) := by
  intro next step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_of_rigid headed rigid rfl root
  · rcases inner.app_inv with root | ⟨_, deeper, _⟩ | ⟨_, deeper, _⟩
    · exact RootStep.not_of_rigid headed rigid rfl root
    · exact RootStep.not_of_rigid headed rigid rfl deeper.con_inv
    · exact srt_normal headed _ _ deeper
  · exact srt_normal headed _ _ inner

/-- **On all terms the inclusion is not hosting**: the extension gives a step
to a term of the theory that had none. -/
theorem includeAll_not_hosting {theory : Theory} (headed : theory.Headed)
    (rigid : ¬ theory.Defines chooseName) : ¬ (includeAll theory).Hosting := by
  intro hosting
  have reflects : (includeAll theory).ReflectsRewrites :=
    (includeAll theory).reflectsRewrites_of_transitions hosting.reflects
  obtain ⟨next, step, _⟩ := reflects (interface := ()) (term := choose (.srt .type) (.srt .kind))
    (step_choose_left theory _ _)
  exact choose_normal headed rigid next step

#print axioms embedding_then_back_hosting
#print axioms choiceModules_join
#print axioms leftModule_confluentAt
#print axioms joined_not_confluentAt
#print axioms forth_terminates
#print axioms loop_not_terminates
#print axioms openImage_breaks_substitution
#print axioms openImage_breaks_conversion
#print axioms includeAll_not_hosting

end Mettapedia.GSLT.Dedukti.Composition
