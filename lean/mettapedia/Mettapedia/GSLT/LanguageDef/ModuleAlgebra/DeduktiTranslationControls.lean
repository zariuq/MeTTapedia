import Mettapedia.OSLF.MeTTaIL.NoncontextualPremiseCheck
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiModuleInterpretations
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.Dedukti.LeanMinusConversion
import Mettapedia.GSLT.Dedukti.LanguageDefExamples
import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution

/-!
# Modular translation controls on actual lambda-Pi terms

Two modules share a carrier and an imported function. Their independently
checked assignments join into a typing- and conversion-preserving translation.
Two source rewrites fuse to one target beta contraction. A separate control
uses the transcribed universe-polymorphism theory to show that forward
preservation does not imply reflection.

The upstream and sentence-style quotations below author the same operational
interface. Their interpretation is checked after quotation; no byte parser,
native certificate checker, or general inverse to the Lean encoding is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiTranslationControls

open Mettapedia.GSLT
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl lookupBody)
open ClosedTermGluing
open DeduktiModuleInterpretations (inventory namedMember)

def carrier : LF.Term := .con "Carrier"
def arrow : LF.Term := .pi carrier carrier
def midRule : Dedukti.RewriteRule := ⟨.app (.con "mid") (.var 0), .var 0⟩
def aliasRule : Dedukti.RewriteRule := ⟨.app (.con "alias") (.var 0), .app (.con "mid") (.var 0)⟩

def leftSig : Sig := [.const "Carrier" (.srt .type), .const "seed" carrier, .const "mid" arrow]
def rightSig : Sig := [.const "Carrier" (.srt .type), .const "mid" arrow, .const "alias" arrow]
def sourceSig : Sig :=
  [.const "Carrier" (.srt .type), .const "seed" carrier, .const "mid" arrow, .const "alias" arrow]

def leftTheory : Theory := Theory.ofSig leftSig [midRule]
def rightTheory : Theory := Theory.ofSig rightSig [aliasRule]
def source : Theory := Theory.ofSig sourceSig [midRule, aliasRule]
def target : Theory := Theory.ofSig [.const "T" (.srt .type), .const "z" (.con "T")] []

def leftNames : Finset String := {"Carrier", "seed", "mid"}
def rightNames : Finset String := {"Carrier", "mid", "alias"}
def left := inventory leftNames
def right := inventory rightNames
def whole := inventory (leftNames ∪ rightNames)

theorem joined : join left right = some whole := DeduktiModuleInterpretations.inventory_join _ _

def identityTerm : LF.Term := .lam (.con "T") (.var 0)

def leftValue (name : String) : ClosedTerm :=
  if name = "Carrier" then ⟨.con "T", .con⟩
  else if name = "seed" then ⟨.con "z", .con⟩
  else ⟨identityTerm, .lam .con (.var (by omega))⟩

def rightValue (name : String) : ClosedTerm :=
  if name = "Carrier" then ⟨.con "T", .con⟩
  else ⟨identityTerm, .lam .con (.var (by omega))⟩

def leftAssignment : Assignment left := fun entry => leftValue entry.val.label
def rightAssignment : Assignment right := fun entry => rightValue entry.val.label

theorem compatible : ∀ entry hp hq,
    leftAssignment ⟨entry, hp⟩ = rightAssignment ⟨entry, hq⟩ := by
  intro entry hp hq
  obtain ⟨name, nameLeft, rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨other, nameRight, same⟩ := Finset.mem_map.mp hq
  have equal : other = name := DeduktiModuleInterpretations.nameEmbedding.injective same
  subst other
  have shared : name ∈ ({"Carrier", "mid"} : Finset String) := by
    have both := Finset.mem_inter.mpr ⟨nameLeft, nameRight⟩
    have overlap : leftNames ∩ rightNames = {"Carrier", "mid"} := by decide
    exact overlap ▸ both
  simp only [Finset.mem_insert, Finset.mem_singleton] at shared
  rcases shared with rfl | rfl <;> rfl

noncomputable def translation : Interpretation :=
  interpretation whole (glueDependent joined leftAssignment rightAssignment)

theorem on_left (entry : Member left) :
    translation.meaning entry.val.label = (leftAssignment entry).val :=
  (glued_meaning_left joined leftAssignment rightAssignment entry).trans
    (interpretation_meaning left leftAssignment entry)

theorem on_right (entry : Member right) :
    translation.meaning entry.val.label = (rightAssignment entry).val :=
  (glued_meaning_right joined leftAssignment rightAssignment compatible entry).trans
    (interpretation_meaning right rightAssignment entry)

private theorem left_support_carrier : Supported left carrier :=
  .con (namedMember "Carrier" (by decide))

private theorem right_support_carrier : Supported right carrier :=
  .con (namedMember "Carrier" (by decide))

private theorem left_apply_carrier : (interpretation left leftAssignment).apply carrier = .con "T" :=
  (interpretation_meaning left leftAssignment (namedMember "Carrier" (by decide))).trans rfl

private theorem right_apply_carrier : (interpretation right rightAssignment).apply carrier = .con "T" :=
  (interpretation_meaning right rightAssignment (namedMember "Carrier" (by decide))).trans rfl

theorem target_closedBodies : target.ClosedBodies := by
  intro name term defined
  simp [target, Theory.ofSig, lookupBody] at defined

theorem target_closedTypes : target.ClosedTypes := by
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> constructor
  · simp at member

theorem target_identity_typed :
    HasType LFProfile.standardLF target [] identityTerm (.pi (.con "T") (.con "T")) := by
  exact .lam (resultSort := .type) (.con rfl) (.con rfl) (by decide) (.var rfl)

private theorem left_closedTypes : leftTheory.ClosedTypes := by
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [leftSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact .srt
    · exact .con
    · exact .pi .con .con
  · simp [leftSig] at member

private theorem right_closedTypes : rightTheory.ClosedTypes := by
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [rightSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact .srt
    · exact .pi .con .con
    · exact .pi .con .con
  · simp [rightSig] at member

theorem left_respects : translation.Respects leftTheory target := by
  apply respects_of_generators leftAssignment translation on_left
  · intro name body defined
    simp [leftTheory, Theory.ofSig, leftSig, lookupBody] at defined
  · intro rule member
    have equal : rule = midRule := List.mem_singleton.mp member
    subst rule
    refine ⟨.app (.con (namedMember "mid" (by decide))) (.var 0), .var 0, ?_⟩
    intro arguments
    have image := interpretation_meaning left leftAssignment (namedMember "mid" (by decide))
    change (interpretation left leftAssignment).meaning "mid" = identityTerm at image
    change Conv target (inst arguments (.app ((interpretation left leftAssignment).meaning "mid")
      (.var 0))) (inst arguments (.var 0))
    rw [image]
    simpa [identityTerm, inst, instantiate, lift_zero, LFTyping.subst0, LFTyping.subst] using
      (Conv.beta (theory := target) (.con "T") (.var 0) (arguments 0))

theorem right_respects : translation.Respects rightTheory target := by
  apply respects_of_generators rightAssignment translation on_right
  · intro name body defined
    simp [rightTheory, Theory.ofSig, rightSig, lookupBody] at defined
  · intro rule member
    have equal : rule = aliasRule := List.mem_singleton.mp member
    subst rule
    refine ⟨.app (.con (namedMember "alias" (by decide))) (.var 0),
      .app (.con (namedMember "mid" (by decide))) (.var 0), ?_⟩
    intro arguments
    have aliasImage := interpretation_meaning right rightAssignment (namedMember "alias" (by decide))
    have midImage := interpretation_meaning right rightAssignment (namedMember "mid" (by decide))
    change (interpretation right rightAssignment).meaning "alias" = identityTerm at aliasImage
    change (interpretation right rightAssignment).meaning "mid" = identityTerm at midImage
    change Conv target (inst arguments (.app ((interpretation right rightAssignment).meaning "alias")
      (.var 0))) (inst arguments (.app ((interpretation right rightAssignment).meaning "mid") (.var 0)))
    rw [aliasImage, midImage]
    exact .refl _

theorem left_typed : translation.Typed LFProfile.standardLF leftTheory target := by
  apply typed_of_generators leftAssignment translation on_left left_closedTypes
    target_closedBodies target_closedTypes
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [leftSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨namedMember "Carrier" (by decide), rfl, .sort .type, .con rfl⟩
    · refine ⟨namedMember "seed" (by decide), rfl, left_support_carrier, ?_⟩
      rw [left_apply_carrier]
      exact .con rfl
    · refine ⟨namedMember "mid" (by decide), rfl,
        .pi left_support_carrier left_support_carrier, ?_⟩
      change HasType LFProfile.standardLF target [] identityTerm
        (.pi ((interpretation left leftAssignment).apply carrier)
          ((interpretation left leftAssignment).apply carrier))
      rw [left_apply_carrier]
      exact target_identity_typed
  · simp [leftSig] at member

theorem right_typed : translation.Typed LFProfile.standardLF rightTheory target := by
  apply typed_of_generators rightAssignment translation on_right right_closedTypes
    target_closedBodies target_closedTypes
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [rightSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨namedMember "Carrier" (by decide), rfl, .sort .type, .con rfl⟩
    · refine ⟨namedMember "mid" (by decide), rfl,
        .pi right_support_carrier right_support_carrier, ?_⟩
      change HasType LFProfile.standardLF target [] identityTerm
        (.pi ((interpretation right rightAssignment).apply carrier)
          ((interpretation right rightAssignment).apply carrier))
      rw [right_apply_carrier]
      exact target_identity_typed
    · refine ⟨namedMember "alias" (by decide), rfl,
        .pi right_support_carrier right_support_carrier, ?_⟩
      change HasType LFProfile.standardLF target [] identityTerm
        (.pi ((interpretation right rightAssignment).apply carrier)
          ((interpretation right rightAssignment).apply carrier))
      rw [right_apply_carrier]
      exact target_identity_typed
  · simp [rightSig] at member

theorem source_respects : translation.Respects source target := by
  apply Interpretation.Respects.of_fragments [leftTheory, rightTheory]
  · intro name body defined
    simp [source, Theory.ofSig, sourceSig, lookupBody] at defined
  · intro rule member
    rcases List.mem_cons.mp member with first | last
    · exact ⟨leftTheory, by simp, List.mem_singleton.mpr first⟩
    · exact ⟨rightTheory, by simp, last⟩
  · intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact left_respects
    · exact right_respects

theorem source_typed : translation.Typed LFProfile.standardLF source target := by
  apply Interpretation.Typed.of_fragments [leftTheory, rightTheory]
  · intro name type declared
    rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
    · simp only [sourceSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨leftTheory, by simp, rfl⟩
      · exact ⟨leftTheory, by simp, rfl⟩
      · exact ⟨leftTheory, by simp, rfl⟩
      · exact ⟨rightTheory, by simp, rfl⟩
    · simp [sourceSig] at member
  · intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact left_typed
    · exact right_typed

/-- The actual joined interpretation preserves all source typing derivations,
including contexts and substitutions, rather than just its sample program. -/
theorem source_typing_preserved {context : LFTyping.Ctx} {term type : LF.Term}
    (typed : HasType LFProfile.standardLF source context term type) :
    HasType LFProfile.standardLF target (context.map translation.apply)
      (translation.apply term) (translation.apply type) :=
  source_respects.hasType source_typed typed

/-- Ordinary target theory growth retains the old proofs. It supplies no
reflection theorem and does not model a priority-changing rule extension. -/
theorem source_preserved_in_extension (larger : Theory) (extension : target.Extends larger)
    {context : LFTyping.Ctx} {term type : LF.Term}
    (typed : HasType LFProfile.standardLF source context term type) :
    HasType LFProfile.standardLF larger (context.map translation.apply)
      (translation.apply term) (translation.apply type) :=
  (source_respects.target_mono extension).hasType (source_typed.target_mono extension) typed

theorem source_signature_formed {name : String} {type : LF.Term}
    (declared : source.constType name = some type) :
    ∃ sort, HasType LFProfile.standardLF source [] type (.srt sort) := by
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [sourceSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨.kind, .sort rfl⟩
    · exact ⟨.type, .con rfl⟩
    · exact ⟨.type, .pi (.con rfl) (.con rfl) (by decide)⟩
    · exact ⟨.type, .pi (.con rfl) (.con rfl) (by decide)⟩
  · simp [sourceSig] at member

/-! ## Fusion is weaker than preservation of individual proof steps -/

theorem carrier_image : translation.meaning "Carrier" = .con "T" :=
  (on_left (namedMember "Carrier" (by decide))).trans rfl

theorem seed_image : translation.meaning "seed" = .con "z" :=
  (on_left (namedMember "seed" (by decide))).trans rfl

theorem mid_image : translation.meaning "mid" = identityTerm :=
  (on_left (namedMember "mid" (by decide))).trans rfl

theorem alias_image : translation.meaning "alias" = identityTerm :=
  (on_right (namedMember "alias" (by decide))).trans rfl

theorem source_alias_step (argument : LF.Term) :
    Step source (.app (.con "alias") argument) (.app (.con "mid") argument) := by
  have step := Step.root (RootStep.rule (theory := source) (rule := aliasRule)
    (fun _ => argument) (by simp [source, Theory.ofSig]))
  simpa [aliasRule, inst, instantiate, lift_zero] using step

theorem source_mid_step (argument : LF.Term) :
    Step source (.app (.con "mid") argument) argument := by
  have step := Step.root (RootStep.rule (theory := source) (rule := midRule)
    (fun _ => argument) (by simp [source, Theory.ofSig]))
  simpa [midRule, inst, instantiate, lift_zero] using step

theorem source_two_steps (argument : LF.Term) :
    Reduces source (.app (.con "alias") argument) argument :=
  (Relation.ReflTransGen.single (source_alias_step argument)).tail (source_mid_step argument)

theorem first_source_step_stutters (argument : LF.Term) :
    translation.apply (.app (.con "alias") argument) =
      translation.apply (.app (.con "mid") argument) := by
  change LF.Term.app (translation.meaning "alias") (translation.apply argument) =
    LF.Term.app (translation.meaning "mid") (translation.apply argument)
  rw [alias_image, mid_image]

theorem target_one_step (argument : LF.Term) :
    Step target (translation.apply (.app (.con "alias") argument)) (translation.apply argument) := by
  change Step target (.app (translation.meaning "alias") (translation.apply argument)) _
  rw [alias_image]
  exact Step.root (RootStep.beta (.con "T") (.var 0) (translation.apply argument))

theorem source_presents : Language.Presents source [midRule, aliasRule] where
  undefined := fun name => by simp [source, Theory.ofSig, sourceSig, lookupBody]
  rule_iff := fun _ => Iff.rfl
  leftAlgebraic := by
    intro rule member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  rightDetermined := by
    intro rule member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

theorem target_presents : Language.Presents target [] where
  undefined := fun name => by simp [target, Theory.ofSig, lookupBody]
  rule_iff := fun _ => Iff.rfl
  leftAlgebraic := fun _ impossible => by cases impossible
  rightDetermined := fun _ impossible => by cases impossible

/-- The same fusion is witnessed inside the existing full lambda-Pi
`LanguageDef` generation. It is not just a comparison of displayed syntax. -/
theorem generated_languages_fuse
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) (argument : LF.Term) :
    Relation.ReflTransGen
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
        (Language.dkLanguage ["Carrier", "seed", "mid", "alias"] [midRule, aliasRule]))
      (Language.encode (.app (.con "alias") argument)) (Language.encode argument) ∧
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base
      (Language.dkLanguage ["T", "z"] [])
      (Language.encode (translation.apply (.app (.con "alias") argument)))
      (Language.encode (translation.apply argument)) := by
  have first := (Language.step_encode_iff (base := base)
    (names := ["Carrier", "seed", "mid", "alias"]) source_presents).mpr
      ⟨_, rfl, source_alias_step argument⟩
  have second := (Language.step_encode_iff (base := base)
    (names := ["Carrier", "seed", "mid", "alias"]) source_presents).mpr
      ⟨_, rfl, source_mid_step argument⟩
  refine ⟨(Relation.ReflTransGen.single first).tail second, ?_⟩
  exact (Language.step_encode_iff (base := base) (names := ["T", "z"]) target_presents).mpr
    ⟨_, rfl, target_one_step argument⟩

/-- The full Dedukti language has recursive congruence premises. The existing
nonrecursive root-query realization cannot be assumed to cover this language. -/
theorem full_dedukti_is_not_nonrecursive :
    ¬ ∀ rule ∈ (Language.dkLanguage ["Carrier", "seed", "mid", "alias"] [midRule, aliasRule]).rewrites,
      Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rule.premises := by
  rw [← Mettapedia.OSLF.MeTTaIL.ContextualStep.check_noncontextualRules_iff]
  decide +kernel

/-- The joined substitution may mention names outside both source modules. -/
theorem foreign_arguments_preserved :
    Conv target (translation.apply (.app (.con "mid") (.con "foreign"))) (.con "foreign") := by
  have converted := source_respects.step (source_mid_step (.con "foreign"))
  have outside : ¬ ∃ entry : Member whole, entry.val.label = "foreign" := by
    rintro ⟨entry, named⟩
    obtain ⟨name, member, same⟩ := Finset.mem_map.mp entry.property
    have equal : name = "foreign" := (congrArg Entry.label same).trans named
    subst name
    have absent : ¬ "foreign" ∈ leftNames ∪ rightNames := by decide
    exact absent member
  have foreignImage : translation.apply (.con "foreign") = .con "foreign" :=
    interpretation_outside whole (glueDependent joined leftAssignment rightAssignment)
      "foreign" outside
  rw [foreignImage] at converted
  exact converted

/-! ## A nonidentity return route with actual constant typing -/

def renamedTarget : Theory := Theory.ofSig [.const "U" (.srt .type), .const "z" (.con "U")] []

def rename : Interpretation where
  meaning := fun name => .con (Equiv.swap "T" "U" name)
  closed := fun _ => .con

theorem rename_twice (term : LF.Term) : rename.apply (rename.apply term) = term := by
  induction term with
  | var _ => rfl
  | srt _ => rfl
  | con name => exact congrArg LF.Term.con (Equiv.swap_apply_self "T" "U" name)
  | pi domain body ihDomain ihBody => exact congrArg₂ LF.Term.pi ihDomain ihBody
  | lam domain body ihDomain ihBody => exact congrArg₂ LF.Term.lam ihDomain ihBody
  | app function argument ihFunction ihArgument => exact congrArg₂ LF.Term.app ihFunction ihArgument

theorem rename_respects : rename.Respects target renamedTarget where
  body := fun name body impossible => by simp [target, Theory.ofSig, lookupBody] at impossible
  rule := fun rule impossible => by cases impossible

theorem rename_back_respects : rename.Respects renamedTarget target where
  body := fun name body impossible => by simp [renamedTarget, Theory.ofSig, lookupBody] at impossible
  rule := fun rule impossible => by cases impossible

theorem rename_typed : rename.Typed LFProfile.standardLF target renamedTarget where
  constType := fun name type declared context => by
    rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
    · simp only [List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · have fixed : rename.meaning "z" = .con "z" := by decide
        rw [fixed]
        exact .con rfl
    · simp at member

theorem rename_back_typed : rename.Typed LFProfile.standardLF renamedTarget target where
  constType := fun name type declared context => by
    rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
    · simp only [List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · have fixed : rename.meaning "z" = .con "z" := by decide
        rw [fixed]
        exact .con rfl
    · simp at member

theorem rename_reflects_conversion {first second : LF.Term}
    (converted : Conv renamedTarget (rename.apply first) (rename.apply second)) :
    Conv target first second :=
  Interpretation.reflects_conversion_of_return rename_back_respects
    (fun term => Conv.of_eq (rename_twice term)) converted

theorem rename_context_reflects : (rename.contextMap rename_respects).ReflectsEquations :=
  Interpretation.contextMap_reflectsEquations_of_return rename_respects rename_back_respects
    (fun term => Conv.of_eq (rename_twice term))

theorem rename_returns_any_inhabitant {type proof : LF.Term} {sort : Srt}
    (formed : HasType LFProfile.standardLF target [] type (.srt sort))
    (typed : HasType LFProfile.standardLF renamedTarget [] proof (rename.apply type)) :
    ∃ sourceProof, HasType LFProfile.standardLF target [] sourceProof type :=
  Interpretation.inhabited_of_return rename_back_respects rename_back_typed formed
    (Conv.of_eq (rename_twice type)) typed

/-- The modular route composes with a separately checked target renaming. -/
theorem composed_typed :
    (rename.comp translation).Typed LFProfile.standardLF source renamedTarget :=
  rename_typed.comp rename_respects source_typed

theorem composed_respects : (rename.comp translation).Respects source renamedTarget :=
  rename_respects.comp source_respects

/-! ## Preserving proofs cannot certify an unsafe target conversion -/

theorem collapsed_forward : Interpretation.id.Respects Theory.empty LeanMinus.leanTheory where
  body := fun _ _ impossible => by cases impossible
  rule := fun _ impossible => impossible.elim

theorem empty_sorts_separate : ¬ Conv Theory.empty (.srt .type) (.srt .kind) :=
  not_conv_of_normal confluent_empty (srt_normal Theory.empty_headed .type)
    (srt_normal Theory.empty_headed .kind) (by decide)

theorem collapsed_target_does_not_reflect :
    ¬ (Interpretation.id.contextMap collapsed_forward).ReflectsEquations := by
  intro reflected
  have converted := LeanMinus.leanTheory_conv_all (.srt .type) (.srt .kind)
  exact empty_sorts_separate (reflected (origin := ()) converted)

theorem collapsed_target_is_not_hosting :
    ¬ (Interpretation.id.contextMap collapsed_forward).Hosting :=
  (Interpretation.id.contextMap collapsed_forward).not_hosting_of_identifies (origin := ())
    empty_sorts_separate (LeanMinus.leanTheory_conv_all (.srt .type) (.srt .kind))

/-- This existing recursive arithmetic control passes every constant type
check while failing the independently specified rewrite equation. -/
theorem constants_typing_is_not_rule_verification :
    Phenomena.wrongDouble.Typed LFProfile.standardLF Phenomena.withDouble Phenomena.unary ∧
      ¬ Phenomena.wrongDouble.Respects Phenomena.withDouble Phenomena.unary :=
  ⟨Phenomena.wrongDouble_typed, Unconditional.wrongDouble_not_respects⟩

theorem missing_fragment_does_not_cover_rules :
    ¬ ∀ rule, source.rule rule →
      ∃ fragment ∈ [leftTheory], fragment.rule rule := by
  intro covered
  obtain ⟨fragment, member, found⟩ := covered aliasRule (by simp [source, Theory.ofSig])
  have equal : fragment = leftTheory := List.mem_singleton.mp member
  subst fragment
  have wrong : aliasRule = midRule := List.mem_singleton.mp found
  have impossible : (.con "alias" : LF.Term) = .con "mid" :=
    (LF.Term.app.inj (congrArg Dedukti.RewriteRule.lhs wrong)).1
  have distinct : (.con "alias" : LF.Term) ≠ .con "mid" := by decide
  exact distinct impossible

/-! ## Two authored surfaces, followed by checked template lowering -/

namespace Surface

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open UpstreamTheoryQuotation
open UpstreamTheoryQuotation.EnglishAuthoring
open Mettapedia.OSLF.Framework.GrammarDerives

def symbolic : QuotedTheory := moduleTheory! Theory Functions() {
  Types { Expr; }
  Exports { Expr; }
  Terms {
    Seed . |- "seed" : Expr;
    Mid . x:Expr |- "mid" "(" x ")" : Expr;
    Alias . x:Expr |- "alias" "(" x ")" : Expr;
  }
  Rewrites {
    mid : (Mid x) ~> x;
    callAlias : (Alias x) ~> (Mid x);
  }
}

def english : QuotedTheory := englishTheory! Theory Functions {
  Declare the sort Expr.
  Export the sort Expr.
  Declare Seed returning Expr with notation "seed".
  Declare Mid taking x:Expr returning Expr with notation "mid" "(" x ")".
  Declare Alias taking x:Expr returning Expr with notation "alias" "(" x ")".
  Rewrite mid : (Mid x) to x.
  Rewrite callAlias : (Alias x) to (Mid x).
}

/-- Independently authored quotations have the same complete payload. -/
theorem surfaces_agree : english = symbolic := rfl

theorem surface_admitted : (admit? symbolic).isSome = true := by cbv

theorem authored_call_parses :
    enumDerives symbolic.toLanguageDef 3 "Expr" ["alias", "(", "mid", "(", "seed", ")", ")"] =
      [.apply "Alias" [.apply "Mid" [.apply "Seed" []]]] := by decide

theorem missing_operand_rejected :
    enumDerives symbolic.toLanguageDef 3 "Expr" ["mid", "(", ")"] = [] := by decide

theorem unknown_notation_rejected :
    enumDerives symbolic.toLanguageDef 3 "Expr" ["alien", "(", "seed", ")"] = [] := by decide

/-! ## The same authored language is a qualified GSLT-ML fibre -/

theorem equation_free : symbolic.toLanguageDef.isEquationFree = true := by decide

theorem nonrecursive : ∀ rule ∈ symbolic.rewrites,
    Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rule.premises :=
  (Mettapedia.OSLF.MeTTaIL.ContextualStep.check_noncontextualRules_iff _).mp (by decide +kernel)

def stage : Pattern := .apply "Functions" []

/-- Reuses the qualified `at` route; no new command syntax or execution
relation is introduced for the quotations. -/
def commandRoute (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) :
    Mettapedia.GSLT.IndexedOperational.CoveredTranslation
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations symbolic.toLanguageDef)
      (GSLTIL.FibreExecution.theory stage
        (Mettapedia.OSLF.MeTTaIL.Engine.rewriteStepWithPremisesUsing relations symbolic.toLanguageDef)) :=
  GSLTIL.FibreExecution.language_coveredTranslation relations symbolic.toLanguageDef stage
    equation_free nonrecursive

theorem command_paths_reflect (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (initial : Pattern) {answer : Pattern}
    (path : (GSLTIL.FibreExecution.theory stage
      (Mettapedia.OSLF.MeTTaIL.Engine.rewriteStepWithPremisesUsing relations symbolic.toLanguageDef)).MultiStep
      (GSLTIL.atPattern stage initial) answer) :
    ∃ final, answer = GSLTIL.atPattern stage final ∧
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations symbolic.toLanguageDef).MultiStep
        initial final :=
  GSLTIL.FibreExecution.language_paths_reflect relations symbolic.toLanguageDef stage
    equation_free nonrecursive initial path

theorem authored_call_successor :
    Mettapedia.OSLF.MeTTaIL.Engine.rewriteStepWithPremisesUsing
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty symbolic.toLanguageDef
      (.apply "Alias" [.apply "Mid" [.apply "Seed" []]]) =
        [.apply "Mid" [.apply "Mid" [.apply "Seed" []]]] := by cbv

/-- This small partial lowering handles the three declared constructors and
one rule variable. It is not the compiler for arbitrary module signatures. -/
def lowerPattern : Pattern → Option LF.Term
  | .fvar "x" => some (.var 0)
  | .apply "Seed" [] => some (.con "seed")
  | .apply "Mid" [argument] => (lowerPattern argument).map (.app (.con "mid"))
  | .apply "Alias" [argument] => (lowerPattern argument).map (.app (.con "alias"))
  | _ => none

/-- Side conditions and typed rule contexts are rejected by this template
adapter, rather than silently erased. The native calculus retains them. -/
def lowerRule (rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule) :
    Option Dedukti.RewriteRule :=
  if rule.premises.isEmpty && rule.typeContext.isEmpty then do
    let left ← lowerPattern rule.left
    let right ← lowerPattern rule.right
    pure ⟨left, right⟩
  else none

def lowerRules (language : LanguageDef) : Option (List Dedukti.RewriteRule) :=
  if language.equations.isEmpty then language.rewrites.mapM lowerRule else none

theorem symbolic_templates_exact :
    lowerRules symbolic.toLanguageDef = some [midRule, aliasRule] := by decide

theorem english_templates_exact :
    lowerRules english.toLanguageDef = some [midRule, aliasRule] := by decide

/-- The authored rule templates enter the actual checked translation under
the supplied typed signature. Signature lowering is not inferred from this. -/
theorem checked_symbolic_templates :
    ∃ rules, lowerRules symbolic.toLanguageDef = some rules ∧
      translation.Respects (Theory.ofSig sourceSig rules) target ∧
      translation.Typed LFProfile.standardLF (Theory.ofSig sourceSig rules) target :=
  ⟨[midRule, aliasRule], symbolic_templates_exact, source_respects, source_typed⟩

theorem checked_english_templates :
    ∃ rules, lowerRules english.toLanguageDef = some rules ∧
      translation.Respects (Theory.ofSig sourceSig rules) target ∧
      translation.Typed LFProfile.standardLF (Theory.ofSig sourceSig rules) target := by
  rw [surfaces_agree]
  exact checked_symbolic_templates

/-- A parsed authored program passes the actual source typing judgment, then
the general joined translation theorem supplies its target typing. -/
theorem authored_program_checked :
    ∃ sourceTerm,
      lowerPattern (.apply "Alias" [.apply "Mid" [.apply "Seed" []]]) = some sourceTerm ∧
      HasType LFProfile.standardLF source [] sourceTerm carrier ∧
      HasType LFProfile.standardLF target [] (translation.apply sourceTerm) (.con "T") := by
  let sourceTerm : LF.Term := .app (.con "alias") (.app (.con "mid") (.con "seed"))
  have aliasTyped : HasType LFProfile.standardLF source [] (.con "alias") arrow := .con rfl
  have midTyped : HasType LFProfile.standardLF source [] (.con "mid") arrow := .con rfl
  have seedTyped : HasType LFProfile.standardLF source [] (.con "seed") carrier := .con rfl
  have typed : HasType LFProfile.standardLF source [] sourceTerm carrier :=
    .app aliasTyped (.app midTyped seedTyped)
  have transported := source_typing_preserved typed
  change HasType LFProfile.standardLF target [] (translation.apply sourceTerm)
    (translation.meaning "Carrier") at transported
  rw [carrier_image] at transported
  exact ⟨sourceTerm, rfl, typed, transported⟩

theorem unknown_constructor_not_lowered : lowerPattern (.apply "Other" []) = none := by decide

theorem guard_not_erased :
    lowerRule {
      «name» := "guarded", typeContext := [],
      premises := [.congruence (.fvar "x") (.fvar "x")],
      left := .apply "Mid" [.fvar "x"], right := .fvar "x" } = none := by decide

def extraEquation : Equation where
  «name» := "extra"
  typeContext := []
  premises := []
  left := .apply "Seed" []
  right := .apply "Mid" [.apply "Seed" []]

theorem equation_not_erased :
    lowerRules { (symbolic.toLanguageDef) with «equations» := [extraEquation] } = none := by decide

end Surface

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiTranslationControls
