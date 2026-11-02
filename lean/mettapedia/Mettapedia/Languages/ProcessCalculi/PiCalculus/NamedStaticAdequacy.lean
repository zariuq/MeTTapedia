import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexClosing
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BindingAgreement
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EquationAdequacy
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSubstitution

/-!
# Named structural congruence in `piCalc`'s static theory

The named π-calculus's structural congruence (`StructuralCongruence`) has the parallel laws, ν of inaction, scope
extrusion, exchange of restrictions, α-conversion, and the unfolding of replicated input. `piCalc` declares all of
these: its server `!x(y).P` is the replication of an input, which unfolds by the law `!P = {P, !P}`.

So every derivation of structural congruence relates processes whose translations `piCalc`'s static theory relates
(`equationEquiv_of_structural`), and they have one canonical form (`canonR_eq_of_structural`). The converse fails:
`piCalc` also declares that two copies of a replication are one, which the named congruence does not, so
`!a(x).0 | !a(x).0` and `!a(x).0` are apart there and equal here (`duplicates_identified`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars closeFVar freeVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv equationEquiv_fill)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piToPattern piPar piComponents
  piPar_components piNameContext piToPattern_hasType piToPattern_admissible piPar_hasType piPar_equivalent_bag
  piPar_equivalent_congr piPar_equivalent_comm piPar_equivalent_unit_left piPar_equivalent_unit_right
  piPar_equivalent_assoc freeVars_piToPattern piToPattern_alpha_input piToPattern_alpha_nu
  piToPattern_alpha_replicate)

/-! ## Closing a name in a translation -/

theorem closeFVar_absent (name : String) (pattern : Pattern) :
    ∀ level, name ∉ freeVars pattern → closeFVar level name pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => intro _ _; simp [closeFVar]
  | hfvar other =>
      intro level absent
      simp only [freeVars, List.mem_singleton] at absent
      simp only [closeFVar]
      split
      · rename_i same
        exact absurd (beq_iff_eq.mp same).symm absent
      · rfl
  | happly constructor arguments recurse =>
      intro level absent
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [closeFVar]
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun argument member => recurse argument member level (absent argument member)
  | hlambda binder body recurse =>
      intro level absent
      simp only [freeVars] at absent
      simp only [closeFVar, recurse (level + 1) absent]
  | hmultiLambda arity binders body recurse =>
      intro level absent
      simp only [freeVars] at absent
      simp only [closeFVar, recurse (level + arity) absent]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro level absent
      simp only [freeVars, List.mem_append, not_or] at absent
      simp only [closeFVar, bodyRecurse (level + 1) absent.1, replacementRecurse level absent.2]
  | hcollection kind elements rest recurse =>
      intro level absent
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [closeFVar]
      congr 1
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun element member => recurse element member level (absent element member)

theorem components_close (name : String) (level : Nat) (pattern : Pattern) :
    piComponents (closeFVar level name pattern) = (piComponents pattern).map (closeFVar level name) := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp [piComponents, closeFVar]
  | fvar other => by_cases same : other = name <;> simp [piComponents, closeFVar, same]
  | _ => simp [piComponents, closeFVar]

theorem close_nu (name : String) (level : Nat) (binder : Option String) (body : Pattern) :
    closeFVar level name (.apply "PiNu" [.lambda binder body]) =
      .apply "PiNu" [.lambda binder (closeFVar (level + 1) name body)] := by
  simp [closeFVar]

theorem close_piPar (name : String) (level : Nat) (first second : Pattern) :
    closeFVar level name (piPar first second) = piPar (closeFVar level name first) (closeFVar level name second) := by
  rw [piPar_components, piPar_components, close_bag, List.map_append, components_close, components_close]

theorem piToPattern_scoped (P : Process) : (piToPattern P).isWellScopedAt 0 = true := by
  simpa using (piToPattern_hasType P).isWellScopedAt

theorem lift_piToPattern (P : Process) : liftBVars 0 1 (piToPattern P) = piToPattern P :=
  Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt (piToPattern_scoped P)

theorem names_context : BaseContext piNameContext [] := Blocks.piNameContext_base

theorem liftIndex_add (outer inner : Nat) (relabel : Nat → Nat) :
    liftIndex outer (liftIndex inner relabel) = liftIndex (inner + outer) relabel := by
  funext index
  simp only [liftIndex]
  by_cases belowOuter : index < outer
  · have below : index < inner + outer := by omega
    simp [belowOuter, below]
  · by_cases belowInner : index - outer < inner
    · have below : index < inner + outer := by omega
      simp only [belowOuter, belowInner, below, if_false, if_true]
      omega
    · have notBelow : ¬ index < inner + outer := by omega
      simp only [belowOuter, belowInner, notBelow, if_false]
      rw [show index - outer - inner = index - (inner + outer) by omega]
      omega

/-- **Exchanging two bound names**: closing `x` inside `y` is closing `y` inside `x`, the two new variables
exchanged, for a pattern with no other variable at that level. -/
theorem close_close_swap {first second : String} (different : first ≠ second) (pattern : Pattern) :
    ∀ level, pattern.isWellScopedAt level = true →
      rename (liftIndex level swapInner) (closeFVar (level + 1) first (closeFVar level second pattern)) =
        closeFVar (level + 1) second (closeFVar level first pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at wellScoped
      simp [closeFVar, rename_bvar, liftIndex, wellScoped]
  | hfvar name =>
      intro level _
      by_cases isFirst : name = first
      · subst isFirst
        simp [closeFVar, rename_bvar, liftIndex, swapInner, different]
      · by_cases isSecond : name = second
        · subst isSecond
          simp [closeFVar, rename_bvar, liftIndex, swapInner, isFirst, Nat.add_comm]
        · simp [closeFVar, rename_fvar, isFirst, isSecond]
  | happly constructor arguments recurse =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
      simp only [closeFVar, rename_apply, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member level (wellScoped argument member)
  | hlambda binder body recurse =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [closeFVar, rename_lambda, liftIndex_add]
      congr 1
      exact recurse (level + 1) wellScoped
  | hmultiLambda arity binders body recurse =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [closeFVar, rename_multiLambda, liftIndex_add]
      congr 1
      rw [show level + 1 + arity = level + arity + 1 by omega]
      exact recurse (level + arity) wellScoped
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
      simp only [closeFVar, rename_subst, liftIndex_add]
      congr 1
      · exact bodyRecurse (level + 1) wellScoped.1
      · exact replacementRecurse level wellScoped.2
  | hcollection kind elements rest recurse =>
      intro level wellScoped
      simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
      simp only [closeFVar, rename_collection, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member level (wellScoped element member)

/-! ## Each law of the named congruence -/

/-- **Binding a name is a congruence for the translation.** -/
theorem close_equivalent {P P' : Process} (name : String)
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern P) (piToPattern P')) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (closeFVar 0 name (piToPattern P))
      (closeFVar 0 name (piToPattern P')) :=
  equationEquiv_close_replication (block := piRepBlock) names_context (name := name) rfl (piToPattern_hasType P)
    (piToPattern_hasType P') (piToPattern_admissible P).object (piToPattern_admissible P').object equivalent


theorem close_typed {P : Process} (name : String) :
    HasType piCalc piNameContext [.base "Name"] (closeFVar 0 name (piToPattern P)) (.base "Proc") := by
  simpa using (piToPattern_hasType P).closeFVar name (.base "Name") rfl

theorem close_close_typed {P : Process} (outer inner : String) :
    HasType piCalc piNameContext [.base "Name", .base "Name"]
      (closeFVar 1 outer (closeFVar 0 inner (piToPattern P))) (.base "Proc") := by
  simpa using (close_typed (P := P) inner).closeFVar outer (.base "Name") rfl

/-- **Every derivation of named structural congruence is a chain of `piCalc`'s laws** between the translations. -/
theorem equationEquiv_of_structural : ∀ {P Q : Process}, StructuralCongruence P Q →
      EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern P) (piToPattern Q)
  | _, _, .refl _ => .refl _
  | _, _, .symm _ _ derivation => .symm _ _ (equationEquiv_of_structural derivation)
  | _, _, .trans _ _ _ first second =>
      .trans _ _ _ (equationEquiv_of_structural first) (equationEquiv_of_structural second)
  | _, _, .par_cong P P' Q Q' first second =>
      piPar_equivalent_congr (piToPattern_hasType P) (piToPattern_hasType P') (piToPattern_hasType Q)
        (piToPattern_hasType Q') (equationEquiv_of_structural first) (equationEquiv_of_structural second)
  | _, _, .input_cong channel bound P P' inner => by
      have closed := close_equivalent bound (equationEquiv_of_structural inner)
      simpa [piToPattern, OneHoleContext.fill] using
        equationEquiv_fill (.apply "PiInp" [.fvar channel] (.lambda none .hole) []) closed
  | _, _, .nu_cong name P P' inner => by
      have closed := close_equivalent name (equationEquiv_of_structural inner)
      simpa [piToPattern, OneHoleContext.fill] using
        equationEquiv_fill (.apply "PiNu" [] (.lambda none .hole) []) closed
  | _, _, .replicate_cong channel bound P P' inner => by
      have closed := close_equivalent bound (equationEquiv_of_structural inner)
      have input := equationEquiv_fill (.apply "PiInp" [.fvar channel] (.lambda none .hole) []) closed
      simpa [piToPattern, OneHoleContext.fill] using
        equationEquiv_fill (.apply "PiRep" [] .hole []) input
  | _, _, .par_comm P Q => piPar_equivalent_comm (piToPattern_hasType P) (piToPattern_hasType Q)
  | _, _, .par_assoc P Q R =>
      piPar_equivalent_assoc (piToPattern_hasType P) (piToPattern_hasType Q) (piToPattern_hasType R)
  | _, _, .par_nil_left P => piPar_equivalent_unit_left (piToPattern_hasType P)
  | _, _, .par_nil_right P => piPar_equivalent_unit_right (piToPattern_hasType P)
  | _, _, .nu_nil name => by
      simpa [piToPattern, closeFVar] using
        (restriction_nil_equivalent (block := piBlock) (free := piNameContext) (bound := [])).toEquationEquiv
  | _, _, .nu_par name P Q fresh => by
      have absent : name ∉ freeVars (piToPattern Q) := fun member => fresh ((freeVars_piToPattern Q name).mp member)
      have bodyTyped := close_typed (P := P) name
      have restTyped : HasType piCalc piNameContext [.base "Name"] (piToPattern Q) (.base "Proc") := by
        simpa [lift_piToPattern] using lift_one (block := piBlock) (piToPattern_hasType Q)
      have unfolded : piToPattern (.nu name (.par P Q)) =
          .apply "PiNu" [.lambda none (piPar (closeFVar 0 name (piToPattern P)) (piToPattern Q))] := by
        simp only [piToPattern, close_piPar, closeFVar_absent name (piToPattern Q) 0 absent]
      rw [unfolded]
      have asBag := equationEquiv_fill (.apply "PiNu" [] (.lambda none .hole) [])
        (Relation.EqvGen.symm _ _ (piPar_equivalent_bag bodyTyped restTyped))
      simp only [OneHoleContext.fill, List.nil_append] at asBag
      have extruded := (extrusion_equivalent (block := piBlock) bodyTyped
        (Members.cons (piToPattern_hasType Q) Members.nil)).toEquationEquiv
      simp only [List.map_cons, List.map_nil, lift_piToPattern] at extruded
      have paired := piPar_equivalent_bag (restrict_typed (block := piBlock) bodyTyped) (piToPattern_hasType Q)
      exact .trans _ _ _ asBag (.trans _ _ _ (.symm _ _ extruded) paired)
  | _, _, .nu_swap outer inner P => by
      simp only [piToPattern, close_nu]
      by_cases same : outer = inner
      · subst same
        have absent : outer ∉ freeVars (closeFVar 0 outer (piToPattern P)) := fun member =>
          ((Mettapedia.OSLF.MeTTaIL.Substitution.freeVars_closeFVar_iff _ 0 outer outer).mp member).1 rfl
        rw [closeFVar_absent outer _ 1 absent]
        exact .refl _
      · have bodyTyped := close_close_typed (P := P) outer inner
        have swappedTyped := close_close_typed (P := P) inner outer
        have swapEq := close_close_swap same (piToPattern P) 0 (piToPattern_scoped P)
        simp only [Nat.zero_add, liftIndex_zero] at swapEq
        have exchanged := (exchange_equivalent (block := piBlock) bodyTyped).toEquationEquiv
        rw [swapEq] at exchanged
        exact exchanged
  | _, _, .alpha_input channel old new P fresh _ => by
      rw [piToPattern_alpha_input channel old new P fresh]
      exact .refl _
  | _, _, .alpha_nu old new P fresh => by
      rw [piToPattern_alpha_nu old new P fresh]
      exact .refl _
  | _, _, .alpha_replicate channel old new P fresh _ => by
      rw [piToPattern_alpha_replicate channel old new P fresh]
      exact .refl _
  | _, _, .replicate_unfold channel bound P => by
      have inputTyped := piToPattern_hasType (.input channel bound P)
      have unfolded := (unfold_equivalent (block := piRepBlock) inputTyped).toEquationEquiv
      have paired := piPar_equivalent_bag inputTyped (piToPattern_hasType (.replicate channel bound P))
      exact .trans _ _ _ unfolded (.symm _ _ paired)

/-- **Structurally congruent processes have one canonical form.** -/
theorem canonR_eq_of_structural {P Q : Process} (derivation : StructuralCongruence P Q) :
    canonR piRepBlock (piToPattern P) = canonR piRepBlock (piToPattern Q) :=
  canonR_complete (block := piRepBlock) (piToPattern_admissible P).object (piToPattern_admissible Q).object
    (restrictionsBind_of_typed (block := piRepBlock) _ (piToPattern_hasType P)) (equationEquiv_of_structural derivation)

/-- **Two copies of a server are one in `piCalc`**, where the named congruence keeps them apart: `piCalc` declares
`{!P, !P} = !P`, a law strong bisimilarity validates and the named congruence lacks. -/
theorem duplicates_identified :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.par (.replicate "a" "x" .nil) (.replicate "a" "x" .nil))) (piToPattern (.replicate "a" "x" .nil)) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) names_context (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
