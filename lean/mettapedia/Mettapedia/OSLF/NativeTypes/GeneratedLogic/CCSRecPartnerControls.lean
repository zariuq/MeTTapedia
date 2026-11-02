import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecControls

/-!
# Controls: least partners of CCS with recursion

In the environment of the definitions of `CCSRecControls`, among them the silent loop `D ≝ τ.D`:

- **The sentinel is needed** (`no_sentinel_misleads`): `τ.0` beside the partner `~a.0` reduces to `~a.0 | 0`, which
  is `~a.0` beside the partner's continuation `0`, although `τ.0` has no action on `a`. With the sentinel `k.0` in
  place of `0`, a reduction beside the least partner shows the action exactly (`reduces_coPartner_iff`).
- **Saturated reduction bisimilarity is coarser than strong bisimilarity** (`loop_saturated`, `loop_not_bisimilar`):
  `a.0 | D` and `D` are saturated reduction bisimilar, because every reduction beside a partner keeps `D`, and is
  matched by `D`'s silent step; yet `a.0 | D` performs `a` and `D` does not. So the front door's partner-labelled
  native types do not tell them apart (`loop_agree`). Reductions beside partners see a process's actions only when the
  partner is used, which the sentinel shows.
- **The least partner with its sentinel, asked at the front door** (`act_loop_performs`, `loop_not_performs`): the
  modal decider answers whether, beside `~a.k.0`, a process steps to a residual beside `k.0`. `a.0 | D` does, to `D`;
  `D` does not, though both step beside the plain partner `~a.0` (`act_loop_steps_beside`, `loop_steps_beside`). The
  server `A(a)` answers and stays a server (`server_performs`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv derivedInstance_equivalent equationEquiv_fill)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms (typed_of_domain domain_of_typed names names_context)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecControls (definitions admitted)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners

/-! ## Reordering a bag keeps a process, and its canonical form -/

theorem perm_process {elements elements' : List Pattern} (perm : elements.Perm elements')
    (bagIn : processes (.collection .hashBag elements none)) :
    processes (.collection .hashBag elements' none) ∧
      blockCanon (.collection .hashBag elements none) = blockCanon (.collection .hashBag elements' none) := by
  obtain ⟨typed, object⟩ := typed_of_domain bagIn
  have typed' := typed_of_members typed fun element member => perm.mem_iff.mpr member
  have object' : isObjectPattern (.collection .hashBag elements' none) = true :=
    isObject_bag.mpr fun element member => bag_objects object element (perm.mem_iff.mpr member)
  exact ⟨domain_of_typed typed' object', canon_complete (block := ccsBlock) object (bag_result_equivalent perm typed)⟩

/-! ## The sentinel is needed -/

/-- `~a.0`: a partner of an action on `a`, with no sentinel. -/
def bareCoPartner : Pattern :=
  .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar "a", .apply "CNil" []]] none]

/-- `τ.0`. -/
def tauNil : Pattern := .apply "CSum" [.collection .hashBag [.apply "CTau" [.apply "CNil" []]] none]

theorem tauNil_no_action {residual : Pattern} : ¬ LStep definitions tauNil (.act (.fvar "a")) residual := by
  intro step
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  match k, hk, performs with
  | 0, _, performs => simp [guardAction] at performs

/-- **Without a sentinel, a reduction beside the partner misleads**: `τ.0 | ~a.0` reduces to `~a.0 | 0`, yet `τ.0`
has no action on `a` to the residual `~a.0`. -/
theorem no_sentinel_misleads :
    ¬ (Reduces definitions (par tauNil bareCoPartner) (par bareCoPartner (.apply "CNil" [])) ↔
      ∃ residual', LStep definitions tauNil (.act (.fvar "a")) residual' ∧
        blockCanon (par residual' (.apply "CNil" [])) = blockCanon (par bareCoPartner (.apply "CNil" []))) := by
  intro claimed
  have bagIn : processes (par tauNil bareCoPartner) := rfl
  have targetIn : processes (par bareCoPartner (.apply "CNil" [])) := rfl
  have swappedIn : processes (.collection .hashBag [.apply "CNil" [], bareCoPartner] none) := rfl
  have reduces : Reduces definitions (par tauNil bareCoPartner) (par bareCoPartner (.apply "CNil" [])) :=
    (reduces_iff_tau admitted bagIn targetIn).mpr ⟨_, .par 0 (by simp) (.offer rfl 0 (by simp) rfl),
      (perm_process (List.Perm.swap _ _ _) swappedIn).2⟩
  obtain ⟨_, step, -⟩ := claimed.mp reduces
  exact tauNil_no_action step

/-! ## Saturated reduction bisimilarity is coarser -/

/-- `D`, the silent loop `D ≝ τ.D`. -/
def loopCall : Pattern := call 2 []

theorem loop_offers : offers definitions loopCall = some [.apply "CTau" [loopCall]] := rfl

theorem loop_process : processes loopCall := rfl

/-- **The loop only moves silently, to itself.** -/
theorem loop_step {action : Action} {target : Pattern} (step : LStep definitions loopCall action target) :
    action = .tau ∧ target = loopCall := by
  generalize sourceIs : loopCall = source at step
  cases step with
  | offer offered k hk performs =>
      subst sourceIs
      rw [loop_offers, Option.some.injEq] at offered
      subst offered
      match k, hk, performs with
      | 0, _, performs =>
          simp only [List.getElem_cons_zero, guardAction, Option.some.injEq, Prod.mk.injEq] at performs
          exact ⟨performs.1.symm, performs.2.symm⟩
  | par => cases sourceIs
  | sync => cases sourceIs
  | res => simp [loopCall, call] at sourceIs

theorem loop_moves : LStep definitions loopCall .tau loopCall := .offer loop_offers 0 (by simp) rfl

/-- A process holding the loop, up to its canonical form. -/
def HasLoop (process : Pattern) : Prop :=
  ∃ rest, processes (.collection .hashBag (loopCall :: rest) none) ∧
    blockCanon process = blockCanon (.collection .hashBag (loopCall :: rest) none)

/-- **A silent transition keeps the loop.** -/
theorem hasLoop_step {process target : Pattern} (processIn : processes process) (has : HasLoop process)
    (step : LStep definitions process .tau target) : HasLoop target := by
  obtain ⟨rest, bagIn, same⟩ := has
  obtain ⟨forward, -⟩ := matched_of_procEquiv admitted names_context (procEquiv_of_canon processIn bagIn same)
    (typed_of_domain processIn).2
  obtain ⟨target', step', related⟩ := forward step
  have targetIn := process_of_step admitted step processIn
  have targetIn' := process_of_step admitted step' bagIn
  have canonSame : blockCanon target = blockCanon target' :=
    canon_complete (block := ccsBlock) (typed_of_domain targetIn).2 related
  obtain ⟨result, move, rfl⟩ := bagMove_of_step step'
  rcases move.result_cases with ⟨member, rest₁, moved, perm, memberStep, rfl⟩ |
    ⟨first, second, rest₁, moved, moved', name, perm, firstStep, secondStep, -, rfl⟩
  · by_cases isLoop : member = loopCall
    · subst isLoop
      obtain ⟨-, rfl⟩ := loop_step memberStep
      exact ⟨rest₁, targetIn', canonSame⟩
    · obtain ⟨rest₂, restPerm, -⟩ := perm_cons_cons_of_ne perm isLoop
      obtain ⟨reorderedIn, reorderedSame⟩ :=
        perm_process ((restPerm.cons moved).trans (List.Perm.swap _ _ _)) targetIn'
      exact ⟨moved :: rest₂, reorderedIn, canonSame.trans reorderedSame⟩
  · have firstNot : first ≠ loopCall := fun same => by
      subst same
      exact absurd (loop_step firstStep).1 (by simp)
    have secondNot : second ≠ loopCall := fun same => by
      subst same
      exact absurd (loop_step secondStep).1 (by simp)
    obtain ⟨rest₂, restPerm₂, -⟩ := perm_cons_cons_of_ne perm firstNot
    obtain ⟨rest₃, restPerm₃, -⟩ := perm_cons_cons_of_ne restPerm₂.symm secondNot
    have reordered : (moved :: moved' :: rest₁).Perm (loopCall :: moved :: moved' :: rest₃) := by
      refine ((restPerm₃.cons moved').cons moved).trans ?_
      perm_ac
    obtain ⟨reorderedIn, reorderedSame⟩ := perm_process reordered targetIn'
    exact ⟨moved :: moved' :: rest₃, reorderedIn, canonSame.trans reorderedSame⟩

/-- A reduction keeps the loop. -/
theorem hasLoop_reduces {process next : Pattern} (processIn : processes process) (has : HasLoop process)
    (reduces : Reduces definitions process next) : HasLoop next := by
  have nextIn := reduces_process admitted processIn reduces
  obtain ⟨next', step, same⟩ := (reduces_iff_tau admitted processIn nextIn).mp reduces
  obtain ⟨rest, bagIn, canonIs⟩ := hasLoop_step processIn has step
  exact ⟨rest, bagIn, same.symm.trans canonIs⟩

/-- **A process holding the loop reduces to itself**, by the loop's silent step. -/
theorem reduces_self {process : Pattern} (processIn : processes process) (has : HasLoop process) :
    Reduces definitions process process := by
  obtain ⟨rest, bagIn, same⟩ := has
  obtain ⟨-, backward⟩ := matched_of_procEquiv admitted names_context (procEquiv_of_canon processIn bagIn same)
    (typed_of_domain processIn).2
  have loopStep : LStep definitions (.collection .hashBag (loopCall :: rest) none) .tau
      (.collection .hashBag (loopCall :: rest) none) := .par 0 (by simp) loop_moves
  obtain ⟨target, step, related⟩ := backward loopStep
  refine (reduces_iff_tau admitted processIn processIn).mpr ⟨target, step, ?_⟩
  exact ((canon_complete (block := ccsBlock) (typed_of_domain bagIn).2 related).symm.trans same.symm)

/-- A process holding the loop holds it beside a partner. -/
theorem hasLoop_par {process partner : Pattern} (processIn : processes process) (partnerIn : processes partner)
    (has : HasLoop process) : HasLoop (par process partner) := by
  obtain ⟨rest, bagIn, same⟩ := has
  obtain ⟨bagTyped, bagObject⟩ := typed_of_domain bagIn
  obtain ⟨partnerTyped, partnerObject⟩ := typed_of_domain partnerIn
  have nestedIn : processes (par (.collection .hashBag (loopCall :: rest) none) partner) := par_process bagIn partnerIn
  have flatMembers : Members ccsRecCalc ccsBlock names [] (loopCall :: (rest ++ [partner])) := by
    intro element member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with rfl | inRest | rfl
    · exact members_of_bag (block := ccsBlock) bagTyped _ List.mem_cons_self
    · exact members_of_bag (block := ccsBlock) bagTyped _ (List.mem_cons_of_mem _ inRest)
    · exact partnerTyped
  have flatObject : isObjectPattern (.collection .hashBag (loopCall :: (rest ++ [partner])) none) = true := by
    refine isObject_bag.mpr fun element member => ?_
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with rfl | inRest | rfl
    · exact bag_objects bagObject _ List.mem_cons_self
    · exact bag_objects bagObject _ (List.mem_cons_of_mem _ inRest)
    · exact partnerObject
  have flatIn : processes (.collection .hashBag (loopCall :: (rest ++ [partner])) none) :=
    domain_of_typed (bag_typed (block := ccsBlock) flatMembers) flatObject
  have inside : EquationEquiv (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty) ccsRecCalc (par process partner)
      (par (.collection .hashBag (loopCall :: rest) none) partner) :=
    equationEquiv_fill (.collection .hashBag [] .hole [partner] none)
      (procEquiv_of_canon processIn bagIn same).toEquationEquiv
  have flattened := derivedInstance_equivalent
    (base := Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
    (ccsRecBlockLanguage.flatten (pre := []) (post := [partner])
    (typed_of_domain nestedIn).1)
  exact ⟨rest ++ [partner], flatIn, canon_complete (block := ccsBlock)
    (typed_of_domain (par_process processIn partnerIn)).2 (.trans _ _ _ inside flattened)⟩

/-- **Processes holding the loop are saturated reduction bisimilar.** -/
theorem loops_saturated : IsSaturatedReduction definitions
    (fun first second => processes first ∧ processes second ∧ HasLoop first ∧ HasLoop second) := by
  rintro first second ⟨firstIn, secondIn, firstHas, secondHas⟩ partner partnerIn
  have firstBag := par_process firstIn partnerIn
  have secondBag := par_process secondIn partnerIn
  constructor
  · intro next reduces
    exact ⟨par second partner, reduces_self secondBag (hasLoop_par secondIn partnerIn secondHas),
      reduces_process admitted firstBag reduces, secondBag,
      hasLoop_reduces firstBag (hasLoop_par firstIn partnerIn firstHas) reduces,
      hasLoop_par secondIn partnerIn secondHas⟩
  · intro next reduces
    exact ⟨par first partner, reduces_self firstBag (hasLoop_par firstIn partnerIn firstHas), firstBag,
      reduces_process admitted secondBag reduces, hasLoop_par firstIn partnerIn firstHas,
      hasLoop_reduces secondBag (hasLoop_par secondIn partnerIn secondHas) reduces⟩

/-- `a.0`. -/
def actNil : Pattern := .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "a", .apply "CNil" []]] none]

/-- **`a.0 | D` and `D` are saturated reduction bisimilar.** -/
theorem loop_saturated : SaturatedReductionBisimilar definitions (par actNil loopCall) loopCall := by
  have pairIn : processes (par actNil loopCall) := rfl
  have singleIn : processes (.collection .hashBag [loopCall] none) := rfl
  refine ⟨_, loops_saturated, fun _ _ related => ⟨related.1, related.2.1⟩, pairIn, loop_process, ?_, ?_⟩
  · obtain ⟨swappedIn, swappedSame⟩ := perm_process (List.Perm.swap loopCall actNil []) pairIn
    exact ⟨[actNil], swappedIn, swappedSame⟩
  · refine ⟨[], singleIn, ?_⟩
    have single := derivedInstance_equivalent
      (base := Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      (ccsRecBlockLanguage.singleton (typed_of_domain loop_process).1)
    exact (canon_complete (block := ccsBlock) (typed_of_domain singleIn).2 single).symm

/-- **`a.0 | D` and `D` are not strongly bisimilar**: `a.0 | D` performs `a`, and `D` moves only silently. -/
theorem loop_not_bisimilar : ¬ Bisimilar definitions (par actNil loopCall) loopCall := by
  intro bisimilar
  have step : LStep definitions (par actNil loopCall) (.act (.fvar "a"))
      (.collection .hashBag [.apply "CNil" [], loopCall] none) := .par 0 (by simp) (.offer rfl 0 (by simp) rfl)
  obtain ⟨_, step', -⟩ := bisimilar.forth step
  exact absurd (loop_step step').1 (by simp)

/-- **Saturated reduction bisimilarity strictly contains strong bisimilarity**, in the presence of a silent loop. -/
theorem saturated_ne_bisimilar :
    SaturatedReductionBisimilar definitions (par actNil loopCall) loopCall ∧
      ¬ Bisimilar definitions (par actNil loopCall) loopCall :=
  ⟨loop_saturated, loop_not_bisimilar⟩

/-- **The partner-labelled native types do not tell `a.0 | D` from `D`**, which are not strongly bisimilar. -/
theorem loop_agree :
    (frontDoor definitions).AgreeOn (Formula.forwardOn isPartnerLabel) (par actNil loopCall) loopCall ∧
      ¬ Bisimilar definitions (par actNil loopCall) loopCall :=
  ⟨(agree_iff_saturated admitted (rfl : processes (par actNil loopCall)) loop_process).mpr loop_saturated,
    loop_not_bisimilar⟩

/-! ## The least partner with its sentinel, asked at the front door -/

/-- The server `A(a)`. -/
def server : Pattern := call 0 [.fvar "a"]

/-- Some step beside the partner. -/
def stepsBeside (partnerProcess : Pattern) : Formula 0 := .possibly (partnerLabel "h" partnerProcess) .top

/-- Beside the least partner of an action on `a`, with the sentinel `k.0`: a step to the residual beside the
sentinel. -/
def performs (residual : Pattern) : Formula 0 :=
  .possibly (partnerLabel "h" (coPartner "a" "k")) (.is (par residual (sentinel "k")))

theorem server_performs : (frontDoor definitions).sat Env.closed (performs server) server :=
  decided_holds admitted (by decide +kernel)

theorem loop_steps_beside : (frontDoor definitions).sat Env.closed (stepsBeside bareCoPartner) loopCall :=
  decided_holds admitted (by decide +kernel)

theorem act_loop_steps_beside :
    (frontDoor definitions).sat Env.closed (stepsBeside bareCoPartner) (par actNil loopCall) :=
  decided_holds admitted (by decide +kernel)

theorem act_loop_performs : (frontDoor definitions).sat Env.closed (performs loopCall) (par actNil loopCall) :=
  decided_holds admitted (by decide +kernel)

theorem loop_not_performs : ¬ (frontDoor definitions).sat Env.closed (performs loopCall) loopCall :=
  decided_fails admitted (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerControls
