import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# MM2 rule-scoped execution

MM2 variables are scoped by one executable directive.  Variables written in
the input are matcher variables and must be bound before they can be used in
an output.  Variables written only in an output are local binders in the
emitted expression.  Values captured by an input binding remain opaque: any
variables inside such a value belong to the captured expression.

The physical workspace is keyed by MORK compact expressions.  Compact keys
replace variable spellings by first-occurrence indices, so insertion and
removal below use those keys rather than nominal `Atom` equality.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open ReflectiveComputable
open WQComputable

/-! ## Variables authored by an input -/

/-- Variables occurring in one explicit input factor. -/
def sourceFactorVariables : SourceFactor → List String
  | .btm pattern => atomFreeVars pattern
  | .eqConstraint pattern witness =>
      atomFreeVars pattern ++ atomFreeVars witness
  | .neqConstraint pattern witness =>
      atomFreeVars pattern ++ atomFreeVars witness

/-- Variables occurring in the authored input of one directive. -/
def inputSpecVariables : InputSpec → List String
  | .compat pattern => atomFreeVars.atomFreeVarsList pattern.atoms
  | .explicit factors => factors.flatMap sourceFactorVariables

/-- Whether a variable is inherited from the directive input. -/
def inputSpecUsesVariable (input : InputSpec) (name : String) : Bool :=
  (inputSpecVariables input).contains name

/-! ## Input-inherited data outputs -/

mutual
  /-- Whether every variable authored in an output atom is inherited from the
  directive input.  This is the strict discipline for transaction and other
  data rows.  It is intentionally separate from rule-scoped output coverage:
  an emitted executable expression may introduce its own local binders. -/
  def ruleTemplateVariablesInherited (input : InputSpec) : Atom → Bool
    | .var name => inputSpecUsesVariable input name
    | .symbol _ | .grounded _ => true
    | .expression children =>
        ruleTemplatesVariablesInherited input children

  /-- Structural input-inheritance check for a finite atom sequence. -/
  def ruleTemplatesVariablesInherited (input : InputSpec) :
      List Atom → Bool
    | [] => true
    | head :: tail =>
        ruleTemplateVariablesInherited input head &&
          ruleTemplatesVariablesInherited input tail
end

/-- Input-inherited-variable discipline for one support sink. -/
def ruleSinkVariablesInherited (input : InputSpec) (sink : Sink) : Bool :=
  ruleTemplateVariablesInherited input sink.atom

/-- Input-inherited-variable discipline for a finite sink batch. -/
def ruleSinksVariablesInherited (input : InputSpec)
    (sinks : List Sink) : Bool :=
  sinks.all (ruleSinkVariablesInherited input)

mutual
  /-- Rule-scoped output coverage.  Input variables require matcher bindings;
  output-local variables introduce binders and therefore need no binding. -/
  def ruleTemplateCovered (input : InputSpec) (substitution : Subst) :
      Atom → Bool
    | .var name =>
        if inputSpecUsesVariable input name then
          (substitution.lookup name).isSome
        else
          true
    | .symbol _ | .grounded _ => true
    | .expression children =>
        ruleTemplatesCovered input substitution children

  def ruleTemplatesCovered (input : InputSpec) (substitution : Subst) :
      List Atom → Bool
    | [] => true
    | head :: tail =>
        ruleTemplateCovered input substitution head &&
          ruleTemplatesCovered input substitution tail
end

/-- On an output whose variables all come from the directive input,
rule-scoped coverage is exactly the earlier fully-bound coverage test. -/
theorem ruleTemplateCovered_eq_templateCovered_of_variablesInherited
    (input : InputSpec) (substitution : Subst) :
    ∀ template,
      ruleTemplateVariablesInherited input template = true →
        ruleTemplateCovered input substitution template =
          templateCovered substitution template
  | .var name, inherited => by
      have used : inputSpecUsesVariable input name = true := by
        simpa [ruleTemplateVariablesInherited] using inherited
      simp [ruleTemplateCovered, templateCovered, used]
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, inherited => by
      exact ruleTemplatesCovered_eq_templatesCovered children inherited
where
  ruleTemplatesCovered_eq_templatesCovered :
      ∀ templates,
        ruleTemplatesVariablesInherited input templates = true →
          ruleTemplatesCovered input substitution templates =
            templatesCovered substitution templates
    | [], _ => rfl
    | head :: tail, inherited => by
        simp only [ruleTemplatesVariablesInherited, Bool.and_eq_true]
          at inherited
        simp only [ruleTemplatesCovered, templatesCovered]
        rw [ruleTemplateCovered_eq_templateCovered_of_variablesInherited
              input substitution head inherited.1,
          ruleTemplatesCovered_eq_templatesCovered tail inherited.2]

/-- Instantiate one output under the scope of its directive. -/
def instantiateRuleTemplateAtom? (input : InputSpec)
    (substitution : Subst) (template : Atom) : Option Atom :=
  if ruleTemplateCovered input substitution template then
    some (applySubst substitution template)
  else
    none

/-- Input-inherited outputs have identical rule-scoped and fully-bound
instantiations.  Output-local variables are deliberately excluded. -/
theorem instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    (input : InputSpec) (substitution : Subst) (template : Atom)
    (inherited : ruleTemplateVariablesInherited input template = true) :
    instantiateRuleTemplateAtom? input substitution template =
      instantiateTemplateAtom? substitution template := by
  simp only [instantiateRuleTemplateAtom?, instantiateTemplateAtom?,
    ruleTemplateCovered_eq_templateCovered_of_variablesInherited input
      substitution template inherited]

/-- Fully bound reflective templates remain fully bound under rule-scoped
coverage.  Rule scoping is a conservative extension of the earlier policy. -/
theorem ruleTemplateCovered_of_templateCovered
    (input : InputSpec) (substitution : Subst) :
    ∀ template,
      templateCovered substitution template = true →
        ruleTemplateCovered input substitution template = true
  | .var name, covered => by
      by_cases inherited : inputSpecUsesVariable input name = true
      · simpa [ruleTemplateCovered, inherited, templateCovered] using covered
      · have notInherited : inputSpecUsesVariable input name = false :=
          Bool.eq_false_of_not_eq_true inherited
        simp [ruleTemplateCovered, notInherited]
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, covered =>
      ruleTemplatesCovered_of_templatesCovered input substitution children
        covered
where
  ruleTemplatesCovered_of_templatesCovered
      (input : InputSpec) (substitution : Subst) :
      ∀ templates,
        templatesCovered substitution templates = true →
          ruleTemplatesCovered input substitution templates = true
    | [], _ => rfl
    | head :: tail, covered => by
        simp only [templatesCovered, Bool.and_eq_true] at covered
        simp only [ruleTemplatesCovered, Bool.and_eq_true]
        exact
          ⟨ruleTemplateCovered_of_templateCovered input substitution head
              covered.1,
            ruleTemplatesCovered_of_templatesCovered input substitution tail
              covered.2⟩

/-- On every fully bound output, rule-scoped and reflective instantiation are
exactly the same computation. -/
theorem instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?_of_covered
    (input : InputSpec) (substitution : Subst) (template : Atom)
    (covered : templateCovered substitution template = true) :
    instantiateRuleTemplateAtom? input substitution template =
      instantiateTemplateAtom? substitution template := by
  have ruleCovered :=
    ruleTemplateCovered_of_templateCovered input substitution template covered
  simp [instantiateRuleTemplateAtom?, instantiateTemplateAtom?, covered,
    ruleCovered]

@[simp] theorem instantiateRuleTemplateAtom?_outputLocal
    (input : InputSpec) (substitution : Subst) (name : String)
    (outputLocal : inputSpecUsesVariable input name = false) :
    instantiateRuleTemplateAtom? input substitution (.var name) =
      some ((substitution.lookup name).getD (.var name)) := by
  simp [instantiateRuleTemplateAtom?, ruleTemplateCovered, outputLocal,
    applySubst]

@[simp] theorem instantiateRuleTemplateAtom?_inputVariable
    (input : InputSpec) (substitution : Subst) (name : String)
    (inherited : inputSpecUsesVariable input name = true) :
    instantiateRuleTemplateAtom? input substitution (.var name) =
      substitution.lookup name := by
  cases lookup : substitution.lookup name with
  | none =>
      simp [instantiateRuleTemplateAtom?, ruleTemplateCovered, inherited,
        lookup]
  | some value =>
      simp [instantiateRuleTemplateAtom?, ruleTemplateCovered, inherited,
        lookup]
      change (substitution.lookup name).getD (.var name) = value
      simp [lookup]

/-! ## Physical support identity -/

/-- A workspace key is either an exact compact-expression path or an abstract
key for a host atom outside the MM2-representable fragment. -/
inductive MorkSupportKey where
  | compact : List Nat → MorkSupportKey
  | abstract : Atom → MorkSupportKey
  deriving Repr, DecidableEq

/-- Physical support identity for one atom. -/
def morkSupportKey (atom : Atom) : MorkSupportKey :=
  match morkCompactKey? atom with
  | some key => .compact key
  | none => .abstract atom

/-- Key-aware equality used by the executable list carrier. -/
def sameMorkSupportAtom (left right : Atom) : Bool :=
  decide (morkSupportKey left = morkSupportKey right)

/-- Find the representative of an atom's physical key. -/
def morkSupportFind? (support : List Atom) (atom : Atom) : Option Atom :=
  support.find? fun candidate => sameMorkSupportAtom candidate atom

/-- Test physical-key membership. -/
def morkSupportContains (support : List Atom) (atom : Atom) : Bool :=
  (morkSupportFind? support atom).isSome

/-- Insert only when the physical key is absent. -/
def morkInsertSupport (support : List Atom) (atom : Atom) : List Atom :=
  if morkSupportContains support atom then support else support ++ [atom]

/-- Remove every representative of one physical key. -/
def morkEraseSupport (support : List Atom) (atom : Atom) : List Atom :=
  support.filter fun candidate => !sameMorkSupportAtom candidate atom

/-- Union two executable support presentations by physical identity. -/
def morkUnionSupport (support staged : List Atom) : List Atom :=
  staged.foldl morkInsertSupport support

/-- Subtract staged physical identities from executable support. -/
def morkSubtractSupport (support staged : List Atom) : List Atom :=
  staged.foldl morkEraseSupport support

/-- Duplicate freedom at the physical compact-key level. -/
def MorkSupportNodup (support : List Atom) : Prop :=
  (support.map morkSupportKey).Nodup

/-- Compact-key duplicate freedom is exactly the injectivity needed on the
represented support, without claiming that compact keys are globally
injective on variable-bearing syntax. -/
theorem morkSupportKey_injective_on
    {support : List Atom} (nodup : MorkSupportNodup support)
    {left right : Atom} (leftMember : left ∈ support)
    (rightMember : right ∈ support)
    (keysEqual : morkSupportKey left = morkSupportKey right) :
    left = right := by
  exact List.inj_on_of_nodup_map nodup leftMember rightMember keysEqual

theorem sameMorkSupportAtom_eq_true_iff (left right : Atom) :
    sameMorkSupportAtom left right = true ↔
      morkSupportKey left = morkSupportKey right := by
  simp [sameMorkSupportAtom]

/-- Physical membership is exactly membership of the requested compact key.
This is the quotient-level observation used by the executable carrier; it
does not assert that the representative stored in the list is nominally the
same atom as the query. -/
theorem morkSupportContains_eq_true_iff_key_mem
    (support : List Atom) (atom : Atom) :
    morkSupportContains support atom = true ↔
      morkSupportKey atom ∈ support.map morkSupportKey := by
  unfold morkSupportContains morkSupportFind?
  rw [List.find?_isSome]
  constructor
  · rintro ⟨candidate, member, matched⟩
    have keysEqual :=
      (sameMorkSupportAtom_eq_true_iff candidate atom).1 matched
    exact keysEqual ▸ List.mem_map_of_mem member
  · intro keyMember
    obtain ⟨candidate, member, keysEqual⟩ := List.mem_map.mp keyMember
    exact ⟨candidate, member,
      (sameMorkSupportAtom_eq_true_iff candidate atom).2 keysEqual⟩

theorem morkSupportContains_morkInsertSupport_self_core
    (support : List Atom) (atom : Atom) :
    morkSupportContains (morkInsertSupport support atom) atom = true := by
  unfold morkInsertSupport
  split
  · assumption
  · unfold morkSupportContains morkSupportFind?
    rw [List.find?_isSome]
    exact ⟨atom, by simp,
      (sameMorkSupportAtom_eq_true_iff atom atom).2 rfl⟩

theorem morkSupportContains_morkInsertSupport_of_contains_core
    (support : List Atom) (inserted candidate : Atom)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkInsertSupport support inserted) candidate =
      true := by
  unfold morkInsertSupport
  split
  · exact present
  · unfold morkSupportContains morkSupportFind? at present ⊢
    obtain ⟨representative, representativeMember, matched⟩ :=
      List.find?_isSome.mp present
    exact List.find?_isSome.mpr
      ⟨representative, List.mem_append_left _ representativeMember, matched⟩

/-- Physical-key presence survives erasure of a different key. -/
theorem morkSupportContains_morkEraseSupport_of_key_ne_core
    (support : List Atom) (removed candidate : Atom)
    (different : morkSupportKey candidate ≠ morkSupportKey removed)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkEraseSupport support removed) candidate = true := by
  unfold morkSupportContains morkSupportFind? at present ⊢
  obtain ⟨representative, representativeMember, matched⟩ :=
    List.find?_isSome.mp present
  have representativeKey :
      morkSupportKey representative = morkSupportKey candidate :=
    (sameMorkSupportAtom_eq_true_iff representative candidate).1 matched
  have survives : representative ∈ morkEraseSupport support removed := by
    apply List.mem_filter.mpr
    refine ⟨representativeMember, ?_⟩
    have keyNe :
        morkSupportKey representative ≠ morkSupportKey removed := by
      simpa [representativeKey] using different
    simp [sameMorkSupportAtom, keyNe]
  exact List.find?_isSome.mpr ⟨representative, survives, matched⟩

/-- Existing physical-key presence survives a support union. -/
theorem morkSupportContains_morkUnionSupport_of_contains_core
    (support staged : List Atom) (candidate : Atom)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkUnionSupport support staged) candidate = true := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkInsertSupport support head)
        (morkSupportContains_morkInsertSupport_of_contains_core support head
          candidate present)

/-- Presence in the staged support is transferred through physical union. -/
theorem morkSupportContains_morkUnionSupport_of_staged_contains_core
    (support staged : List Atom) (candidate : Atom)
    (present : morkSupportContains staged candidate = true) :
    morkSupportContains (morkUnionSupport support staged) candidate = true := by
  have keyMember : morkSupportKey candidate ∈ staged.map morkSupportKey :=
    (morkSupportContains_eq_true_iff_key_mem staged candidate).1 present
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simp at keyMember
  | cons head tail induction =>
      simp only [List.map_cons, List.mem_cons] at keyMember
      simp only [List.foldl_cons]
      rcases keyMember with headKey | tailKey
      · apply morkSupportContains_morkUnionSupport_of_contains_core
        have insertedHead :=
          morkSupportContains_morkInsertSupport_self_core support head
        rw [morkSupportContains_eq_true_iff_key_mem] at insertedHead ⊢
        simpa [headKey] using insertedHead
      · apply induction (morkInsertSupport support head)
        exact (morkSupportContains_eq_true_iff_key_mem tail candidate).2 tailKey
        exact tailKey

theorem mem_morkInsertSupport_of_mem_core
    {support : List Atom} {candidate inserted : Atom}
    (member : candidate ∈ support) :
    candidate ∈ morkInsertSupport support inserted := by
  unfold morkInsertSupport
  split
  · exact member
  · exact List.mem_append_left _ member

theorem mem_morkUnionSupport_of_mem_left_core
    {support staged : List Atom} {candidate : Atom}
    (member : candidate ∈ support) :
    candidate ∈ morkUnionSupport support staged := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => exact member
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (mem_morkInsertSupport_of_mem_core member)

/-- Quotient membership becomes exact nominal membership when every stored
representative is already known to come from one compact-key duplicate-free
reference presentation.  This is the bridge between MORK's alpha-quotiented
storage and source-derived exact rows. -/
theorem mem_of_morkSupportContains_of_reference
    {support reference : List Atom} {atom : Atom}
    (referenceNodup : MorkSupportNodup reference)
    (atomMember : atom ∈ reference)
    (supportWithin : ∀ candidate ∈ support, candidate ∈ reference)
    (present : morkSupportContains support atom = true) :
    atom ∈ support := by
  unfold morkSupportContains morkSupportFind? at present
  obtain ⟨candidate, candidateMember, matched⟩ :=
    List.find?_isSome.mp present
  have candidateReference : candidate ∈ reference :=
    supportWithin candidate candidateMember
  have keysEqual :
      morkSupportKey candidate = morkSupportKey atom :=
    (sameMorkSupportAtom_eq_true_iff candidate atom).1 matched
  have exactAtom : candidate = atom :=
    morkSupportKey_injective_on referenceNodup candidateReference atomMember
      keysEqual
  simpa [exactAtom] using candidateMember

/-- Removing a physical key removes the requested atom itself, independently
of which representative was present before removal. -/
theorem not_mem_morkEraseSupport_self (support : List Atom) (atom : Atom) :
    atom ∉ morkEraseSupport support atom := by
  intro member
  have rejected := (List.mem_filter.mp member).2
  simp [sameMorkSupportAtom] at rejected

/-- A removed physical key is absent from the resulting support lookup. -/
@[simp] theorem morkSupportContains_morkEraseSupport_self
    (support : List Atom) (atom : Atom) :
    morkSupportContains (morkEraseSupport support atom) atom = false := by
  simp [morkSupportContains, morkSupportFind?, morkEraseSupport,
    List.find?_eq_none, sameMorkSupportAtom]

/-- Read-copy insertion after physical removal appends one exact selected
representative. -/
theorem morkInsertSupport_morkEraseSupport_self
    (support : List Atom) (atom : Atom) :
    morkInsertSupport (morkEraseSupport support atom) atom =
      morkEraseSupport support atom ++ [atom] := by
  simp [morkInsertSupport]

/-- If a physical key is absent, it is absent from the mapped key list. -/
theorem morkSupportKey_not_mem_of_contains_eq_false
    (support : List Atom) (atom : Atom)
    (absent : morkSupportContains support atom = false) :
    morkSupportKey atom ∉ support.map morkSupportKey := by
  have notFound :
      support.find? (fun candidate => sameMorkSupportAtom candidate atom) =
        none := by
    simpa [morkSupportContains, morkSupportFind?] using absent
  intro member
  rcases List.mem_map.mp member with ⟨candidate, candidateMember, equal⟩
  have rejected := List.find?_eq_none.mp notFound candidate candidateMember
  apply rejected
  exact (sameMorkSupportAtom_eq_true_iff candidate atom).2 equal

/-- Physical-key insertion preserves duplicate freedom. -/
theorem morkInsertSupport_nodup (support : List Atom) (atom : Atom)
    (nodup : MorkSupportNodup support) :
    MorkSupportNodup (morkInsertSupport support atom) := by
  unfold morkInsertSupport
  split
  · exact nodup
  · rename_i absent
    unfold MorkSupportNodup at nodup ⊢
    rw [List.map_append]
    exact nodup.append
      (by simp)
      (by
        intro key keyMember singletonMember
        have keyEq : key = morkSupportKey atom := by
          simpa using singletonMember
        rw [keyEq] at keyMember
        exact morkSupportKey_not_mem_of_contains_eq_false support atom
          (Bool.eq_false_of_not_eq_true absent) keyMember)

/-- Physical-key removal preserves duplicate freedom at the compact-support
level.  This is stronger than ordinary list duplicate freedom: two distinct
atoms that MORK identifies physically cannot both survive. -/
theorem morkEraseSupport_nodup (support : List Atom) (atom : Atom)
    (nodup : MorkSupportNodup support) :
    MorkSupportNodup (morkEraseSupport support atom) := by
  unfold MorkSupportNodup at nodup ⊢
  exact nodup.sublist (List.filter_sublist.map morkSupportKey)

/-- On a physically duplicate-free support, removing a represented atom by
its MORK key is exactly ordinary one-occurrence erasure. -/
theorem morkEraseSupport_eq_erase_of_mem
    (support : List Atom) (atom : Atom)
    (listNodup : support.Nodup) (morkNodup : MorkSupportNodup support)
    (member : atom ∈ support) :
    morkEraseSupport support atom = support.erase atom := by
  rw [morkEraseSupport, listNodup.erase_eq_filter]
  apply List.filter_congr
  intro candidate candidateMember
  by_cases equal : candidate = atom
  · subst candidate
    simp [sameMorkSupportAtom]
  · have keysDifferent :
        morkSupportKey candidate ≠ morkSupportKey atom := by
      intro keysEqual
      exact equal
        (morkSupportKey_injective_on morkNodup candidateMember member keysEqual)
    simp [sameMorkSupportAtom, equal, keysDifferent]

/-- Physical support union preserves compact-key duplicate freedom. -/
theorem morkUnionSupport_nodup (support staged : List Atom)
    (nodup : MorkSupportNodup support) :
    MorkSupportNodup (morkUnionSupport support staged) := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkInsertSupport support head)
        (morkInsertSupport_nodup support head nodup)

/-- Physical support subtraction preserves compact-key duplicate freedom. -/
theorem morkSubtractSupport_nodup (support staged : List Atom)
    (nodup : MorkSupportNodup support) :
    MorkSupportNodup (morkSubtractSupport support staged) := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkEraseSupport support head)
        (morkEraseSupport_nodup support head nodup)

/-- Physical-key insertion also preserves ordinary list duplicate freedom. -/
theorem morkInsertSupport_list_nodup (support : List Atom) (atom : Atom)
    (nodup : support.Nodup) :
    (morkInsertSupport support atom).Nodup := by
  unfold morkInsertSupport
  split
  · exact nodup
  · rename_i absent
    apply nodup.append
    · simp
    · intro candidate candidateMember singletonMember
      have equal : candidate = atom := by simpa using singletonMember
      subst candidate
      have keyMember : morkSupportKey atom ∈ support.map morkSupportKey :=
        List.mem_map_of_mem candidateMember
      exact morkSupportKey_not_mem_of_contains_eq_false support atom
        (Bool.eq_false_of_not_eq_true absent) keyMember

/-- Physical-key removal preserves ordinary duplicate freedom. -/
theorem morkEraseSupport_list_nodup (support : List Atom) (atom : Atom)
    (nodup : support.Nodup) :
    (morkEraseSupport support atom).Nodup := by
  exact nodup.filter _

/-- Physical support union preserves ordinary duplicate freedom even when
the staged rows themselves contain repeated representatives. -/
theorem morkUnionSupport_list_nodup (support staged : List Atom)
    (nodup : support.Nodup) :
    (morkUnionSupport support staged).Nodup := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkInsertSupport support head)
        (morkInsertSupport_list_nodup support head nodup)

/-- Physical support subtraction preserves ordinary duplicate freedom. -/
theorem morkSubtractSupport_list_nodup (support staged : List Atom)
    (nodup : support.Nodup) :
    (morkSubtractSupport support staged).Nodup := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkEraseSupport support head)
        (morkEraseSupport_list_nodup support head nodup)

/-! ## Atom-local invariant transport -/

/-- Physical-key insertion preserves every property of the existing support
when the candidate atom itself has that property.  If its key is already
represented, no new atom is inserted. -/
theorem morkInsertSupport_atomsWithin
    (property : Atom → Prop) (support : List Atom) (atom : Atom)
    (sourceWithin : AtomsWithin property support)
    (atomProperty : property atom) :
    AtomsWithin property (morkInsertSupport support atom) := by
  unfold morkInsertSupport
  split
  · exact sourceWithin
  · intro candidate member
    rw [List.mem_append] at member
    rcases member with prior | inserted
    · exact sourceWithin candidate prior
    · have equal : candidate = atom := by simpa using inserted
      subst candidate
      exact atomProperty

/-- Removing a physical key cannot introduce a counterexample to an
atom-local invariant. -/
theorem morkEraseSupport_atomsWithin
    (property : Atom → Prop) (support : List Atom) (atom : Atom)
    (sourceWithin : AtomsWithin property support) :
    AtomsWithin property (morkEraseSupport support atom) := by
  intro candidate member
  exact sourceWithin candidate (List.mem_filter.mp member).1

/-- Physical support union preserves an atom-local invariant supplied for
both its live and staged inputs. -/
theorem morkUnionSupport_atomsWithin
    (property : Atom → Prop) (support staged : List Atom)
    (sourceWithin : AtomsWithin property support)
    (stagedWithin : AtomsWithin property staged) :
    AtomsWithin property (morkUnionSupport support staged) := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      · exact morkInsertSupport_atomsWithin property support head
          sourceWithin (stagedWithin head (by simp))
      · intro atom member
        exact stagedWithin atom (by simp [member])

/-- Physical support subtraction preserves every atom-local invariant of the
live support. -/
theorem morkSubtractSupport_atomsWithin
    (property : Atom → Prop) (support staged : List Atom)
    (sourceWithin : AtomsWithin property support) :
    AtomsWithin property (morkSubtractSupport support staged) := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkEraseSupport support head)
        (morkEraseSupport_atomsWithin property support head sourceWithin)

/-- Compact-key extrema contain only atoms from the staged support. -/
theorem compactExtremaList_atomsWithin
    (property : Atom → Prop) (least : Bool) (count : Nat)
    (staged : List Atom) (stagedWithin : AtomsWithin property staged) :
    AtomsWithin property (compactExtremaList least count staged) := by
  intro atom member
  apply stagedWithin atom
  have sortedMember := List.mem_of_mem_take member
  simpa [compactExtremaList] using sortedMember

/-! ## Rule-scoped matching and sinks -/

/-- Computable explicit-factor matching with compact-key membership and
removal for equality and inequality factors. -/
def cMatchSourceFactorMork (substitution : Subst) (space : List Atom) :
    SourceFactor → List (Subst × Atom)
  | .btm pattern =>
      space.filterMap fun atom =>
        (Conformance.Computable.cmatchAtom substitution pattern atom).map
          (·, atom)
  | .eqConstraint pattern witness =>
      let target := applySubst substitution pattern
      match morkSupportFind? space target with
      | none => []
      | some representative =>
          match Conformance.Computable.cmatchAtom substitution witness
              representative with
          | some next => [(next, representative)]
          | none => []
  | .neqConstraint pattern witness =>
      let target := applySubst substitution pattern
      (morkEraseSupport space target).filterMap fun atom =>
        (Conformance.Computable.cmatchAtom substitution witness atom).map
          (·, atom)

/-- Relational product of explicit factors. -/
def cMatchSourceFactorsMork (substitution : Subst) (space : List Atom) :
    List SourceFactor → List (Subst × List Atom)
  | [] => [(substitution, [])]
  | factor :: rest =>
      (cMatchSourceFactorMork substitution space factor).flatMap fun
          (next, witness) =>
        (cMatchSourceFactorsMork next space rest).map fun (final, witnesses) =>
          (final, witness :: witnesses)

/-- Match an input with compact-key factor semantics. -/
def cMatchInputSpecMork (substitution : Subst) (space : List Atom) :
    InputSpec → List (Subst × List Atom)
  | .compat pattern =>
      Conformance.Computable.cmatchPattern substitution space pattern
  | .explicit factors =>
      cMatchSourceFactorsMork substitution space factors

/-- Stage one output using rule-scoped coverage and physical support. -/
def stageRuleScopedSink (input : InputSpec) (sink : Sink)
    (staged : List Atom) (substitution : Subst) : List Atom :=
  match instantiateRuleTemplateAtom? input substitution sink.atom with
  | none => staged
  | some instantiated => morkInsertSupport staged instantiated

/-- Finalize one independently staged support-valued sink. -/
def finalizeRuleScopedSink (sink : Sink) (staged space : List Atom) :
    List Atom :=
  match sink with
  | .add _ => morkUnionSupport space staged
  | .remove _ => morkSubtractSupport space staged
  | .head count _ =>
      morkUnionSupport space (compactExtremaList true count staged)
  | .tail count _ =>
      morkUnionSupport space (compactExtremaList false count staged)

/-- Apply all sinks, staging all matcher rows before each finalization. -/
def cApplyRuleScopedSinkBatch (input : InputSpec) (rows : List Subst) :
    List Atom → List Sink → List Atom
  | space, [] => space
  | space, sink :: rest =>
      let staged := rows.foldl (stageRuleScopedSink input sink) []
      cApplyRuleScopedSinkBatch input rows
        (finalizeRuleScopedSink sink staged space) rest

/-- Sink-batch execution respects list concatenation.  This exposes an
authored administrative prefix and a semantically significant suffix without
reimplementing either part. -/
theorem cApplyRuleScopedSinkBatch_append
    (input : InputSpec) (rows : List Subst) (space : List Atom) :
    ∀ beforeSinks afterSinks,
      cApplyRuleScopedSinkBatch input rows space (beforeSinks ++ afterSinks) =
        cApplyRuleScopedSinkBatch input rows
          (cApplyRuleScopedSinkBatch input rows space beforeSinks) afterSinks
  | [], _ => rfl
  | sink :: rest, afterSinks => by
      simp only [List.cons_append, cApplyRuleScopedSinkBatch]
      exact cApplyRuleScopedSinkBatch_append input rows
        (finalizeRuleScopedSink sink
          (rows.foldl (stageRuleScopedSink input sink) []) space)
        rest afterSinks

/-- Apply one complete rule-scoped template. -/
def cApplyRuleScopedTemplate (input : InputSpec) (space : List Atom)
    (rows : List Subst) (template : Template) : List Atom :=
  cApplyRuleScopedSinkBatch input rows space template.sinks

/-- With no matcher rows, every staged rule-scoped sink is empty and the
complete sink batch leaves the live physical support unchanged. -/
theorem cApplyRuleScopedSinkBatch_nil (input : InputSpec)
    (space : List Atom) (sinks : List Sink) :
    cApplyRuleScopedSinkBatch input [] space sinks = space := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [cApplyRuleScopedSinkBatch, List.foldl_nil]
      have emptyFinalize : finalizeRuleScopedSink sink [] space = space := by
        cases sink <;>
          simp [finalizeRuleScopedSink, morkUnionSupport,
            morkSubtractSupport, compactExtremaList]
      rw [emptyFinalize]
      exact induction space

/-- A complete rule-scoped sink batch preserves ordinary list duplicate
freedom.  Every adding branch uses physical-key insertion, and every removing
branch is a filter. -/
theorem cApplyRuleScopedSinkBatch_list_nodup
    (input : InputSpec) (rows : List Subst) :
    ∀ (space : List Atom) (sinks : List Sink),
      space.Nodup → (cApplyRuleScopedSinkBatch input rows space sinks).Nodup
  | space, [], nodup => nodup
  | space, sink :: rest, nodup => by
      simp only [cApplyRuleScopedSinkBatch]
      apply cApplyRuleScopedSinkBatch_list_nodup input rows _ rest
      cases sink with
      | add atom =>
          exact morkUnionSupport_list_nodup space _ nodup
      | remove atom =>
          exact morkSubtractSupport_list_nodup space _ nodup
      | head count atom =>
          exact morkUnionSupport_list_nodup space _ nodup
      | tail count atom =>
          exact morkUnionSupport_list_nodup space _ nodup

/-- Applying one rule-scoped template preserves ordinary list duplicate
freedom. -/
theorem cApplyRuleScopedTemplate_list_nodup
    (input : InputSpec) (space : List Atom) (rows : List Subst)
    (template : Template) (nodup : space.Nodup) :
    (cApplyRuleScopedTemplate input space rows template).Nodup := by
  exact cApplyRuleScopedSinkBatch_list_nodup input rows space template.sinks
    nodup

/-- A complete rule-scoped sink batch preserves physical compact-key
duplicate freedom.  This is the storage invariant used by MORK execution,
where alpha-equivalent executable patterns share one support identity. -/
theorem cApplyRuleScopedSinkBatch_mork_nodup
    (input : InputSpec) (rows : List Subst) :
    ∀ (space : List Atom) (sinks : List Sink),
      MorkSupportNodup space →
        MorkSupportNodup
          (cApplyRuleScopedSinkBatch input rows space sinks)
  | space, [], nodup => nodup
  | space, sink :: rest, nodup => by
      simp only [cApplyRuleScopedSinkBatch]
      apply cApplyRuleScopedSinkBatch_mork_nodup input rows _ rest
      cases sink with
      | add atom => exact morkUnionSupport_nodup space _ nodup
      | remove atom => exact morkSubtractSupport_nodup space _ nodup
      | head count atom => exact morkUnionSupport_nodup space _ nodup
      | tail count atom => exact morkUnionSupport_nodup space _ nodup

/-- Applying one rule-scoped template preserves physical compact-key
duplicate freedom. -/
theorem cApplyRuleScopedTemplate_mork_nodup
    (input : InputSpec) (space : List Atom) (rows : List Subst)
    (template : Template) (nodup : MorkSupportNodup space) :
    MorkSupportNodup
      (cApplyRuleScopedTemplate input space rows template) := by
  exact cApplyRuleScopedSinkBatch_mork_nodup input rows space template.sinks
    nodup

/-! ## Exact-atom no-invention for rule-scoped support -/

/-- Any exact atom present after physical insertion was already present or is
the inserted representative.  The converse is intentionally not claimed:
an alpha-equivalent key already in the support can suppress insertion of a
different nominal atom. -/
theorem mem_morkInsertSupport_cases
    {support : List Atom} {inserted candidate : Atom}
    (member : candidate ∈ morkInsertSupport support inserted) :
    candidate ∈ support ∨ candidate = inserted := by
  unfold morkInsertSupport at member
  split at member
  · exact Or.inl member
  · exact (List.mem_append.mp member).elim Or.inl
      (fun singleton => Or.inr (List.mem_singleton.mp singleton))

/-- Any exact atom present after a physical union came from the original or
staged presentation. -/
theorem mem_morkUnionSupport_cases
    {support staged : List Atom} {candidate : Atom}
    (member : candidate ∈ morkUnionSupport support staged) :
    candidate ∈ support ∨ candidate ∈ staged := by
  unfold morkUnionSupport at member
  induction staged generalizing support with
  | nil => exact Or.inl member
  | cons head tail induction =>
      rcases induction member with later | tailMember
      · rcases mem_morkInsertSupport_cases later with original | rfl
        · exact Or.inl original
        · exact Or.inr (by simp)
      · exact Or.inr (by simp [tailMember])

/-- Physical subtraction cannot invent an exact atom. -/
theorem mem_morkSubtractSupport_source
    {support staged : List Atom} {candidate : Atom}
    (member : candidate ∈ morkSubtractSupport support staged) :
    candidate ∈ support := by
  unfold morkSubtractSupport at member
  induction staged generalizing support with
  | nil => exact member
  | cons head tail induction =>
      exact (List.mem_filter.mp (induction member)).1

/-- Subtracting a staged physical identity removes its exact representative,
even when the staged batch contains the representative after other rows. -/
theorem not_mem_morkSubtractSupport_of_mem_staged
    (support staged : List Atom) (candidate : Atom)
    (member : candidate ∈ staged) :
    candidate ∉ morkSubtractSupport support staged := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · intro survived
        exact not_mem_morkEraseSupport_self support candidate
          (mem_morkSubtractSupport_source survived)
      · exact induction (morkEraseSupport support head) tailMember

/-- Exact membership survives physical subtraction when every staged key is
different from the candidate key. -/
theorem mem_morkSubtractSupport_of_mem_of_keys_ne
    (support staged : List Atom) (candidate : Atom)
    (member : candidate ∈ support)
    (different : ∀ removed ∈ staged,
      morkSupportKey candidate ≠ morkSupportKey removed) :
    candidate ∈ morkSubtractSupport support staged := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction (morkEraseSupport support head)
      · apply List.mem_filter.mpr
        exact ⟨member, by
          simp [sameMorkSupportAtom, different head (by simp)]⟩
      · intro removed removedMember
        exact different removed (by simp [removedMember])

/-- Physical-key presence survives subtraction when every staged removal key
is different from the candidate key. -/
theorem morkSupportContains_morkSubtractSupport_of_keys_ne_core
    (support staged : List Atom) (candidate : Atom)
    (different : ∀ removed ∈ staged,
      morkSupportKey candidate ≠ morkSupportKey removed)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkSubtractSupport support staged) candidate = true := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction
      · intro removed removedMember
        exact different removed (by simp [removedMember])
      · exact morkSupportContains_morkEraseSupport_of_key_ne_core support head
          candidate (different head (by simp)) present

/-- Staging any representative of a physical key makes subtraction remove
every exact atom with that key. -/
theorem not_mem_morkSubtractSupport_of_contains_staged
    (support staged : List Atom) (candidate : Atom)
    (present : morkSupportContains staged candidate = true) :
    candidate ∉ morkSubtractSupport support staged := by
  have keyMember :
      morkSupportKey candidate ∈ staged.map morkSupportKey :=
    (morkSupportContains_eq_true_iff_key_mem staged candidate).1 present
  have removeOfKeyMember : ∀ (remaining : List Atom) (initial : List Atom),
      morkSupportKey candidate ∈ remaining.map morkSupportKey →
        candidate ∉ remaining.foldl morkEraseSupport initial := by
    intro remaining
    induction remaining with
    | nil => simp
    | cons head tail induction =>
        intro initial member
        simp only [List.foldl_cons, List.map_cons, List.mem_cons] at member ⊢
        rcases member with headKey | tailKey
        · intro survived
          have beforeTail : candidate ∈ morkEraseSupport initial head :=
            mem_morkSubtractSupport_source survived
          have accepted := (List.mem_filter.mp beforeTail).2
          have equal : morkSupportKey candidate = morkSupportKey head := headKey
          simp [sameMorkSupportAtom, equal] at accepted
        · exact induction (morkEraseSupport initial head) tailKey
  exact removeOfKeyMember staged support keyMember

/-- Exact atoms staged for one sink come from an actual matcher row and its
rule-scoped instantiation. -/
theorem mem_foldl_stageRuleScopedSink_cases
    (input : InputSpec) (sink : Sink) (rows : List Subst)
    (initial : List Atom) {candidate : Atom}
    (member : candidate ∈ rows.foldl (stageRuleScopedSink input sink) initial) :
    candidate ∈ initial ∨
      ∃ substitution ∈ rows,
        instantiateRuleTemplateAtom? input substitution sink.atom =
          some candidate := by
  induction rows generalizing initial with
  | nil => exact Or.inl member
  | cons substitution rest induction =>
      simp only [List.foldl_cons] at member
      rcases induction (stageRuleScopedSink input sink initial substitution)
          member with staged | later
      · unfold stageRuleScopedSink at staged
        cases instantiated :
            instantiateRuleTemplateAtom? input substitution sink.atom with
        | none =>
            simp [instantiated] at staged
            exact Or.inl staged
        | some atom =>
            simp [instantiated] at staged
            rcases mem_morkInsertSupport_cases staged with prior | rfl
            · exact Or.inl prior
            · exact Or.inr ⟨substitution, by simp, instantiated⟩
      · rcases later with ⟨laterSubstitution, laterMember, exact⟩
        exact Or.inr ⟨laterSubstitution, by simp [laterMember], exact⟩

/-- If one matcher row instantiates a sink to a candidate, staging the whole
matcher relation contains that candidate by physical identity. -/
theorem morkSupportContains_foldl_stageRuleScopedSink_of_row
    (input : InputSpec) (sink : Sink) (rows : List Subst)
    (candidate : Atom) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateRuleTemplateAtom? input substitution sink.atom =
        some candidate) :
    morkSupportContains
      (rows.foldl (stageRuleScopedSink input sink) []) candidate = true := by
  have persists : ∀ (remaining : List Subst) (initial : List Atom),
      morkSupportContains initial candidate = true →
        morkSupportContains
          (remaining.foldl (stageRuleScopedSink input sink) initial)
          candidate = true := by
    intro remaining
    induction remaining with
    | nil => exact fun _ present => present
    | cons head tail induction =>
        intro initial present
        simp only [List.foldl_cons]
        apply induction
        unfold stageRuleScopedSink
        split
        · exact present
        · exact morkSupportContains_morkInsertSupport_of_contains_core
            initial _ candidate present
  have eventually : ∀ (remaining : List Subst) (initial : List Atom),
      substitution ∈ remaining →
        morkSupportContains
          (remaining.foldl (stageRuleScopedSink input sink) initial)
          candidate = true := by
    intro remaining
    induction remaining with
    | nil => simp
    | cons head tail induction =>
        intro initial member
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp member with rfl | tailMember
        · apply persists
          unfold stageRuleScopedSink
          rw [instantiates]
          exact morkSupportContains_morkInsertSupport_self_core initial candidate
        · exact induction (stageRuleScopedSink input sink initial head)
            tailMember
  exact eventually rows [] rowMember

/-- A matched rule-scoped remove eliminates its exact instantiated row from
the physical carrier. -/
theorem not_mem_finalizeRuleScopedSink_remove_of_row
    (input : InputSpec) (rows : List Subst) (space : List Atom)
    (authored candidate : Atom) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateRuleTemplateAtom? input substitution authored =
        some candidate) :
    candidate ∉ finalizeRuleScopedSink (.remove authored)
      (rows.foldl (stageRuleScopedSink input (.remove authored)) []) space := by
  change candidate ∉ morkSubtractSupport space
    (rows.foldl (stageRuleScopedSink input (.remove authored)) [])
  apply not_mem_morkSubtractSupport_of_contains_staged
  have foldPreserves : ∀ (remaining : List Subst) (initial : List Atom),
      morkSupportContains initial candidate = true →
        morkSupportContains
          (remaining.foldl
            (stageRuleScopedSink input (.remove authored)) initial)
          candidate = true := by
    intro remaining
    induction remaining with
    | nil => exact fun _ present => present
    | cons head tail induction =>
        intro initial present
        simp only [List.foldl_cons]
        apply induction
        unfold stageRuleScopedSink
        split
        · exact present
        · exact morkSupportContains_morkInsertSupport_of_contains_core
            initial _ candidate present
  have foldEventually : ∀ (remaining : List Subst) (initial : List Atom),
      substitution ∈ remaining →
        morkSupportContains
          (remaining.foldl
            (stageRuleScopedSink input (.remove authored)) initial)
          candidate = true := by
    intro remaining
    induction remaining with
    | nil => simp
    | cons head tail induction =>
        intro initial member
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp member with rfl | tailMember
        · apply foldPreserves
          unfold stageRuleScopedSink
          change morkSupportContains
            (match instantiateRuleTemplateAtom? input substitution authored with
            | none => initial
            | some instantiated => morkInsertSupport initial instantiated)
            candidate = true
          rw [instantiates]
          exact morkSupportContains_morkInsertSupport_self_core initial candidate
        · exact induction
            (stageRuleScopedSink input (.remove authored) initial head)
            tailMember
  exact foldEventually rows [] rowMember

/-- Once a physical row is absent, remove sinks preserve absence and add
sinks preserve it when no matcher row instantiates that exact row. -/
theorem not_mem_cApplyRuleScopedSinkBatch_of_remove_or_nonproducing_add
    (input : InputSpec) (rows : List Subst)
    {space : List Atom} {sinks : List Sink} {candidate : Atom}
    (safe : ∀ sink ∈ sinks,
      (∃ authored, sink = .remove authored) ∨
        ∃ authored, sink = .add authored ∧
          ∀ substitution ∈ rows,
            instantiateRuleTemplateAtom? input substitution authored ≠
              some candidate)
    (absent : candidate ∉ space) :
    candidate ∉ cApplyRuleScopedSinkBatch input rows space sinks := by
  induction sinks generalizing space with
  | nil => exact absent
  | cons sink rest induction =>
      have restSafe : ∀ later ∈ rest,
          (∃ authored, later = .remove authored) ∨
            ∃ authored, later = .add authored ∧
              ∀ substitution ∈ rows,
                instantiateRuleTemplateAtom? input substitution authored ≠
                  some candidate := by
        intro later laterMember
        exact safe later (by simp [laterMember])
      rcases safe sink (by simp) with remove | add
      · obtain ⟨authored, rfl⟩ := remove
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        intro member
        exact absent (mem_morkSubtractSupport_source member)
      · obtain ⟨authored, rfl, nonproducing⟩ := add
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        intro member
        rcases mem_morkUnionSupport_cases member with original | staged
        · exact absent original
        · rcases mem_foldl_stageRuleScopedSink_cases input (.add authored)
              rows [] staged with impossible | introduced
          · simp at impossible
          · rcases introduced with
              ⟨substitution, substitutionMember, instantiates⟩
            exact nonproducing substitution substitutionMember instantiates

/-- A matched physical remove at any authored position establishes exact
absence when the remaining sinks cannot recreate the removed row. -/
theorem not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
    (input : InputSpec) (rows : List Subst) (space : List Atom)
    (before : List Sink) (authored candidate : Atom) (rest : List Sink)
    (substitution : Subst) (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateRuleTemplateAtom? input substitution authored =
        some candidate)
    (restSafe : ∀ sink ∈ rest,
      (∃ later, sink = .remove later) ∨
        ∃ later, sink = .add later ∧
          ∀ laterSubstitution ∈ rows,
            instantiateRuleTemplateAtom? input laterSubstitution later ≠
              some candidate) :
    candidate ∉ cApplyRuleScopedSinkBatch input rows space
      (before ++ .remove authored :: rest) := by
  induction before generalizing space with
  | nil =>
      simp only [List.nil_append, cApplyRuleScopedSinkBatch]
      exact not_mem_cApplyRuleScopedSinkBatch_of_remove_or_nonproducing_add
        input rows restSafe
          (not_mem_finalizeRuleScopedSink_remove_of_row input rows space
            authored candidate substitution rowMember instantiates)
  | cons sink before induction =>
      simp only [List.cons_append, cApplyRuleScopedSinkBatch]
      exact induction _

/-- Exact membership survives a physical sink batch when additions are
unrestricted and every instantiated remove key differs from the candidate. -/
theorem mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    (input : InputSpec) (rows : List Subst)
    {space : List Atom} {sinks : List Sink} {candidate : Atom}
    (safe : ∀ sink ∈ sinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows, ∀ removed,
            instantiateRuleTemplateAtom? input substitution authored =
                some removed →
              morkSupportKey candidate ≠ morkSupportKey removed)
    (present : candidate ∈ space) :
    candidate ∈ cApplyRuleScopedSinkBatch input rows space sinks := by
  induction sinks generalizing space with
  | nil => exact present
  | cons sink rest induction =>
      have restSafe : ∀ later ∈ rest,
          (∃ authored, later = .add authored) ∨
            ∃ authored, later = .remove authored ∧
              ∀ substitution ∈ rows, ∀ removed,
                instantiateRuleTemplateAtom? input substitution authored =
                    some removed →
                  morkSupportKey candidate ≠ morkSupportKey removed := by
        intro later laterMember
        exact safe later (by simp [laterMember])
      rcases safe sink (by simp) with add | remove
      · obtain ⟨authored, rfl⟩ := add
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        exact mem_morkUnionSupport_of_mem_left_core present
      · obtain ⟨authored, rfl, nonremoving⟩ := remove
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        apply mem_morkSubtractSupport_of_mem_of_keys_ne _ _ candidate present
        intro removed removedMember
        rcases mem_foldl_stageRuleScopedSink_cases input (.remove authored)
            rows [] removedMember with impossible | introduced
        · simp at impossible
        · rcases introduced with
            ⟨substitution, substitutionMember, instantiated⟩
          exact nonremoving substitution substitutionMember removed instantiated

/-- Physical-key presence survives a rule-scoped sink batch when additions
are unrestricted and every instantiated remove key is different. -/
theorem morkSupportContains_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    (input : InputSpec) (rows : List Subst)
    {space : List Atom} {sinks : List Sink} {candidate : Atom}
    (safe : ∀ sink ∈ sinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows, ∀ removed,
            instantiateRuleTemplateAtom? input substitution authored =
                some removed →
              morkSupportKey candidate ≠ morkSupportKey removed)
    (present : morkSupportContains space candidate = true) :
    morkSupportContains
      (cApplyRuleScopedSinkBatch input rows space sinks) candidate = true := by
  induction sinks generalizing space with
  | nil => exact present
  | cons sink rest induction =>
      have restSafe : ∀ later ∈ rest,
          (∃ authored, later = .add authored) ∨
            ∃ authored, later = .remove authored ∧
              ∀ substitution ∈ rows, ∀ removed,
                instantiateRuleTemplateAtom? input substitution authored =
                    some removed →
                  morkSupportKey candidate ≠ morkSupportKey removed := by
        intro later laterMember
        exact safe later (by simp [laterMember])
      rcases safe sink (by simp) with add | remove
      · obtain ⟨authored, rfl⟩ := add
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        exact morkSupportContains_morkUnionSupport_of_contains_core _ _ _
          present
      · obtain ⟨authored, rfl, nonremoving⟩ := remove
        simp only [cApplyRuleScopedSinkBatch]
        apply induction restSafe
        apply morkSupportContains_morkSubtractSupport_of_keys_ne_core
        · intro removed removedMember
          rcases mem_foldl_stageRuleScopedSink_cases input (.remove authored)
              rows [] removedMember with impossible | introduced
          · simp at impossible
          · rcases introduced with
              ⟨substitution, substitutionMember, instantiated⟩
            exact nonremoving substitution substitutionMember removed
              instantiated
        · exact present

/-- One authored add establishes physical-key presence through the rest of a
sink batch whenever later removes cannot target that key. -/
theorem morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
    (input : InputSpec) (rows : List Subst) (space : List Atom)
    (before : List Sink) (authored candidate : Atom) (rest : List Sink)
    (substitution : Subst) (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateRuleTemplateAtom? input substitution authored =
        some candidate)
    (restSafe : ∀ sink ∈ rest,
      (∃ later, sink = .add later) ∨
        ∃ later, sink = .remove later ∧
          ∀ laterSubstitution ∈ rows, ∀ removed,
            instantiateRuleTemplateAtom? input laterSubstitution later =
                some removed →
              morkSupportKey candidate ≠ morkSupportKey removed) :
    morkSupportContains
      (cApplyRuleScopedSinkBatch input rows space
        (before ++ .add authored :: rest)) candidate = true := by
  induction before generalizing space with
  | nil =>
      simp only [List.nil_append, cApplyRuleScopedSinkBatch]
      apply
        morkSupportContains_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
          input rows restSafe
      apply morkSupportContains_morkUnionSupport_of_staged_contains_core
      exact morkSupportContains_foldl_stageRuleScopedSink_of_row input
        (.add authored) rows candidate substitution rowMember instantiates
  | cons sink before induction =>
      simp only [List.cons_append, cApplyRuleScopedSinkBatch]
      exact induction _

/-- Atoms genuinely introduced by rule-scoped add sinks.  The relation names
the authored sink, matcher row, and exact instantiated representative. -/
def RuleScopedAddedAtom (input : InputSpec) (rows : List Subst)
    (sinks : List Sink) (atom : Atom) : Prop :=
  ∃ sink ∈ sinks, ∃ authored,
    sink = .add authored ∧
      ∃ substitution ∈ rows,
        instantiateRuleTemplateAtom? input substitution authored = some atom

/-- In an add/remove-only rule-scoped batch, every surviving exact atom was
already in the input or was instantiated by an authored add sink. -/
theorem mem_cApplyRuleScopedTemplate_of_supportSet
    (input : InputSpec) (space : List Atom) (rows : List Subst)
    (template : Template) (supported : ReflectiveSupportSetTemplate template)
    {candidate : Atom}
    (member : candidate ∈ cApplyRuleScopedTemplate input space rows template) :
    candidate ∈ space ∨
      RuleScopedAddedAtom input rows template.sinks candidate := by
  change candidate ∈
    cApplyRuleScopedSinkBatch input rows space template.sinks at member
  have allSupported : ∀ sink ∈ template.sinks,
      ReflectiveSupportSetSink sink := supported
  generalize template.sinks = sinks at allSupported member ⊢
  induction sinks generalizing space with
  | nil => exact Or.inl member
  | cons sink rest induction =>
      simp only [cApplyRuleScopedSinkBatch] at member
      rcases induction
          (finalizeRuleScopedSink sink
            (rows.foldl (stageRuleScopedSink input sink) []) space)
          (fun candidate candidateMember =>
            allSupported candidate
              (List.mem_cons_of_mem sink candidateMember)) member with
        prior | laterAdded
      · cases sink with
        | add authored =>
            change candidate ∈ morkUnionSupport space
              (rows.foldl
                (stageRuleScopedSink input (.add authored)) []) at prior
            rcases mem_morkUnionSupport_cases prior with original | staged
            · exact Or.inl original
            · right
              refine ⟨.add authored, by simp, authored, rfl, ?_⟩
              exact
                (mem_foldl_stageRuleScopedSink_cases input (.add authored)
                  rows [] staged).resolve_left (by simp)
        | remove authored =>
            exact Or.inl (mem_morkSubtractSupport_source prior)
        | head count authored =>
            exact False.elim (allSupported (.head count authored) (by simp))
        | tail count authored =>
            exact False.elim (allSupported (.tail count authored) (by simp))
      · right
        rcases laterAdded with
          ⟨laterSink, laterMember, authored, equal, witness⟩
        exact ⟨laterSink, by simp [laterMember], authored, equal, witness⟩

/-- Every concrete atom instantiated for one rule-scoped sink satisfies the
selected atom-local invariant. -/
def RuleScopedSinkInstantiationsWithin (property : Atom → Prop)
    (input : InputSpec) (rows : List Subst) (sink : Sink) : Prop :=
  ∀ substitution ∈ rows, ∀ atom,
    instantiateRuleTemplateAtom? input substitution sink.atom = some atom →
      property atom

/-- The corresponding obligation for every sink in one template. -/
def RuleScopedTemplateInstantiationsWithin (property : Atom → Prop)
    (input : InputSpec) (rows : List Subst) (template : Template) : Prop :=
  ∀ sink ∈ template.sinks,
    RuleScopedSinkInstantiationsWithin property input rows sink

/-- The exact invariant obligation for one sink: only sinks that can add rows
must justify their instantiated atoms.  A remove sink may name an atom outside
the invariant because that atom is never inserted into the result. -/
def RuleScopedSinkAdditionsWithin (property : Atom → Prop)
    (input : InputSpec) (rows : List Subst) : Sink → Prop
  | .remove _ => True
  | sink => RuleScopedSinkInstantiationsWithin property input rows sink

/-- Exact addition obligations for every sink in one template. -/
def RuleScopedTemplateAdditionsWithin (property : Atom → Prop)
    (input : InputSpec) (rows : List Subst) (template : Template) : Prop :=
  ∀ sink ∈ template.sinks,
    RuleScopedSinkAdditionsWithin property input rows sink

/-- Addition obligations are monotone in their atom-local invariant. -/
theorem RuleScopedTemplateAdditionsWithin.mono
    {property stronger : Atom → Prop}
    {input : InputSpec} {rows : List Subst} {template : Template}
    (implication : ∀ atom, property atom → stronger atom)
    (within :
      RuleScopedTemplateAdditionsWithin property input rows template) :
    RuleScopedTemplateAdditionsWithin stronger input rows template := by
  intro sink sinkMember
  have sinkWithin := within sink sinkMember
  cases sink with
  | remove atom => trivial
  | add atom =>
      intro substitution substitutionMember candidate instantiated
      exact implication candidate
        (sinkWithin substitution substitutionMember candidate instantiated)
  | head count atom =>
      intro substitution substitutionMember candidate instantiated
      exact implication candidate
        (sinkWithin substitution substitutionMember candidate instantiated)
  | tail count atom =>
      intro substitution substitutionMember candidate instantiated
      exact implication candidate
        (sinkWithin substitution substitutionMember candidate instantiated)

/-- Staging one matched substitution preserves an atom-local invariant when
the instantiated output, if any, satisfies it. -/
theorem stageRuleScopedSink_atomsWithin
    (property : Atom → Prop) (input : InputSpec) (sink : Sink)
    (staged : List Atom) (substitution : Subst)
    (stagedWithin : AtomsWithin property staged)
    (instantiatedWithin : ∀ atom,
      instantiateRuleTemplateAtom? input substitution sink.atom = some atom →
        property atom) :
    AtomsWithin property
      (stageRuleScopedSink input sink staged substitution) := by
  unfold stageRuleScopedSink
  cases instantiated :
      instantiateRuleTemplateAtom? input substitution sink.atom with
  | none => exact stagedWithin
  | some atom =>
      exact morkInsertSupport_atomsWithin property staged atom stagedWithin
        (instantiatedWithin atom instantiated)

/-- Staging all matcher rows preserves an atom-local invariant under the
row-indexed instantiation obligation. -/
theorem stageRuleScopedSinkRows_atomsWithin
    (property : Atom → Prop) (input : InputSpec) (sink : Sink)
    (rows : List Subst) (staged : List Atom)
    (stagedWithin : AtomsWithin property staged)
    (instantiatedWithin :
      RuleScopedSinkInstantiationsWithin property input rows sink) :
    AtomsWithin property
      (rows.foldl (stageRuleScopedSink input sink) staged) := by
  induction rows generalizing staged with
  | nil => simpa
  | cons substitution rest induction =>
      simp only [List.foldl_cons]
      apply induction
      · apply stageRuleScopedSink_atomsWithin property input sink staged
          substitution stagedWithin
        intro atom instantiated
        exact instantiatedWithin substitution (by simp) atom instantiated
      · intro later laterMember atom instantiated
        exact instantiatedWithin later (by simp [laterMember]) atom instantiated

/-- Finalizing any supported sink preserves an atom-local invariant of the
live support when every staged atom satisfies it. -/
theorem finalizeRuleScopedSink_atomsWithin
    (property : Atom → Prop) (sink : Sink) (staged space : List Atom)
    (sourceWithin : AtomsWithin property space)
    (stagedWithin : AtomsWithin property staged) :
    AtomsWithin property (finalizeRuleScopedSink sink staged space) := by
  cases sink with
  | add atom =>
      exact morkUnionSupport_atomsWithin property space staged sourceWithin
        stagedWithin
  | remove atom =>
      exact morkSubtractSupport_atomsWithin property space staged sourceWithin
  | head count atom =>
      exact morkUnionSupport_atomsWithin property space
        (compactExtremaList true count staged) sourceWithin
        (compactExtremaList_atomsWithin property true count staged stagedWithin)
  | tail count atom =>
      exact morkUnionSupport_atomsWithin property space
        (compactExtremaList false count staged) sourceWithin
        (compactExtremaList_atomsWithin property false count staged stagedWithin)

/-- Applying a finite rule-scoped sink batch preserves an atom-local invariant
when every atom instantiated by every sink satisfies it. -/
theorem cApplyRuleScopedSinkBatch_atomsWithin
    (property : Atom → Prop) (input : InputSpec) (rows : List Subst)
    (space : List Atom) (sinks : List Sink)
    (sourceWithin : AtomsWithin property space)
    (instantiatedWithin : ∀ sink ∈ sinks,
      RuleScopedSinkInstantiationsWithin property input rows sink) :
    AtomsWithin property
      (cApplyRuleScopedSinkBatch input rows space sinks) := by
  induction sinks generalizing space with
  | nil => exact sourceWithin
  | cons sink rest induction =>
      simp only [cApplyRuleScopedSinkBatch]
      apply induction
      · apply finalizeRuleScopedSink_atomsWithin property sink
          (rows.foldl (stageRuleScopedSink input sink) []) space sourceWithin
        apply stageRuleScopedSinkRows_atomsWithin property input sink rows []
        · intro atom member
          simp at member
        · exact instantiatedWithin sink (by simp)
      · intro later laterMember
        exact instantiatedWithin later (by simp [laterMember])

/-- Applying one complete rule-scoped template preserves an atom-local
invariant under its explicit instantiation obligation. -/
theorem cApplyRuleScopedTemplate_atomsWithin
    (property : Atom → Prop) (input : InputSpec) (space : List Atom)
    (rows : List Subst) (template : Template)
    (sourceWithin : AtomsWithin property space)
    (instantiatedWithin :
      RuleScopedTemplateInstantiationsWithin property input rows template) :
    AtomsWithin property
      (cApplyRuleScopedTemplate input space rows template) := by
  apply cApplyRuleScopedSinkBatch_atomsWithin property input rows space
    template.sinks sourceWithin
  exact instantiatedWithin

/-- Applying a sink batch preserves an atom-local invariant under obligations
for additions only; removal targets need no property. -/
theorem cApplyRuleScopedSinkBatch_atomsWithin_of_additions
    (property : Atom → Prop) (input : InputSpec) (rows : List Subst)
    (space : List Atom) (sinks : List Sink)
    (sourceWithin : AtomsWithin property space)
    (additionsWithin : ∀ sink ∈ sinks,
      RuleScopedSinkAdditionsWithin property input rows sink) :
    AtomsWithin property
      (cApplyRuleScopedSinkBatch input rows space sinks) := by
  induction sinks generalizing space with
  | nil => exact sourceWithin
  | cons sink rest induction =>
      simp only [cApplyRuleScopedSinkBatch]
      apply induction
      · cases sink with
        | add atom =>
            apply finalizeRuleScopedSink_atomsWithin property (.add atom)
              (rows.foldl (stageRuleScopedSink input (.add atom)) []) space
              sourceWithin
            apply stageRuleScopedSinkRows_atomsWithin property input (.add atom)
              rows []
            · intro candidate member
              simp at member
            · simpa [RuleScopedSinkAdditionsWithin] using
                additionsWithin (.add atom) (by simp)
        | remove atom =>
            exact morkSubtractSupport_atomsWithin property space
              (rows.foldl (stageRuleScopedSink input (.remove atom)) [])
              sourceWithin
        | head count atom =>
            apply finalizeRuleScopedSink_atomsWithin property (.head count atom)
              (rows.foldl (stageRuleScopedSink input (.head count atom)) [])
              space sourceWithin
            apply stageRuleScopedSinkRows_atomsWithin property input
              (.head count atom) rows []
            · intro candidate member
              simp at member
            · simpa [RuleScopedSinkAdditionsWithin] using
                additionsWithin (.head count atom) (by simp)
        | tail count atom =>
            apply finalizeRuleScopedSink_atomsWithin property (.tail count atom)
              (rows.foldl (stageRuleScopedSink input (.tail count atom)) [])
              space sourceWithin
            apply stageRuleScopedSinkRows_atomsWithin property input
              (.tail count atom) rows []
            · intro candidate member
              simp at member
            · simpa [RuleScopedSinkAdditionsWithin] using
                additionsWithin (.tail count atom) (by simp)
      · intro later laterMember
        exact additionsWithin later (by simp [laterMember])

/-- One complete template preserves an atom-local invariant under the exact
addition-only obligation. -/
theorem cApplyRuleScopedTemplate_atomsWithin_of_additions
    (property : Atom → Prop) (input : InputSpec) (space : List Atom)
    (rows : List Subst) (template : Template)
    (sourceWithin : AtomsWithin property space)
    (additionsWithin :
      RuleScopedTemplateAdditionsWithin property input rows template) :
    AtomsWithin property
      (cApplyRuleScopedTemplate input space rows template) := by
  exact cApplyRuleScopedSinkBatch_atomsWithin_of_additions property input rows
    space template.sinks sourceWithin additionsWithin

/-- Fire one directive with rule-scoped binders and physical support identity. -/
def cFireRuleScopedSourceExecFact (space : List Atom)
    (directive : SourceExecFact) : List Atom :=
  let live := morkEraseSupport space directive.atom
  let read := morkInsertSupport live directive.atom
  let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
    (substitution, _) => matchSourceGuards substitution directive.rule.guards
  cApplyRuleScopedTemplate directive.rule.input live (rows.map Prod.fst)
    directive.rule.tmpl

/-- A selected rule-scoped directive with no guarded physical matches consumes
only its own executable shell. -/
theorem cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
    (space : List Atom) (directive : SourceExecFact)
    (noMatches :
      (cMatchInputSpecMork []
        (morkInsertSupport (morkEraseSupport space directive.atom)
          directive.atom)
        directive.rule.input).filter (fun (substitution, _) =>
          matchSourceGuards substitution directive.rule.guards) = []) :
    cFireRuleScopedSourceExecFact space directive =
      morkEraseSupport space directive.atom := by
  simp only [cFireRuleScopedSourceExecFact, noMatches, List.map_nil,
    cApplyRuleScopedTemplate]
  exact cApplyRuleScopedSinkBatch_nil directive.rule.input
    (morkEraseSupport space directive.atom) directive.rule.tmpl.sinks

/-- One actual rule-scoped firing preserves ordinary list duplicate freedom. -/
theorem cFireRuleScopedSourceExecFact_list_nodup
    (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup) :
    (cFireRuleScopedSourceExecFact space directive).Nodup := by
  unfold cFireRuleScopedSourceExecFact
  apply cApplyRuleScopedTemplate_list_nodup
  exact morkEraseSupport_list_nodup space directive.atom nodup

/-- One actual rule-scoped firing preserves physical compact-key duplicate
freedom, not merely ordinary atom duplicate freedom. -/
theorem cFireRuleScopedSourceExecFact_mork_nodup
    (space : List Atom) (directive : SourceExecFact)
    (nodup : MorkSupportNodup space) :
    MorkSupportNodup (cFireRuleScopedSourceExecFact space directive) := by
  unfold cFireRuleScopedSourceExecFact
  apply cApplyRuleScopedTemplate_mork_nodup
  exact morkEraseSupport_nodup space directive.atom nodup

/-- One actual rule-scoped directive firing preserves an atom-local invariant
when every concretely instantiated output of the selected matcher rows has the
property.  The executable directive itself is removed before the template is
applied, so the premise concerns only atoms that can remain or be emitted. -/
theorem cFireRuleScopedSourceExecFact_atomsWithin
    (property : Atom → Prop) (space : List Atom)
    (directive : SourceExecFact)
    (sourceWithin : AtomsWithin property space)
    (instantiatedWithin :
      let live := morkEraseSupport space directive.atom
      let read := morkInsertSupport live directive.atom
      let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
        (substitution, _) => matchSourceGuards substitution directive.rule.guards
      RuleScopedTemplateInstantiationsWithin property directive.rule.input
        (rows.map Prod.fst) directive.rule.tmpl) :
    AtomsWithin property (cFireRuleScopedSourceExecFact space directive) := by
  unfold cFireRuleScopedSourceExecFact
  apply cApplyRuleScopedTemplate_atomsWithin
  · exact morkEraseSupport_atomsWithin property space directive.atom
      sourceWithin
  · exact instantiatedWithin

/-- Exact addition-only invariant transport for one selected rule-scoped
directive. -/
theorem cFireRuleScopedSourceExecFact_atomsWithin_of_additions
    (property : Atom → Prop) (space : List Atom)
    (directive : SourceExecFact)
    (sourceWithin : AtomsWithin property space)
    (additionsWithin :
      let live := morkEraseSupport space directive.atom
      let read := morkInsertSupport live directive.atom
      let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
        (substitution, _) => matchSourceGuards substitution directive.rule.guards
      RuleScopedTemplateAdditionsWithin property directive.rule.input
        (rows.map Prod.fst) directive.rule.tmpl) :
    AtomsWithin property (cFireRuleScopedSourceExecFact space directive) := by
  unfold cFireRuleScopedSourceExecFact
  apply cApplyRuleScopedTemplate_atomsWithin_of_additions
  · exact morkEraseSupport_atomsWithin property space directive.atom
      sourceWithin
  · exact additionsWithin

/-- Exact addition-only invariant transport when the invariant begins after
the selected executable shell has been physically erased. -/
theorem cFireRuleScopedSourceExecFact_atomsWithin_of_live_additions
    (property : Atom → Prop) (space : List Atom)
    (directive : SourceExecFact)
    (liveWithin :
      AtomsWithin property (morkEraseSupport space directive.atom))
    (additionsWithin :
      let live := morkEraseSupport space directive.atom
      let read := morkInsertSupport live directive.atom
      let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
        (substitution, _) => matchSourceGuards substitution directive.rule.guards
      RuleScopedTemplateAdditionsWithin property directive.rule.input
        (rows.map Prod.fst) directive.rule.tmpl) :
    AtomsWithin property (cFireRuleScopedSourceExecFact space directive) := by
  unfold cFireRuleScopedSourceExecFact
  exact cApplyRuleScopedTemplate_atomsWithin_of_additions property
    directive.rule.input (morkEraseSupport space directive.atom)
    (((cMatchInputSpecMork []
      (morkInsertSupport (morkEraseSupport space directive.atom)
        directive.atom)
      directive.rule.input).filter fun (substitution, _) =>
        matchSourceGuards substitution directive.rule.guards).map Prod.fst)
    directive.rule.tmpl liveWithin additionsWithin

/-- Least-key work-queue step for the rule-scoped executable semantics. -/
def cRuleScopedSourceWorkQueueStep (policy : UnsupportedExecPolicy)
    (space : List Atom) : Option (List Atom) :=
  match policy with
  | .leaveInert =>
      match selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => none
      | some directive => some (cFireRuleScopedSourceExecFact space directive)
  | .consume =>
      match selectNextScheduled (cRawExecFacts space) with
      | none => none
      | some raw =>
          match decodeSupportedSourceExec raw with
          | some directive =>
              some (cFireRuleScopedSourceExecFact space directive)
          | none => some (morkEraseSupport space raw.atom)

/-- Exact-fuel rule-scoped execution. -/
def cRuleScopedSourceWorkQueueRunN (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom × Nat
  | 0, space => (space, 0)
  | fuel + 1, space =>
      match cRuleScopedSourceWorkQueueStep policy space with
      | none => (space, 0)
      | some next =>
          let (final, used) :=
            cRuleScopedSourceWorkQueueRunN policy fuel next
          (final, used + 1)

/-- The rule-scoped executable semantics as a deterministic GSLT. -/
def ruleScopedNativeListExecGSLT
    (policy : UnsupportedExecPolicy) : GSLT where
  Term := List Atom
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    cRuleScopedSourceWorkQueueStep policy source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem ruleScopedNativeListExecGSLT_step_iff
    (policy : UnsupportedExecPolicy) (source target : List Atom) :
    (ruleScopedNativeListExecGSLT policy).Step source target ↔
      cRuleScopedSourceWorkQueueStep policy source = some target :=
  Iff.rfl

theorem ruleScopedNativeListExecGSLT_step_deterministic
    (policy : UnsupportedExecPolicy) {source left right : List Atom}
    (leftStep : (ruleScopedNativeListExecGSLT policy).Step source left)
    (rightStep : (ruleScopedNativeListExecGSLT policy).Step source right) :
    left = right := by
  exact Option.some.inj (leftStep.symm.trans rightStep)

/-! ## OSLF-generated native types -/

/-- Native types generated by applying OSLF to the actual rule-scoped list
execution GSLT. -/
abbrev RuleScopedNativeListExecNativeType
    (policy : UnsupportedExecPolicy) : Type :=
  GSLTNativeType (ruleScopedNativeListExecGSLT policy)

/-- The exact one-step successor type generated from rule-scoped execution. -/
noncomputable def ruleScopedNativeListExactTargetNativeType
    (policy : UnsupportedExecPolicy) (target : List Atom) :
    RuleScopedNativeListExecNativeType policy :=
  exactTargetNativeType (ruleScopedNativeListExecGSLT policy) target

/-- Inhabiting the exact target type is equivalent to one transition of the
rule-scoped executable machine. -/
theorem satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
    (policy : UnsupportedExecPolicy) (source target : List Atom) :
    (gsltOSLF (ruleScopedNativeListExecGSLT policy)).satisfies source
        (ruleScopedNativeListExactTargetNativeType policy target).pred ↔
      cRuleScopedSourceWorkQueueStep policy source = some target := by
  change
    (gsltOSLF (ruleScopedNativeListExecGSLT policy)).satisfies source
        (exactTargetNativeType (ruleScopedNativeListExecGSLT policy) target).pred ↔
      cRuleScopedSourceWorkQueueStep policy source = some target
  exact
    (satisfies_exactTargetNativeType_iff_step
      (ruleScopedNativeListExecGSLT policy) source target).trans
      (ruleScopedNativeListExecGSLT_step_iff policy source target)

/-! ## Bounded proof-relevant execution -/

/-- A proof-relevant rule-scoped execution trace.  The fuel index is an upper
bound: a quiescent state yields a reflexive trace even when fuel remains. -/
inductive CRuleScopedTrace (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Type where
  | refl : CRuleScopedTrace policy fuel source source
  | step {fuel source middle target} :
      cRuleScopedSourceWorkQueueStep policy source = some middle →
      CRuleScopedTrace policy fuel middle target →
      CRuleScopedTrace policy (fuel + 1) source target

/-- Erase a proof-relevant rule-scoped trace to the executable GSLT path with
the same intermediate states. -/
def CRuleScopedTrace.toRewritePath
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CRuleScopedTrace policy fuel source target) :
    (ruleScopedNativeListExecGSLT policy).RewritePath source target :=
  match trace with
  | .refl => .nil _
  | .step moved tail =>
      .cons
        ((ruleScopedNativeListExecGSLT_step_iff policy _ _).2 moved)
        tail.toRewritePath

/-- A proof-relevant rule-scoped execution whose every primitive transition
inhabits the OSLF-generated exact type of its successor. -/
inductive RuleScopedNativeTypeTrace (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Type where
  | refl {fuel : Nat} {source : List Atom} :
      RuleScopedNativeTypeTrace policy fuel source source
  | step {fuel source middle target} :
      (gsltOSLF (ruleScopedNativeListExecGSLT policy)).satisfies source
        (ruleScopedNativeListExactTargetNativeType policy middle).pred →
      RuleScopedNativeTypeTrace policy fuel middle target →
      RuleScopedNativeTypeTrace policy (fuel + 1) source target

/-- OSLF classifies every transition retained by a rule-scoped executable
trace. -/
def CRuleScopedTrace.toNativeTypeTrace
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CRuleScopedTrace policy fuel source target) :
    RuleScopedNativeTypeTrace policy fuel source target :=
  match trace with
  | .refl => .refl
  | .step moved tail =>
      .step
        ((satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          policy _ _).2 moved)
        tail.toNativeTypeTrace

/-- Number of executed transitions retained by a proof-relevant trace. -/
def CRuleScopedTrace.steps :
    {policy : UnsupportedExecPolicy} → {fuel : Nat} →
      {source target : List Atom} →
      CRuleScopedTrace policy fuel source target → Nat
  | _, _, _, _, .refl => 0
  | _, _, _, _, .step _ tail => tail.steps + 1

/-- Trace erasure preserves the exact transition count. -/
theorem CRuleScopedTrace.toRewritePath_length
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CRuleScopedTrace policy fuel source target) :
    trace.toRewritePath.length = trace.steps := by
  induction trace with
  | refl =>
      simp only [toRewritePath, steps, GSLT.RewritePath.length]
  | step moved tail induction =>
      simp only [toRewritePath, GSLT.RewritePath.length, steps]
      omega

/-- The exact-fuel evaluator constructs a path to its returned state. -/
def cRuleScopedSourceWorkQueueRunN_trace
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    CRuleScopedTrace policy fuel source
      (cRuleScopedSourceWorkQueueRunN policy fuel source).1 := by
  induction fuel generalizing source with
  | zero => exact .refl
  | succ fuel induction =>
      simp only [cRuleScopedSourceWorkQueueRunN]
      cases moved : cRuleScopedSourceWorkQueueStep policy source with
      | none => exact .refl
      | some next => exact .step moved (induction next)

/-- Every exact-fuel rule-scoped execution is classified transition-by-
transition by the native types generated through OSLF. -/
def cRuleScopedSourceWorkQueueRunN_nativeTypeTrace
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    RuleScopedNativeTypeTrace policy fuel source
      (cRuleScopedSourceWorkQueueRunN policy fuel source).1 :=
  (cRuleScopedSourceWorkQueueRunN_trace policy fuel source).toNativeTypeTrace

/-- Every bounded evaluator result carries a trace whose length is the
reported number of executed steps. -/
def cRuleScopedSourceWorkQueueRunN_certificate
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    { trace : CRuleScopedTrace policy fuel source
        (cRuleScopedSourceWorkQueueRunN policy fuel source).1 //
      trace.steps = (cRuleScopedSourceWorkQueueRunN policy fuel source).2 } := by
  induction fuel generalizing source with
  | zero =>
      simp only [cRuleScopedSourceWorkQueueRunN]
      exact ⟨.refl, rfl⟩
  | succ fuel induction =>
      simp only [cRuleScopedSourceWorkQueueRunN]
      cases moved : cRuleScopedSourceWorkQueueStep policy source with
      | none =>
          simp only
          exact ⟨.refl, rfl⟩
      | some next =>
          let tail := induction next
          refine ⟨.step moved tail.1, ?_⟩
          simp only [CRuleScopedTrace.steps]
          exact congrArg (· + 1) tail.2

/-- The exact path component of the bounded execution certificate. -/
def cRuleScopedSourceWorkQueueRunN_rewritePath
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    (ruleScopedNativeListExecGSLT policy).RewritePath source
      (cRuleScopedSourceWorkQueueRunN policy fuel source).1 :=
  (cRuleScopedSourceWorkQueueRunN_certificate policy fuel source).1.toRewritePath

/-- The executable reports exactly the number of non-reflexive steps in its
proof-relevant path. -/
theorem cRuleScopedSourceWorkQueueRunN_rewritePath_length
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    (cRuleScopedSourceWorkQueueRunN_rewritePath policy fuel source).length =
      (cRuleScopedSourceWorkQueueRunN policy fuel source).2 :=
  (cRuleScopedSourceWorkQueueRunN_certificate policy fuel source).1.toRewritePath_length.trans
    (cRuleScopedSourceWorkQueueRunN_certificate policy fuel source).2

/-! ## Positive and negative controls -/

private def localInput : InputSpec :=
  .compat ⟨[.expression [.symbol "trigger"]]⟩

theorem outputLocalVariable_is_preserved :
    instantiateRuleTemplateAtom? localInput []
      (.expression [.symbol "pair", .var "local", .var "local"]) =
      some (.expression [.symbol "pair", .var "local", .var "local"]) := by
  decide

theorem outputLocalDataVariable_is_not_inputInherited :
    ruleTemplateVariablesInherited localInput
      (.expression [.symbol "transaction", .var "local"]) = false := by
  decide

private def inheritedInput : InputSpec :=
  .compat ⟨[.expression [.symbol "trigger", .var "inherited"]]⟩

theorem inheritedDataVariable_is_inputInherited :
    ruleTemplateVariablesInherited inheritedInput
      (.expression [.symbol "transaction", .var "inherited"]) = true := by
  decide

theorem unmatchedInputVariable_is_rejected :
    instantiateRuleTemplateAtom? inheritedInput [] (.var "inherited") =
      none := by
  decide

theorem capturedValue_is_opaque :
    instantiateRuleTemplateAtom? inheritedInput
      [("inherited",
        .expression [.symbol "exec-body", .var "inner", .var "inner"])]
      (.var "inherited") =
      some (.expression [.symbol "exec-body", .var "inner", .var "inner"]) := by
  decide

private def alphaLeft : Atom :=
  .expression [.symbol "pair", .var "left", .var "left"]

private def alphaRight : Atom :=
  .expression [.symbol "pair", .var "right", .var "right"]

private def nonAlpha : Atom :=
  .expression [.symbol "pair", .var "left", .var "right"]

theorem alphaRenamedSupport_coalesces :
    morkInsertSupport [alphaLeft] alphaRight = [alphaLeft] := by
  decide

theorem differentVariableSharing_does_not_coalesce :
    morkInsertSupport [alphaLeft] nonAlpha = [alphaLeft, nonAlpha] := by
  decide

theorem alphaRenamedSupport_removes :
    morkEraseSupport [alphaLeft, .symbol "kept"] alphaRight =
      [.symbol "kept"] := by
  decide

#print axioms instantiateRuleTemplateAtom?_outputLocal
#print axioms instantiateRuleTemplateAtom?_inputVariable
#print axioms ruleTemplateCovered_of_templateCovered
#print axioms instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?_of_covered
#print axioms ruleTemplateCovered_eq_templateCovered_of_variablesInherited
#print axioms instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
#print axioms sameMorkSupportAtom_eq_true_iff
#print axioms cApplyRuleScopedSinkBatch_append
#print axioms morkSupportKey_injective_on
#print axioms morkSupportContains_eq_true_iff_key_mem
#print axioms morkSupportContains_morkInsertSupport_self_core
#print axioms morkSupportContains_morkInsertSupport_of_contains_core
#print axioms morkSupportContains_morkEraseSupport_of_key_ne_core
#print axioms morkSupportContains_morkUnionSupport_of_contains_core
#print axioms morkSupportContains_morkUnionSupport_of_staged_contains_core
#print axioms mem_morkInsertSupport_of_mem_core
#print axioms mem_morkUnionSupport_of_mem_left_core
#print axioms mem_of_morkSupportContains_of_reference
#print axioms morkSupportKey_not_mem_of_contains_eq_false
#print axioms morkInsertSupport_nodup
#print axioms morkEraseSupport_nodup
#print axioms morkEraseSupport_eq_erase_of_mem
#print axioms morkUnionSupport_nodup
#print axioms morkSubtractSupport_nodup
#print axioms not_mem_morkEraseSupport_self
#print axioms morkSupportContains_morkEraseSupport_self
#print axioms morkInsertSupport_morkEraseSupport_self
#print axioms morkInsertSupport_list_nodup
#print axioms morkEraseSupport_list_nodup
#print axioms morkUnionSupport_list_nodup
#print axioms morkSubtractSupport_list_nodup
#print axioms morkInsertSupport_atomsWithin
#print axioms morkEraseSupport_atomsWithin
#print axioms morkUnionSupport_atomsWithin
#print axioms morkSubtractSupport_atomsWithin
#print axioms compactExtremaList_atomsWithin
#print axioms stageRuleScopedSinkRows_atomsWithin
#print axioms finalizeRuleScopedSink_atomsWithin
#print axioms cApplyRuleScopedSinkBatch_atomsWithin
#print axioms cApplyRuleScopedTemplate_atomsWithin
#print axioms cFireRuleScopedSourceExecFact_atomsWithin
#print axioms cApplyRuleScopedSinkBatch_list_nodup
#print axioms cApplyRuleScopedTemplate_list_nodup
#print axioms cFireRuleScopedSourceExecFact_list_nodup
#print axioms cApplyRuleScopedSinkBatch_mork_nodup
#print axioms cApplyRuleScopedTemplate_mork_nodup
#print axioms cFireRuleScopedSourceExecFact_mork_nodup
#print axioms mem_morkInsertSupport_cases
#print axioms mem_morkUnionSupport_cases
#print axioms mem_morkSubtractSupport_source
#print axioms not_mem_morkSubtractSupport_of_mem_staged
#print axioms mem_morkSubtractSupport_of_mem_of_keys_ne
#print axioms morkSupportContains_morkSubtractSupport_of_keys_ne_core
#print axioms not_mem_morkSubtractSupport_of_contains_staged
#print axioms mem_foldl_stageRuleScopedSink_cases
#print axioms morkSupportContains_foldl_stageRuleScopedSink_of_row
#print axioms not_mem_finalizeRuleScopedSink_remove_of_row
#print axioms not_mem_cApplyRuleScopedSinkBatch_of_remove_or_nonproducing_add
#print axioms not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
#print axioms mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
#print axioms morkSupportContains_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
#print axioms morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
#print axioms mem_cApplyRuleScopedTemplate_of_supportSet
#print axioms cApplyRuleScopedSinkBatch_atomsWithin_of_additions
#print axioms cApplyRuleScopedTemplate_atomsWithin_of_additions
#print axioms cFireRuleScopedSourceExecFact_atomsWithin_of_additions
#print axioms cApplyRuleScopedSinkBatch_nil
#print axioms cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
#print axioms ruleScopedNativeListExecGSLT_step_deterministic
#print axioms satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
#print axioms cRuleScopedSourceWorkQueueRunN_rewritePath_length
#print axioms outputLocalVariable_is_preserved
#print axioms outputLocalDataVariable_is_not_inputInherited
#print axioms inheritedDataVariable_is_inputInherited
#print axioms unmatchedInputVariable_is_rejected
#print axioms capturedValue_is_opaque
#print axioms alphaRenamedSupport_coalesces
#print axioms differentVariableSharing_does_not_coalesce
#print axioms alphaRenamedSupport_removes

end Mettapedia.Languages.ProcessCalculi.MORK
