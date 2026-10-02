import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentInterpretation
import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeCumulativeFormationCoherenceBoundary

/-!
# Universe operations attached to the same native interpretation

The raw operations below use the existing semantic CwF and all native level
expressions. They contain no decoding, closure, constructor-meaning or
substitution proofs. Those are independent predicates on the very same raw
native interpretation; a code constructor alone does not interpret Pi or Sigma.

The strict predicates state an explicit candidate-class restriction. Equality
of semantic codes or decoded CwF types is not inferred from equivalence and
is not a universal requirement on other interpretation strategies. On this
class, native cumulativity and semantic substitution derive the code squares
on admitted inputs. Arbitrary raw substitutions or uninterpreted codes gain
no such law.

No common model, universe-operator inhabitant, full identity interpretation,
or six-family qualification is constructed here. Native K, UIP, eta and a
particular evaluation strategy remain unselected.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive
open SharedJudgmentFragment

universe u v w w' uHost

/-- Operations only. The native level index is unbounded; this does not
assert that a host interpreting these operations and their laws exists. -/
structure Operations (C : Cwf.{u, v, w, w'}) where
  «universe» : TarskiUniverseFamily (LevelExpr Nat) C
  sortCode : (context : C.Ctx) → (level : LevelExpr Nat) →
    C.Tm context («universe».univ context (.succ level))
  liftCode : {context : C.Ctx} → {lower upper : LevelExpr Nat} →
    Tower.Cumulative (.sort lower) (.sort upper) →
    C.Tm context («universe».univ context lower) →
      C.Tm context («universe».univ context upper)
  piCode : {context : C.Ctx} → {left right : LevelExpr Nat} →
    (domain : C.Tm context («universe».univ context left)) →
    C.Tm (C.ext context («universe».el domain))
      («universe».univ (C.ext context («universe».el domain)) right) →
        C.Tm context («universe».univ context (.max left right))
  sigmaCode : {context : C.Ctx} → {left right : LevelExpr Nat} →
    (domain : C.Tm context («universe».univ context left)) →
    C.Tm (C.ext context («universe».el domain))
      («universe».univ (C.ext context («universe».el domain)) right) →
        C.Tm context («universe».univ context (.max left right))

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-! ## Independent native meaning and decoding requirements -/

/-- Universe types and their term codes have separate meanings in the
same relation. The actual source formation is constructed below. -/
def SortMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (level : LevelExpr Nat),
    ContextFormation assembly.rules context.raw →
      interpretation.ty context (sortTm level)
          (operations.universe.univ (interpretation.ctx context) level) ∧
        interpretation.term context (sortTm level) (sortTm (.succ level))
          (operations.universe.univ (interpretation.ctx context) (.succ level))
          (operations.sortCode (interpretation.ctx context) level)

/-- Every native type admitted at a displayed universe has a code in that
very semantic universe. General interpretation totality alone does not fix
the semantic type to be this universe. -/
def CodeTotal (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n) (level : LevelExpr Nat),
    Judgment assembly.rules context.raw type (sortTm level) →
      ∃ code : C.Tm (interpretation.ctx context)
          (operations.universe.univ (interpretation.ctx context) level),
        interpretation.term context type (sortTm level)
          (operations.universe.univ (interpretation.ctx context) level) code

/-- The term meaning of an admitted type code decodes to a type meaning.
This neither identifies distinct code values nor supplies code totality. -/
def CodesDecode (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n) (level : LevelExpr Nat)
    (code : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) level)),
    Judgment assembly.rules context.raw type (sortTm level) →
    interpretation.term context type (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level) code →
      interpretation.ty context type (operations.universe.el code)

/-- The primitive native cumulativity clause acts on the selected code,
instead of choosing an unrelated witness for the raised judgment. -/
def CumulativeMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n)
    (lower upper : LevelExpr Nat) (order : Tower.Cumulative (.sort lower) (.sort upper))
    (code : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) lower)),
    Judgment assembly.rules context.raw type (sortTm lower) →
    interpretation.term context type (sortTm lower)
      (operations.universe.univ (interpretation.ctx context) lower) code →
      interpretation.term context type (sortTm upper)
        (operations.universe.univ (interpretation.ctx context) upper)
        (operations.liftCode order code)

/-- Strict decoding of the universe's own formation code. This is a
restriction to equality of internal CwF type objects, not merely equivalence. -/
def StrictSortDecoding (operations : Operations C) : Prop :=
  ∀ (context : C.Ctx) (level : LevelExpr Nat),
    operations.universe.el (operations.sortCode context level) =
      operations.universe.univ context level

/-- Strict preservation of decoded type objects under cumulative lifting.
It does not assert equality of the lower and upper code carriers. -/
def StrictLiftDecoding (operations : Operations C) : Prop :=
  ∀ (context : C.Ctx) (lower upper : LevelExpr Nat)
    (order : Tower.Cumulative (.sort lower) (.sort upper))
    (code : C.Tm context (operations.universe.univ context lower)),
    operations.universe.el (operations.liftCode order code) = operations.universe.el code

/-- Strict functionality is scoped to a single admitted native code and
its displayed universe. It is not a claim about all possible semantic models
or an identification of codes with equivalent decoded carriers. -/
def StrictCodeUniqueness (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n) (level : LevelExpr Nat)
    (first second : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) level)),
    Judgment assembly.rules context.raw type (sortTm level) →
    interpretation.term context type (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level) first →
    interpretation.term context type (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level) second → first = second

/-! ## Actual native formation and cumulative derivations -/

theorem sort_admitted {n : Nat} {context : Tower.Ctx n}
    (formed : ContextFormation assembly.rules context) (level : LevelExpr Nat) :
    Judgment assembly.rules context (sortTm level) (sortTm (.succ level)) :=
  ⟨formed, .headType (.sort level)⟩

theorem cumulative_admitted {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
    {lower upper : LevelExpr Nat}
    (admitted : Judgment assembly.rules context type (sortTm lower))
    (order : Tower.Cumulative (.sort lower) (.sort upper)) :
    Judgment assembly.rules context type (sortTm upper) :=
  ⟨admitted.context, .cumul admitted.typing order⟩

/-- Composition uses the actual pointwise native level order. -/
theorem cumulativeTrans {first middle last : LevelExpr Nat}
    (earlier : Tower.Cumulative (.sort first) (.sort middle))
    (later : Tower.Cumulative (.sort middle) (.sort last)) :
    Tower.Cumulative (.sort first) (.sort last) :=
  fun valuation => Nat.le_trans (earlier valuation) (later valuation)

theorem sort_has_code (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n}
    (formed : ContextFormation assembly.rules context.raw) (level : LevelExpr Nat) :
    Judgment assembly.rules context.raw (sortTm level) (sortTm (.succ level)) ∧
      interpretation.term context (sortTm level) (sortTm (.succ level))
        (operations.universe.univ (interpretation.ctx context) (.succ level))
        (operations.sortCode (interpretation.ctx context) level) :=
  ⟨sort_admitted formed level, (sorts n context level formed).2⟩

theorem decoded_sort_meaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    (decode : CodesDecode interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n}
    (formed : ContextFormation assembly.rules context.raw) (level : LevelExpr Nat) :
    interpretation.ty context (sortTm level)
      (operations.universe.el (operations.sortCode (interpretation.ctx context) level)) :=
  decode n context (sortTm level) (.succ level) _ (sort_admitted formed level)
    (sorts n context level formed).2

/-! ## Code lifting laws derived on admitted meanings -/

theorem admitted_lift_identity
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (cumulative : CumulativeMeaning interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n} {level : LevelExpr Nat}
    (admitted : Judgment assembly.rules context.raw type (sortTm level))
    (code : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) level))
    (meaning : interpretation.term context type (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level) code) :
    operations.liftCode (fun _ => Nat.le_refl _) code = code :=
  unique n context type level _ _ admitted
    (cumulative n context type level level (fun _ => Nat.le_refl _) code admitted meaning) meaning

theorem admitted_lift_composition
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (cumulative : CumulativeMeaning interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n} {first middle last : LevelExpr Nat}
    (earlier : Tower.Cumulative (.sort first) (.sort middle))
    (later : Tower.Cumulative (.sort middle) (.sort last))
    (admitted : Judgment assembly.rules context.raw type (sortTm first))
    (code : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) first))
    (meaning : interpretation.term context type (sortTm first)
      (operations.universe.univ (interpretation.ctx context) first) code) :
    operations.liftCode later (operations.liftCode earlier code) =
      operations.liftCode (cumulativeTrans earlier later) code := by
  have middleAdmitted := cumulative_admitted admitted earlier
  have middleMeaning := cumulative n context type first middle earlier code admitted meaning
  exact unique n context type last _ _ (cumulative_admitted middleAdmitted later)
    (cumulative n context type middle last later _ middleAdmitted middleMeaning)
    (cumulative n context type first last (cumulativeTrans earlier later) code admitted meaning)

/-! ## Substitution of the same code and its decoding -/

/-- The existing universe naturality witness supplies the necessary type
transport. Its laws are not stored in `Operations`. -/
def substituteCode (operations : Operations C)
    (stable : operations.universe.SubstitutionStable)
    {source target : C.Ctx} {level : LevelExpr Nat}
    (substitution : C.Sub source target)
    (code : C.Tm target (operations.universe.univ target level)) :
    C.Tm source (operations.universe.univ source level) :=
  TarskiUniverseFamily.castTm (stable.univ_sub level substitution) (C.tmSub code substitution)

private theorem term_cast
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {term type : Tower.Tm n}
    {first second : C.Ty (interpretation.ctx context)} (equal : first = second)
    {value : C.Tm (interpretation.ctx context) first}
    (meaning : interpretation.term context term type first value) :
    interpretation.term context term type second (TarskiUniverseFamily.castTm equal value) := by
  cases equal
  exact meaning

theorem substituted_code_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    (substitutes : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (stable : operations.universe.SubstitutionStable)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n} {target : SharedJudgmentInterpretation.Context assembly m}
    {sigma : Sub Tower.Head n m}
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source.raw target.raw sigma)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (subMeaning : interpretation.sub source target sigma semantic)
    {type : Tower.Tm n} {level : LevelExpr Nat}
    (admitted : Judgment assembly.rules source.raw type (sortTm level))
    (code : C.Tm (interpretation.ctx source)
      (operations.universe.univ (interpretation.ctx source) level))
    (meaning : interpretation.term source type (sortTm level)
      (operations.universe.univ (interpretation.ctx source) level) code) :
    interpretation.term target (subst sigma type) (sortTm level)
      (operations.universe.univ (interpretation.ctx target) level)
      (substituteCode operations stable semantic code) := by
  have transported := substitutes n m source target sigma semantic type (sortTm level)
    _ code formed typed admitted subMeaning (sorts n source level admitted.context).1 meaning
  exact term_cast interpretation (stable.univ_sub level semantic) transported

/-- Two independently derived meanings meet at the same actual raised,
substituted native judgment. Strict functionality yields their code square. -/
theorem admitted_lift_substitution
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    (cumulative : CumulativeMeaning interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    (substitutes : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (stable : operations.universe.SubstitutionStable)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n} {target : SharedJudgmentInterpretation.Context assembly m}
    {sigma : Sub Tower.Head n m}
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source.raw target.raw sigma)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (subMeaning : interpretation.sub source target sigma semantic)
    {type : Tower.Tm n} {lower upper : LevelExpr Nat}
    (order : Tower.Cumulative (.sort lower) (.sort upper))
    (admitted : Judgment assembly.rules source.raw type (sortTm lower))
    (code : C.Tm (interpretation.ctx source)
      (operations.universe.univ (interpretation.ctx source) lower))
    (meaning : interpretation.term source type (sortTm lower)
      (operations.universe.univ (interpretation.ctx source) lower) code) :
    substituteCode operations stable semantic (operations.liftCode order code) =
      operations.liftCode order (substituteCode operations stable semantic code) := by
  have raised := cumulative_admitted admitted order
  have liftedMeaning := cumulative n source type lower upper order code admitted meaning
  have first := substituted_code_meaning interpretation operations sorts substitutes stable
    formed typed semantic subMeaning raised _ liftedMeaning
  have original := substituted_code_meaning interpretation operations sorts substitutes stable
    formed typed semantic subMeaning admitted code meaning
  have second := cumulative m target (subst sigma type) lower upper order _
    (admitted.substitute formed typed) original
  exact unique m target (subst sigma type) upper _ _
    (raised.substitute formed typed) first second

/-- The complete two-lift/substitution square retains native admission,
the actual semantic code, and the reindexed original decoded type. The
lift-composition and lift-substitution laws are derived, not hypotheses. -/
theorem cumulative_substitution_square
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    (cumulative : CumulativeMeaning interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    (decode : CodesDecode interpretation operations)
    (liftDecode : StrictLiftDecoding operations)
    (substitutes : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (stable : operations.universe.SubstitutionStable)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n} {target : SharedJudgmentInterpretation.Context assembly m}
    {sigma : Sub Tower.Head n m}
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source.raw target.raw sigma)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (subMeaning : interpretation.sub source target sigma semantic)
    {type : Tower.Tm n} {first middle last : LevelExpr Nat}
    (earlier : Tower.Cumulative (.sort first) (.sort middle))
    (later : Tower.Cumulative (.sort middle) (.sort last))
    (admitted : Judgment assembly.rules source.raw type (sortTm first))
    (code : C.Tm (interpretation.ctx source)
      (operations.universe.univ (interpretation.ctx source) first))
    (meaning : interpretation.term source type (sortTm first)
      (operations.universe.univ (interpretation.ctx source) first) code) :
    let finalCode := substituteCode operations stable semantic
      (operations.liftCode later (operations.liftCode earlier code))
    Judgment assembly.rules target.raw (subst sigma type) (sortTm last) ∧
      finalCode = operations.liftCode (cumulativeTrans earlier later)
        (substituteCode operations stable semantic code) ∧
      interpretation.term target (subst sigma type) (sortTm last)
        (operations.universe.univ (interpretation.ctx target) last) finalCode ∧
      operations.universe.el finalCode = C.tySub (operations.universe.el code) semantic ∧
      interpretation.ty target (subst sigma type)
        (C.tySub (operations.universe.el code) semantic) := by
  let finalCode := substituteCode operations stable semantic
    (operations.liftCode later (operations.liftCode earlier code))
  have middleAdmitted := cumulative_admitted admitted earlier
  have lastAdmitted := cumulative_admitted middleAdmitted later
  have middleMeaning := cumulative n source type first middle earlier code admitted meaning
  have lastMeaning := cumulative n source type middle last later _ middleAdmitted middleMeaning
  have targetAdmitted := lastAdmitted.substitute formed typed
  have finalMeaning := substituted_code_meaning interpretation operations sorts substitutes stable
    formed typed semantic subMeaning lastAdmitted _ lastMeaning
  have square : finalCode = operations.liftCode (cumulativeTrans earlier later)
      (substituteCode operations stable semantic code) := by
    dsimp [finalCode]
    rw [admitted_lift_composition interpretation operations cumulative unique
      earlier later admitted code meaning]
    exact admitted_lift_substitution interpretation operations sorts cumulative unique substitutes stable
      formed typed semantic subMeaning (cumulativeTrans earlier later) admitted code meaning
  have decoded : operations.universe.el finalCode =
      C.tySub (operations.universe.el code) semantic := by
    rw [square, liftDecode]
    exact stable.el_sub code semantic
  refine ⟨targetAdmitted, square, finalMeaning, decoded, ?_⟩
  rw [← decoded]
  exact decode m target (subst sigma type) last finalCode targetAdmitted finalMeaning

/-! ## An inhabited native source and a nontrivial typed substitution -/

namespace WeakeningControl

/-- An actual open type code, not a closed term chosen to ignore substitution. -/
def source (level : LevelExpr Nat) : SharedJudgmentInterpretation.Context common 1 :=
  ⟨.snoc .nil (sortTm level), .snoc .nil (.headType (.sort level)) (.sort (.succ level))⟩

/-- The added field uses the shared package's genuine native wire datatype. -/
def target (level : LevelExpr Nat) : SharedJudgmentInterpretation.Context common 2 :=
  .snoc (source level) NativeWireData.dataType (.sort Tower.zero)
    (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)) (.sort Tower.zero)

def substitution : Sub Tower.Head 1 2 := renSub wk

theorem source_formed (level : LevelExpr Nat) :
    ContextFormation common.rules (source level).raw :=
  .snoc .nil (.headType (.sort level)) (.sort (.succ level))

theorem target_formed (level : LevelExpr Nat) :
    ContextFormation common.rules (target level).raw :=
  .snoc (source_formed level)
    (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))
    (.sort Tower.zero)

theorem source_admitted (level : LevelExpr Nat) :
    Judgment common.rules (source level).raw (.var 0) (sortTm level) :=
  ⟨source_formed level, .var 0⟩

theorem substitution_typed (level : LevelExpr Nat) :
    FormationSensitive.CtxMor common.rules (source level).raw (target level).raw substitution := by
  intro index
  fin_cases index
  exact .var 1

theorem substituted_variable : subst substitution (.var 0) = (.var 1 : Tower.Tm 2) := rfl

/-- Forgetting the index shift would change the source code to the new Data
field. The distinction is syntactic and does not assume a semantic model. -/
theorem substituted_variable_ne_newest :
    subst substitution (.var 0) ≠ (.var 0 : Tower.Tm 2) := by decide

theorem next_level (level : LevelExpr Nat) :
    Tower.Cumulative (.sort level) (.sort (.succ level)) :=
  fun _ => Nat.le_succ _

theorem raised_substitution_admitted (level : LevelExpr Nat) :
    Judgment common.rules (target level).raw (.var 1) (sortTm (.succ (.succ level))) :=
  (cumulative_admitted (cumulative_admitted (source_admitted level) (next_level level))
    (next_level (.succ level))).substitute (target_formed level) (substitution_typed level)

/-- The source-side controls have actual proofs independently of every
semantic predicate used in the following consequence. -/
theorem native_control (level : LevelExpr Nat) :
    ContextFormation common.rules (source level).raw ∧
      ContextFormation common.rules (target level).raw ∧
      Judgment common.rules (source level).raw (.var 0) (sortTm level) ∧
      FormationSensitive.CtxMor common.rules (source level).raw (target level).raw substitution ∧
      Judgment common.rules (target level).raw (.var 1) (sortTm (.succ (.succ level))) ∧
      subst substitution (.var 0) ≠ (.var 0 : Tower.Tm 2) :=
  ⟨source_formed level, target_formed level, source_admitted level,
    substitution_typed level, raised_substitution_admitted level,
    substituted_variable_ne_newest⟩

/-- Independent coverage supplies witnesses for this concrete admitted
source and substitution. Their cumulative/decoding square then follows from
the primitive laws, rather than being an additional qualification field.
This is conditional semantic coverage of an inhabited native source; it is
not an existence theorem for a common model satisfying those laws. -/
theorem semantic_control
    (interpretation : SharedJudgmentInterpretation.Data common C)
    (operations : Operations C) (sorts : SortMeaning interpretation operations)
    (total : CodeTotal interpretation operations)
    (subTotal : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal interpretation)
    (cumulative : CumulativeMeaning interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    (decode : CodesDecode interpretation operations)
    (liftDecode : StrictLiftDecoding operations)
    (substitutes : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (stable : operations.universe.SubstitutionStable) (level : LevelExpr Nat) :
    ∃ (code : C.Tm (interpretation.ctx (source level))
        (operations.universe.univ (interpretation.ctx (source level)) level))
      (semantic : C.Sub (interpretation.ctx (target level)) (interpretation.ctx (source level))),
      interpretation.term (source level) (.var 0) (sortTm level)
        (operations.universe.univ (interpretation.ctx (source level)) level) code ∧
      interpretation.sub (source level) (target level) substitution semantic ∧
      let finalCode := substituteCode operations stable semantic
        (operations.liftCode (next_level (.succ level))
          (operations.liftCode (next_level level) code))
      Judgment common.rules (target level).raw (.var 1) (sortTm (.succ (.succ level))) ∧
        finalCode = operations.liftCode
          (cumulativeTrans (next_level level) (next_level (.succ level)))
          (substituteCode operations stable semantic code) ∧
        interpretation.term (target level) (.var 1) (sortTm (.succ (.succ level)))
          (operations.universe.univ (interpretation.ctx (target level)) (.succ (.succ level)))
          finalCode ∧
        operations.universe.el finalCode = C.tySub (operations.universe.el code) semantic ∧
        interpretation.ty (target level) (.var 1)
          (C.tySub (operations.universe.el code) semantic) := by
  obtain ⟨code, meaning⟩ := total 1 (source level) (.var 0) level (source_admitted level)
  obtain ⟨semantic, subMeaning⟩ := subTotal 1 2 (source level) (target level) substitution
    (target_formed level) (substitution_typed level)
  refine ⟨code, semantic, meaning, subMeaning, ?_⟩
  exact cumulative_substitution_square interpretation operations sorts cumulative unique decode
    liftDecode substitutes stable (target_formed level) (substitution_typed level)
    semantic subMeaning (next_level level) (next_level (.succ level))
    (source_admitted level) code meaning

end WeakeningControl

/-! ## Exact strict-class obstruction on the actual formation diamond -/

/-- Select a witness supplied by the independently stated coverage law.
This defines no native semantics: the raw relation and its coverage proof
are already supplied. Strict uniqueness, when available, removes the choice. -/
noncomputable def chooseCode
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (total : CodeTotal interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {level : LevelExpr Nat}
    (term : { type : Tower.Tm n // Judgment assembly.rules context.raw type (sortTm level) }) :
    C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) level) :=
  Classical.choose (total n context term.val level term.property)

theorem chooseCode_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (total : CodeTotal interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {level : LevelExpr Nat}
    (term : { type : Tower.Tm n // Judgment assembly.rules context.raw type (sortTm level) }) :
    interpretation.term context term.val (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level)
      (chooseCode interpretation operations total term) :=
  Classical.choose_spec (total n context term.val level term.property)

theorem chooseCode_eq
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (total : CodeTotal interpretation operations)
    (unique : StrictCodeUniqueness interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {level : LevelExpr Nat}
    (term : { type : Tower.Tm n // Judgment assembly.rules context.raw type (sortTm level) })
    (code : C.Tm (interpretation.ctx context)
      (operations.universe.univ (interpretation.ctx context) level))
    (meaning : interpretation.term context term.val (sortTm level)
      (operations.universe.univ (interpretation.ctx context) level) code) :
    chooseCode interpretation operations total term = code :=
  unique n context term.val level _ code term.property
    (chooseCode_meaning interpretation operations total term) meaning

namespace TaggedFormation

open NativeCumulativeFormationCoherenceBoundary
open Mettapedia.TypeTheory
open UniverseClosureProfiles TarskiCumulativeCodeCoherenceBoundary

/-- The formation diamond is interpreted only on its independently formed
native telescope; its raw declaration-level construction is unchanged. -/
def formedContext (level : LevelExpr Nat) : SharedJudgmentInterpretation.Context assembly 2 :=
  ⟨context level, context_formed assembly.declarations level⟩

/-- These two meaning clauses are for the same actual native Pi code at
the same upper display. If an independently supplied chart reads them as
the existing unequal tagged routes, strict uniqueness is impossible. The
operator and chart are parameters, not constructed hosts or native tag tests.
No conclusion concerns interpretation classes without these exact clauses. -/
theorem strict_code_uniqueness_incompatible
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (total : CodeTotal interpretation operations)
    (level : LevelExpr Nat) (operator : SmallFamilyEnclosingUniverseOperator.{uHost})
    (A : Type uHost) (B : A → Type uHost) (valuation : Nat → Nat)
    (domain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
      (LevelExpr.eval valuation level))
    (codomain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El
        (LevelExpr.eval valuation level) domain →
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
        (LevelExpr.eval valuation level))
    (chart : C.Tm (interpretation.ctx (formedContext level))
        (operations.universe.univ (interpretation.ctx (formedContext level)) (upperLevel level)) →
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
        (LevelExpr.eval valuation level + 1))
    (liftValue formValue : C.Tm (interpretation.ctx (formedContext level))
      (operations.universe.univ (interpretation.ctx (formedContext level)) (upperLevel level)))
    (liftMeaning : interpretation.term (formedContext level) dependentPi (sortTm (upperLevel level))
      (operations.universe.univ (interpretation.ctx (formedContext level)) (upperLevel level)) liftValue)
    (formMeaning : interpretation.term (formedContext level) dependentPi (sortTm (upperLevel level))
      (operations.universe.univ (interpretation.ctx (formedContext level)) (upperLevel level)) formValue)
    (cumulativeEquation : chart liftValue =
      Routes.liftedPi (tagOperator operator) A B (LevelExpr.eval valuation level) domain codomain)
    (formationEquation : chart formValue =
      (Routes.upperPi (tagOperator operator) A B (LevelExpr.eval valuation level)).code
        domain codomain) :
    ¬ StrictCodeUniqueness interpretation operations := by
  intro unique
  apply tagged_route_equations_incompatible assembly.declarations level operator A B valuation
    domain codomain
  refine ⟨fun term => chart (chooseCode interpretation operations total (context := formedContext level) term), ?_, ?_⟩
  · exact (congrArg chart (chooseCode_eq interpretation operations total unique
      (context := formedContext level)
      (formedByLift assembly.declarations level) liftValue liftMeaning)).trans cumulativeEquation
  · exact (congrArg chart (chooseCode_eq interpretation operations total unique
      (context := formedContext level)
      (formedByUpper assembly.declarations level) formValue formMeaning)).trans formationEquation

end TaggedFormation

#print axioms admitted_lift_identity
#print axioms admitted_lift_composition
#print axioms admitted_lift_substitution
#print axioms cumulative_substitution_square
#print axioms WeakeningControl.native_control
#print axioms WeakeningControl.semantic_control
#print axioms TaggedFormation.strict_code_uniqueness_incompatible

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseInterpretation
