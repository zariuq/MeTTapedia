/-
# Typecheck-v3: the Exact/Gradual/Conflict seam

The gradual runtime waist for v3 (and, transported, for MeTTa Native):
every judged occurrence classifies into exactly one of

* **Exact** — fully `?Unknown`-free positive evidence; carries an
  `OptLicense`, the *only* authority for typed fast paths;
* **Gradual** — some ignorance remains; execution proceeds on the generic
  semantics, and **no license is constructible** (`no_inexact_actual_license`
  is correct-by-construction, in the style of `GroundingLicense`);
* **Conflict** — a definite, replayable witness (`EvidenceConflict.valid`),
  never manufactured from ignorance or exhaustion.

The seam laws proved here:

1. `classifyKind_unknown` — ignorance always classifies gradual: unknown
   evidence executes and can never conflict (`unknown_never_conflicts`).
2. `conflict_kind_witness` — every conflict classification carries a valid
   replayable witness.
3. `no_inexact_actual_license` / `no_inexact_expected_license` — gradual
   types cannot license typed optimization, structurally.
4. `exact_kind_license` — every exact classification constructs a license.
5. `conflict_persists` — a witnessed conflict survives every future
   precision refinement (the static-gradual-guarantee direction that makes
   conflict caches sound); dually, gradual *acceptance* is not persistent
   (named example), which is why gradual never licenses.
6. `exact_rigid` / `license_rigid` — exact types admit no proper
   refinement, so exact judgments and licenses are revision-eternal
   relative to their types.
7. Mobility — gradual may move to any of the three kinds as evidence
   upgrades (three named examples); exact and conflict never move.

Together: **`?Unknown` preserves execution without licensing typed
optimization** (`unknown_preserves_execution_without_license`).
-/
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core

namespace Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam

open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core

/-! ## §1 Exactness: the `?Unknown`-free predicate -/

mutual

/-- A type is exact when `?Unknown` occurs nowhere inside it.  Arrow modes
are orthogonal: a named effect parameter is symbolic polymorphism, not
gradual ignorance, so it does not spoil exactness. -/
def exactTy : Ty → Bool
  | .unknown => false
  | .prim _ => true
  | .list elem => exactTy elem
  | .product fields => exactArgs fields
  | .arrow doms _ cod => exactArgs doms && exactTy cod
  | .union left right => exactTy left && exactTy right
  | .newtype _ repr => exactTy repr
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf <;> try omega)

/-- Componentwise exactness for argument spines. -/
def exactArgs : TyArgs → Bool
  | .nil => true
  | .cons head tail => exactTy head && exactArgs tail
termination_by ts => sizeOf ts
decreasing_by all_goals (simp_wf; omega)

end

/-- Positive exactness witness. -/
example : exactTy (.arrow (.cons (.prim .num) .nil) (.grade .det)
    (.union (.prim .str) (.prim .bool))) = true := by
  simp [exactTy, exactArgs]

/-- Negative exactness witness: one buried `?Unknown` spoils exactness. -/
example : exactTy (.list (.newtype 3 .unknown)) = false := by
  simp [exactTy]

/-! ## §2 Precision refinement

`Refines t u` reads: `t` is a precision refinement of `u` — it fills some
of `u`'s `?Unknown` holes with concrete structure and changes nothing
else.  Arrow modes are preserved exactly (no gradual dimension there). -/

mutual

inductive Refines : Ty → Ty → Prop where
  | unknown (t) : Refines t .unknown
  | prim (p) : Refines (.prim p) (.prim p)
  | list {a b} : Refines a b → Refines (.list a) (.list b)
  | product {as bs} : RefinesArgs as bs → Refines (.product as) (.product bs)
  | arrow {ds ds' eff c c'} : RefinesArgs ds ds' → Refines c c' →
      Refines (.arrow ds eff c) (.arrow ds' eff c')
  | union {a a' b b'} : Refines a a' → Refines b b' →
      Refines (.union a b) (.union a' b')
  | newtype {n r r'} : Refines r r' → Refines (.newtype n r) (.newtype n r')

inductive RefinesArgs : TyArgs → TyArgs → Prop where
  | nil : RefinesArgs .nil .nil
  | cons {a b as bs} : Refines a b → RefinesArgs as bs →
      RefinesArgs (.cons a as) (.cons b bs)

end

mutual

/-- Refinement is reflexive: filling no holes is a refinement. -/
theorem Refines.refl : ∀ t : Ty, Refines t t
  | .unknown => .unknown .unknown
  | .prim p => .prim p
  | .list elem => .list (Refines.refl elem)
  | .product fields => .product (RefinesArgs.refl fields)
  | .arrow doms _ cod => .arrow (RefinesArgs.refl doms) (Refines.refl cod)
  | .union left right => .union (Refines.refl left) (Refines.refl right)
  | .newtype _ repr => .newtype (Refines.refl repr)
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf <;> try omega)

theorem RefinesArgs.refl : ∀ ts : TyArgs, RefinesArgs ts ts
  | .nil => .nil
  | .cons head tail => .cons (Refines.refl head) (RefinesArgs.refl tail)
termination_by ts => sizeOf ts
decreasing_by all_goals (simp_wf; omega)

end

/-! ## §3 The consistency/precision interaction

Two theorems carry the whole seam story.

`consistent_of_common`: two unprecisions of one common refinement are
consistent — the constructive heart of gradual consistency.

`consistent_of_refines`: consistency at higher precision implies
consistency at lower precision; contrapositively (`conflict_persists`),
a definite conflict can never be repaired by learning more.  That is
what makes conflict witnesses cacheable forever, and it is exactly the
asymmetry that forbids treating gradual acceptance as a promise. -/

mutual

theorem consistent_of_common :
    ∀ (t a b : Ty), Refines t a → Refines t b → Consistent a b
  | .unknown, _, b, ha, _ => by
      cases ha
      exact .unknownL b
  | .prim _, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | prim =>
          cases hb with
          | unknown => exact .unknownR _
          | prim => exact .refl _
  | .list elem, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | list ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | list hb' =>
              exact .listCong (consistent_of_common elem _ _ ha' hb')
  | .product fields, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | product ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | product hb' =>
              exact .productCong
                (consistentArgs_of_common fields _ _ ha' hb')
  | .arrow doms eff cod, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | arrow hda hca =>
          cases hb with
          | unknown => exact .unknownR _
          | arrow hdb hcb =>
              exact .arrowCong (consistentArgs_of_common doms _ _ hda hdb)
                (consistent_of_common cod _ _ hca hcb) (modeFits_refl eff)
  | .union left right, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | union hla hra =>
          cases hb with
          | unknown => exact .unknownR _
          | union hlb hrb =>
              exact .unionL
                (.unionR1 (consistent_of_common left _ _ hla hlb))
                (.unionR2 (consistent_of_common right _ _ hra hrb))
  | .newtype _ repr, _, b, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | newtype ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | newtype hb' =>
              exact .newtypeCong (consistent_of_common repr _ _ ha' hb')
termination_by t _ _ _ _ => t.rank
decreasing_by all_goals (simp [Ty.rank] <;> try omega)

theorem consistentArgs_of_common :
    ∀ (ts as bs : TyArgs), RefinesArgs ts as → RefinesArgs ts bs →
      ConsistentArgs as bs
  | .nil, _, _, ha, hb => by
      cases ha
      cases hb
      exact .nil
  | .cons head tail, _, _, ha, hb => by
      cases ha with
      | cons hha hta =>
          cases hb with
          | cons hhb htb =>
              exact .cons (consistent_of_common head _ _ hha hhb)
                (consistentArgs_of_common tail _ _ hta htb)
termination_by ts _ _ _ _ => ts.rank
decreasing_by all_goals (simp [TyArgs.rank]; omega)

end

mutual

/-- Losing precision preserves consistency: if the refined pair is
consistent, so is every unprecision of it. -/
theorem consistent_of_refines :
    ∀ {a' b' a b : Ty}, Consistent a' b' → Refines a' a → Refines b' b →
      Consistent a b
  | _, _, a, b, .refl t, ha, hb => consistent_of_common t a b ha hb
  | _, _, _, b, .unknownL _, ha, _ => by
      cases ha
      exact .unknownL b
  | _, _, a, _, .unknownR _, _, hb => by
      cases hb
      exact .unknownR a
  | _, _, _, b, .listCong inner, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | list ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | list hb' => exact .listCong (consistent_of_refines inner ha' hb')
  | _, _, _, b, .productCong fields, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | product ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | product hb' =>
              exact .productCong (consistentArgs_of_refines fields ha' hb')
  | _, _, _, b, .arrowCong args result he, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | arrow hda hca =>
          cases hb with
          | unknown => exact .unknownR _
          | arrow hdb hcb =>
              exact .arrowCong (consistentArgs_of_refines args hda hdb)
                (consistent_of_refines result hca hcb) he
  | _, _, _, b, .unionL hleft hright, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | union hla hra =>
          exact .unionL (consistent_of_refines hleft hla hb)
            (consistent_of_refines hright hra hb)
  | _, _, a, _, .unionR1 inner, ha, hb => by
      cases hb with
      | unknown => exact .unknownR a
      | union hlb _ => exact .unionR1 (consistent_of_refines inner ha hlb)
  | _, _, a, _, .unionR2 inner, ha, hb => by
      cases hb with
      | unknown => exact .unknownR a
      | union _ hrb => exact .unionR2 (consistent_of_refines inner ha hrb)
  | _, _, _, b, .newtypeCong inner, ha, hb => by
      cases ha with
      | unknown => exact .unknownL b
      | newtype ha' =>
          cases hb with
          | unknown => exact .unknownR _
          | newtype hb' =>
              exact .newtypeCong (consistent_of_refines inner ha' hb')

/-- Spine version of `consistent_of_refines`. -/
theorem consistentArgs_of_refines :
    ∀ {as' bs' as bs : TyArgs}, ConsistentArgs as' bs' →
      RefinesArgs as' as → RefinesArgs bs' bs → ConsistentArgs as bs
  | _, _, _, _, .nil, ha, hb => by
      cases ha
      cases hb
      exact .nil
  | _, _, _, _, .cons head tail, ha, hb => by
      cases ha with
      | cons hha hta =>
          cases hb with
          | cons hhb htb =>
              exact .cons (consistent_of_refines head hha hhb)
                (consistentArgs_of_refines tail hta htb)

end

/-- **Seam law 5 — conflict persistence**: a witnessed inconsistency at any
precision survives every refinement of both sides.  Conflict caches never
need invalidation by *learning*; only by revision change of the types
themselves. -/
theorem conflict_persists {a a' b b' : Ty}
    (ha : Refines a' a) (hb : Refines b' b)
    (h : consistent? a b = false) : consistent? a' b' = false := by
  cases hcheck : consistent? a' b' with
  | false => rfl
  | true =>
      have : Consistent a b :=
        consistent_of_refines (consistent?_sound _ _ hcheck) ha hb
      simp [consistent?_complete _ _ this] at h

/-- Persistence applied: `list ? ≁ num`, and the refinement `list str` of
`list ?` still conflicts — derived from the theorem, not rechecked. -/
example : consistent? (.list (.prim .str)) (.prim .num) = false :=
  conflict_persists (.list (.unknown _)) (.prim _) (by simp [consistent?])

/-- **The asymmetry**: gradual *acceptance* is not persistent — `? ~ num`
holds while its refinement `str` gives `str ≁ num`.  Acceptance through
ignorance is permission to run, never a promise; this is why gradual
classifications carry no license. -/
example :
    consistent? .unknown (.prim .num) = true ∧
    consistent? (.prim .str) (.prim .num) = false ∧
    Refines (.prim .str) .unknown := by
  refine ⟨by simp, by simp [consistent?], .unknown _⟩

/-! ## §4 Rigidity: exact types admit no proper refinement -/

mutual

/-- **Seam law 6 — rigidity**: an exact type has no holes to fill, so its
only refinement is itself.  Exact judgments therefore never move as
knowledge grows. -/
theorem exact_rigid : ∀ {t' t : Ty}, exactTy t = true → Refines t' t → t' = t
  | _, _, hexact, .unknown _ => by simp [exactTy] at hexact
  | _, _, _, .prim _ => rfl
  | _, _, hexact, .list h => by
      simp only [exactTy] at hexact
      rw [exact_rigid hexact h]
  | _, _, hexact, .product h => by
      simp only [exactTy] at hexact
      rw [exactArgs_rigid hexact h]
  | _, _, hexact, .arrow hd hc => by
      simp only [exactTy, Bool.and_eq_true] at hexact
      rw [exactArgs_rigid hexact.1 hd, exact_rigid hexact.2 hc]
  | _, _, hexact, .union hl hr => by
      simp only [exactTy, Bool.and_eq_true] at hexact
      rw [exact_rigid hexact.1 hl, exact_rigid hexact.2 hr]
  | _, _, hexact, .newtype h => by
      simp only [exactTy] at hexact
      rw [exact_rigid hexact h]

/-- Spine version of `exact_rigid`. -/
theorem exactArgs_rigid : ∀ {ts' ts : TyArgs}, exactArgs ts = true →
    RefinesArgs ts' ts → ts' = ts
  | _, _, _, .nil => rfl
  | _, _, hexact, .cons hh ht => by
      simp only [exactArgs, Bool.and_eq_true] at hexact
      rw [exact_rigid hexact.1 hh, exactArgs_rigid hexact.2 ht]

end

/-- Rigidity applied: nothing properly refines `num`. -/
example (t : Ty) (h : Refines t (.prim .num)) : t = .prim .num :=
  exact_rigid (by simp [exactTy]) h

/-! ## §5 The optimization license

The authority to select a typed fast path.  Constructible only from
fully exact evidence — the maximal-native-calculus discipline: the kernel
computes with what it knows; ignorance runs but never authorizes. -/

structure OptLicense where
  actual : Ty
  expected : Ty
  card : Card
  demand : ArrowMode
  actual_exact : exactTy actual = true
  expected_exact : exactTy expected = true
  flows : consistent? actual expected = true
  fits : modeFits (.grade card) demand = true

/-- **Seam law 3 — no license from gradual (actual side)**. -/
theorem no_inexact_actual_license (t : Ty) (h : exactTy t = false) :
    ¬ ∃ l : OptLicense, l.actual = t := by
  rintro ⟨l, rfl⟩
  rw [l.actual_exact] at h
  simp at h

/-- Seam law 3, expected side. -/
theorem no_inexact_expected_license (t : Ty) (h : exactTy t = false) :
    ¬ ∃ l : OptLicense, l.expected = t := by
  rintro ⟨l, rfl⟩
  rw [l.expected_exact] at h
  simp at h

/-- `?Unknown` itself can never appear as a license's actual type. -/
theorem no_unknown_license : ¬ ∃ l : OptLicense, l.actual = .unknown :=
  no_inexact_actual_license .unknown (by simp [exactTy])

/-- A license is refinement-eternal: both of its types are rigid, so no
future knowledge can move the judgment it packages. -/
theorem license_rigid (l : OptLicense) {a' e' : Ty}
    (ha : Refines a' l.actual) (he : Refines e' l.expected) :
    a' = l.actual ∧ e' = l.expected :=
  ⟨exact_rigid l.actual_exact ha, exact_rigid l.expected_exact he⟩

/-! ## §6 The classifier -/

/-- The three seam kinds. -/
inductive SeamKind where
  | exact | gradual | conflict
  deriving DecidableEq, Repr

/-- Classify one judged occurrence.  A refutation is a conflict; ignorance
(undetermined) and exhaustion (incomplete) are gradual; an established
verdict is exact only when both sides are `?Unknown`-free.  Established
emptiness deliberately classifies gradual: withholding a license is always
sound (fewer fast paths, identical answers). -/
def classifyKind (evidence : RuntimeEvidence) (expected : Ty)
    (demand : ArrowMode) : SeamKind :=
  match checkEvidence evidence expected demand with
  | .refuted _ => .conflict
  | .undetermined => .gradual
  | .incomplete => .gradual
  | .established =>
      match evidence.result with
      | .typed actual =>
          if exactTy actual && exactTy expected then .exact else .gradual
      | _ => .gradual

/-- An established verdict on typed evidence pins both boundary checks. -/
theorem established_typed_facts {evidence : RuntimeEvidence} {expected : Ty}
    {demand : ArrowMode} {actual : Ty}
    (hres : evidence.result = .typed actual)
    (hcheck : checkEvidence evidence expected demand = .established) :
    consistent? actual expected = true ∧
      modeFits (.grade evidence.card) demand = true := by
  cases evidence with
  | mk result card stage facts =>
      have hres' : result = ResultEvidence.typed actual := hres
      subst hres'
      by_cases hc : consistent? actual expected
      · by_cases hm : modeFits (.grade card) demand
        · exact ⟨hc, hm⟩
        · simp [checkEvidence, hc, hm] at hcheck
      · simp [checkEvidence, hc] at hcheck

/-- **Seam law 1 — ignorance is gradual**: unknown evidence always
classifies gradual, whatever is expected or demanded. -/
@[simp] theorem classifyKind_unknown (card : Card) (stage : Stage)
    (facts : BoundaryFacts) (expected : Ty) (demand : ArrowMode) :
    classifyKind { result := .unknown, card, stage, facts } expected demand
      = .gradual := rfl

/-- Ignorance can never manufacture a conflict. -/
theorem unknown_never_conflicts (card : Card) (stage : Stage)
    (facts : BoundaryFacts) (expected : Ty) (demand : ArrowMode) :
    classifyKind { result := .unknown, card, stage, facts } expected demand
      ≠ .conflict := by simp

/-- **Seam law 2 — conflicts are witnessed**: every conflict classification
exposes a valid, replayable `EvidenceConflict`. -/
theorem conflict_kind_witness (evidence : RuntimeEvidence) (expected : Ty)
    (demand : ArrowMode)
    (h : classifyKind evidence expected demand = .conflict) :
    ∃ w, checkEvidence evidence expected demand = .refuted w ∧
      w.valid = true := by
  unfold classifyKind at h
  cases hcheck : checkEvidence evidence expected demand with
  | refuted w =>
      exact ⟨w, rfl, checkEvidence_refuted_valid _ _ _ _ hcheck⟩
  | undetermined => rw [hcheck] at h; simp at h
  | incomplete => rw [hcheck] at h; simp at h
  | established =>
      rw [hcheck] at h
      cases hres : evidence.result with
      | unknown => rw [hres] at h; simp at h
      | empty => rw [hres] at h; simp at h
      | typed actual =>
          rw [hres] at h
          by_cases hexact : (exactTy actual && exactTy expected) = true
          · simp [hexact] at h
          · simp [hexact] at h

/-- **Seam law 4 — exact classifications license**: every exact
classification constructs a genuine `OptLicense` for its occurrence. -/
theorem exact_kind_license (evidence : RuntimeEvidence) (expected : Ty)
    (demand : ArrowMode)
    (h : classifyKind evidence expected demand = .exact) :
    ∃ l : OptLicense, l.expected = expected ∧ l.demand = demand ∧
      l.card = evidence.card ∧ evidence.result = .typed l.actual := by
  unfold classifyKind at h
  cases hcheck : checkEvidence evidence expected demand with
  | refuted w => rw [hcheck] at h; simp at h
  | undetermined => rw [hcheck] at h; simp at h
  | incomplete => rw [hcheck] at h; simp at h
  | established =>
      rw [hcheck] at h
      cases hres : evidence.result with
      | unknown => rw [hres] at h; simp at h
      | empty => rw [hres] at h; simp at h
      | typed actual =>
          rw [hres] at h
          by_cases hexact : (exactTy actual && exactTy expected) = true
          · have hparts : exactTy actual = true ∧ exactTy expected = true := by
              simpa [Bool.and_eq_true] using hexact
            obtain ⟨hflows, hfits⟩ := established_typed_facts hres hcheck
            exact ⟨{ actual, expected, card := evidence.card, demand
                     actual_exact := hparts.1
                     expected_exact := hparts.2
                     flows := hflows
                     fits := hfits }, rfl, rfl, rfl, rfl⟩
          · simp [hexact] at h

/-- **The seam principle, composed**: `?Unknown` preserves execution
without licensing typed optimization — ignorance always classifies
gradual, and no license over an inexact type is constructible. -/
theorem unknown_preserves_execution_without_license :
    (∀ (card : Card) (stage : Stage) (facts : BoundaryFacts)
        (expected : Ty) (demand : ArrowMode),
      classifyKind { result := .unknown, card, stage, facts } expected demand
        = .gradual) ∧
    ¬ ∃ l : OptLicense, l.actual = .unknown :=
  ⟨fun _ _ _ _ _ => rfl, no_unknown_license⟩

/-! ### Mobility witnesses (seam law 7)

Gradual is the only mobile kind: as evidence upgrades, the same occurrence
may become exact, become conflict, or stay gradual.  Exact never moves
(rigidity, §4); conflict never moves (persistence, §3). -/

def unknownEvidence : RuntimeEvidence :=
  { result := .unknown, card := .det, stage := .evaluated, facts := {} }

/-- Mobility, starting point: ignorance is gradual. -/
example : classifyKind unknownEvidence (.prim .num) (.grade .det)
    = .gradual := rfl

/-- Mobility → exact: the upgrade to exact agreeing evidence licenses. -/
example : classifyKind numberEvidence (.prim .num) (.grade .det)
    = .exact := by
  simp [classifyKind, checkEvidence, numberEvidence, exactTy]

/-- Mobility → conflict: the upgrade to exact disagreeing evidence
produces a witnessed conflict. -/
example : classifyKind numberEvidence (.prim .str) (.grade .det)
    = .conflict := by
  simp [classifyKind, checkEvidence, numberEvidence, consistent?]

/-- Mobility → gradual: an upgrade that still contains `?Unknown` keeps
executing without a license — established is necessary but not sufficient
for exactness. -/
example :
    classifyKind
      { result := .typed .unknown, card := .det, stage := .evaluated,
        facts := {} } (.prim .num) (.grade .det) = .gradual := by
  simp [classifyKind, checkEvidence, exactTy]

/-- Established emptiness stays gradual: a sound under-approximation
(dead-branch licensing is future work, and withholding never lies). -/
example :
    classifyKind
      { result := .empty, card := .det, stage := .evaluated, facts := {} }
      (.prim .num) (.grade .det) = .gradual := by
  simp [classifyKind, checkEvidence]

/-! ## §7 Ordered seam rule inventory (H7 extension)

The langdef mirror's rule names for this layer, in semantic order:
exactness before classification; within classification, conflict first
(mirrors `checkEvidence`'s refutation priority), then the two ignorance
outcomes, then the established split. -/

inductive SeamRule where
  | exactTyUnknown | exactTyPrim | exactTyList | exactTyProduct
  | exactTyArrow | exactTyUnion | exactTyNewtype
  | exactArgsNil | exactArgsCons
  | seamConflict | seamUndetermined | seamIncomplete
  | seamEstablishedExact | seamEstablishedInexact | seamEstablishedUntyped
  deriving DecidableEq, Repr

def SeamRule.name : SeamRule → String
  | .exactTyUnknown => "v3-exact-ty-unknown"
  | .exactTyPrim => "v3-exact-ty-prim"
  | .exactTyList => "v3-exact-ty-list"
  | .exactTyProduct => "v3-exact-ty-product"
  | .exactTyArrow => "v3-exact-ty-arrow"
  | .exactTyUnion => "v3-exact-ty-union"
  | .exactTyNewtype => "v3-exact-ty-newtype"
  | .exactArgsNil => "v3-exact-args-nil"
  | .exactArgsCons => "v3-exact-args-cons"
  | .seamConflict => "v3-seam-conflict"
  | .seamUndetermined => "v3-seam-undetermined"
  | .seamIncomplete => "v3-seam-incomplete"
  | .seamEstablishedExact => "v3-seam-established-exact"
  | .seamEstablishedInexact => "v3-seam-established-inexact"
  | .seamEstablishedUntyped => "v3-seam-established-untyped"

def seamRules : List SeamRule :=
  [ .exactTyUnknown
  , .exactTyPrim
  , .exactTyList
  , .exactTyProduct
  , .exactTyArrow
  , .exactTyUnion
  , .exactTyNewtype
  , .exactArgsNil
  , .exactArgsCons
  , .seamConflict
  , .seamUndetermined
  , .seamIncomplete
  , .seamEstablishedExact
  , .seamEstablishedInexact
  , .seamEstablishedUntyped ]

def seamRuleNames : List String := seamRules.map SeamRule.name

theorem seamRules_nodup : seamRules.Nodup := by decide

theorem seamRuleNames_nodup : seamRuleNames.Nodup := by decide

theorem seamRules_count : seamRules.length = 15 := rfl

/-! ## §8 Handoff notes

For the v3 lane: wire `classifyKind` behind the existing evidence layer —
`checkEvidence` already computes the outcome, so the seam adds only the
exactness test and the license constructor; extend H7 parity with the
fifteen ordered rules above; the license is the sole input to any typed
fast-path selection, and `conflict_persists`/`exact_rigid` are the cache
laws (conflicts and licenses are keyed by revision only, never invalidated
by monotone knowledge growth; gradual outcomes are the only recomputable
kind).

For the MeTTa Native lane: the seam transports verbatim — replace `Ty` by
the native type syntax and `checkEvidence` by the corresponding boundary
judgment; laws 1–7 are the coherence obligations of the
Exact/Gradual/Conflict runtime waist, with `Refines` as the precision
order and `OptLicense` as the admitted-fact shape NIK records per
revision. -/

def seamHandoff : List String :=
  [ "S1-wire: classifyKind behind the live evidence providers; licenses \
     become the only typed-fast-path inputs."
  , "S2-parity: extend the ordered langdef inventory with the fifteen \
     v3-exact-*/v3-seam-* rules."
  , "S3-cache: conflict/license caches keyed by revision only; \
     conflict_persists and exact_rigid are the invalidation laws."
  , "S4-native: port the seam to MeTTa Native types for the Prime waist; \
     laws 1-7 are the coherence obligations." ]

theorem seamHandoff_count : seamHandoff.length = 4 := rfl

end Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
