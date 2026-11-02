import Mettapedia.Logic.HOL.PredicateSigma

/-!
# Retained projection and reconstruction proofs for guarded Sigma

The two projection equations are explicit closed-law proofs. Opening the
existential image exposes the same first/second witnesses for reconstruction,
domain membership and the dependent family. No witness is selected by choice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateSigma

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {space : Ty Base}

def firstLaw (ops : Operations Const space) : ClosedFormula Const :=
  .all (.all (.eq (first ops (pair ops (.var (.vs .vz)) (.var .vz))) (.var (.vs .vz))))

def secondLaw (ops : Operations Const space) : ClosedFormula Const :=
  .all (.all (.eq (second ops (pair ops (.var (.vs .vz)) (.var .vz))) (.var .vz)))

theorem firstLaw_form (ops : Operations Const space) : weakenCtx Γ (firstLaw ops) =
    .all (.all (.eq (first ops (pair ops (.var (.vs .vz)) (.var .vz))) (.var (.vs .vz)))) := by
  let mapping : Rename Base [] Γ := fun index => nomatch index
  have fromEmpty : HOL.rename mapping (firstLaw ops) = weakenCtx Γ (firstLaw ops) := by
    simpa only [weakenCtx_nil] using rename_weakenCtx mapping (firstLaw ops)
  rw [← fromEmpty]
  simp only [firstLaw, first, pair, HOL.rename, rename_weakenCtx, Rename.lift]

theorem secondLaw_form (ops : Operations Const space) : weakenCtx Γ (secondLaw ops) =
    .all (.all (.eq (second ops (pair ops (.var (.vs .vz)) (.var .vz))) (.var .vz))) := by
  let mapping : Rename Base [] Γ := fun index => nomatch index
  have fromEmpty : HOL.rename mapping (secondLaw ops) = weakenCtx Γ (secondLaw ops) := by
    simpa only [weakenCtx_nil] using rename_weakenCtx mapping (secondLaw ops)
  rw [← fromEmpty]
  simp only [secondLaw, second, pair, HOL.rename, rename_weakenCtx, Rename.lift]

variable {Δ : List (Formula Const Γ)}

def pair_first (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (firstLaw ops))) :
    ProofSyntax Const Δ (.eq (first ops (pair ops head tail)) head) := by
  have normalized := ProofSyntax.castIndices rfl (firstLaw_form (Γ := Γ) ops) law
  have once := ProofSyntax.allE head normalized
  apply ProofSyntax.castIndices rfl ?_ (.allE tail once)
  simp [first, pair, instantiate, HOL.subst, Subst.single, Subst.lift]
  exact instantiate_weaken tail head

def pair_second (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (secondLaw ops))) :
    ProofSyntax Const Δ (.eq (second ops (pair ops head tail)) tail) := by
  have normalized := ProofSyntax.castIndices rfl (secondLaw_form (Γ := Γ) ops) law
  have once := ProofSyntax.allE head normalized
  apply ProofSyntax.castIndices rfl ?_ (.allE tail once)
  simp [second, pair, instantiate, HOL.subst, Subst.single, Subst.lift]
  exact instantiate_weaken tail head

theorem pair_first_free (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (firstLaw ops))) (free : law.FunctionExtensionalityFree) :
    (pair_first ops head tail law).FunctionExtensionalityFree := by
  simp [pair_first, ProofSyntax.FunctionExtensionalityFree, free]

theorem pair_second_free (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (secondLaw ops))) (free : law.FunctionExtensionalityFree) :
    (pair_second ops head tail law).FunctionExtensionalityFree := by
  simp [pair_second, ProofSyntax.FunctionExtensionalityFree, free]

@[simp] theorem pair_first_free_iff (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (firstLaw ops))) :
    (pair_first ops head tail law).FunctionExtensionalityFree ↔ law.FunctionExtensionalityFree := by
  simp [pair_first, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem pair_second_free_iff (ops : Operations Const space) (head tail : Term Const Γ space)
    (law : ProofSyntax Const Δ (weakenCtx Γ (secondLaw ops))) :
    (pair_second ops head tail law).FunctionExtensionalityFree ↔ law.FunctionExtensionalityFree := by
  simp [pair_second, ProofSyntax.FunctionExtensionalityFree]

def decoded (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) : Formula Const Γ :=
  .and (.eq (pair ops (first ops point) (second ops point)) point)
    (.and (.app domain (first ops point)) (familyAt family (first ops point) (second ops point)))

@[simp] theorem decoded_weaken (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) {type : Ty Base} :
    weaken (σ := type) (decoded ops domain family point) =
      decoded ops (weaken domain) (weaken family) (weaken point) := by
  simp only [decoded, familyAt, pair, first, second, weaken, HOL.rename, rename_weakenCtx]

private def weakenClosed {type : Ty Base} (closed : ClosedFormula Const)
    (proof : ProofSyntax Const Δ (weakenCtx Γ closed)) :
    ProofSyntax Const (weakenHyps (σ := type) Δ) (weakenCtx (type :: Γ) closed) := by
  apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof proof)
  simp only [weaken, rename_weakenCtx]

private theorem weakenClosed_free {type : Ty Base} (closed : ClosedFormula Const)
    (proof : ProofSyntax Const Δ (weakenCtx Γ closed)) (free : proof.FunctionExtensionalityFree) :
    (weakenClosed (type := type) closed proof).FunctionExtensionalityFree := by
  simp [weakenClosed, PredicateFixedPoint.weakenProof, free]

@[simp] private theorem weakenClosed_free_iff {type : Ty Base} (closed : ClosedFormula Const)
    (proof : ProofSyntax Const Δ (weakenCtx Γ closed)) :
    (weakenClosed (type := type) closed proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [weakenClosed, PredicateFixedPoint.weakenProof]

def headClause (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point head : Term Const Γ space) : Formula Const Γ :=
  .ex (.and (.eq (pair ops (weaken head) (.var .vz)) (weaken point))
    (.and (.app (weaken domain) (weaken head)) (familyAt (weaken family) (weaken head) (.var .vz))))

def projection (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space)
    (firstRoot : ProofSyntax Const Δ (weakenCtx Γ (firstLaw ops)))
    (secondRoot : ProofSyntax Const Δ (weakenCtx Γ (secondLaw ops)))
    (member : ProofSyntax Const Δ (.app (sigma ops domain family) point)) :
    ProofSyntax Const Δ (decoded ops domain family point) := by
  have existsPair := ProofSyntax.impE (.eqPropEL (beta ops domain family point)) member
  refine .exE existsPair ?_
  refine .exE (.hyp 0) ?_
  let firstClause := headClause ops (weaken domain) (weaken family) (weaken point) (.var .vz)
  let head : Term Const (space :: space :: Γ) space := .var (.vs .vz)
  let tail : Term Const (space :: space :: Γ) space := .var .vz
  let A : Term Const (space :: space :: Γ) (space ⇒ .prop) := weaken (weaken domain)
  let F : Term Const (space :: space :: Γ) (space ⇒ space ⇒ .prop) := weaken (weaken family)
  let p : Term Const (space :: space :: Γ) space := weaken (weaken point)
  let body : Formula Const (space :: space :: Γ) :=
    .and (.eq (pair ops head tail) p) (.and (.app A head) (familyAt F head tail))
  let assumptions := body :: weakenHyps (firstClause :: weakenHyps Δ)
  have firstRaised : ProofSyntax Const assumptions (weakenCtx (space :: space :: Γ) (firstLaw ops)) :=
    (weakenClosed (firstLaw ops) ((weakenClosed (firstLaw ops) firstRoot).prepend firstClause)).prepend body
  have secondRaised : ProofSyntax Const assumptions (weakenCtx (space :: space :: Γ) (secondLaw ops)) :=
    (weakenClosed (secondLaw ops) ((weakenClosed (secondLaw ops) secondRoot).prepend firstClause)).prepend body
  have equal : ProofSyntax Const assumptions (.eq (pair ops head tail) p) := .andEL (.hyp 0)
  have headMember : ProofSyntax Const assumptions (.app A head) := .andEL (.andER (.hyp 0))
  have tailMember : ProofSyntax Const assumptions (familyAt F head tail) := .andER (.andER (.hyp 0))
  have firstEqual : ProofSyntax Const assumptions (.eq (first ops p) head) :=
    .eqTrans (.eqSymm (.eqAppArg (weakenCtx _ ops.first) equal)) (pair_first ops head tail firstRaised)
  have secondEqual : ProofSyntax Const assumptions (.eq (second ops p) tail) :=
    .eqTrans (.eqSymm (.eqAppArg (weakenCtx _ ops.second) equal)) (pair_second ops head tail secondRaised)
  have pairEqual : ProofSyntax Const assumptions (.eq (pair ops (first ops p) (second ops p)) (pair ops head tail)) :=
    .eqTrans (.eqApp (second ops p) (.eqAppArg (weakenCtx _ ops.pair) firstEqual))
      (.eqAppArg (.app (weakenCtx _ ops.pair) head) secondEqual)
  have familyEqual : ProofSyntax Const assumptions
      (.eq (familyAt F (first ops p) (second ops p)) (familyAt F head tail)) :=
    .eqTrans (.eqApp (second ops p) (.eqAppArg F firstEqual)) (.eqAppArg (.app F head) secondEqual)
  have result : ProofSyntax Const assumptions (decoded ops A F p) :=
    .andI (.eqTrans pairEqual equal)
      (.andI (.impE (.eqPropER (.eqAppArg A firstEqual)) headMember)
        (.impE (.eqPropER familyEqual) tailMember))
  apply ProofSyntax.castIndices rfl ?_ result
  simp only [decoded_weaken]
  rfl

theorem projection_free (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space)
    (firstRoot : ProofSyntax Const Δ (weakenCtx Γ (firstLaw ops)))
    (secondRoot : ProofSyntax Const Δ (weakenCtx Γ (secondLaw ops)))
    (member : ProofSyntax Const Δ (.app (sigma ops domain family) point))
    (firstFree : firstRoot.FunctionExtensionalityFree) (secondFree : secondRoot.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (projection ops domain family point firstRoot secondRoot member).FunctionExtensionalityFree := by
  simp [projection, ProofSyntax.FunctionExtensionalityFree, beta_free, ProofSyntax.prepend,
    firstFree, secondFree, memberFree]

#print axioms projection
#print axioms projection_free

end Mettapedia.Logic.HOL.PredicateSigma
