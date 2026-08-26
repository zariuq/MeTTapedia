import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

/-!
# Replayable class-aware ParserPack certificates

The operational ParserPack semantics is proof-relevant, while a native GLL or
GLR backend emits finite data.  This module defines the data boundary between
those layers.  Certificates retain physical production positions, exact input
spans, terminal steps, recursive alternatives, and zero-width steps.  They do
not contain Lean derivation objects.

`Replays` checks certificate data against the supplied parser profile, plan,
and scalar input.  The main equivalence proves that admitted certificates have
exactly the same fibres as `ParserPackDerivesAt`.  In particular, two equal
production payloads at different positions remain different certificates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

mutual
  /-- Finite data for one lexical or structural ParserPack derivation.
  Production identity is its physical position in the corresponding ordered
  plan table. -/
  inductive Certificate where
    | lexical (production : Nat) (matcher : TerminalMatcher)
        (start stop : Nat)
    | structural (production start stop : Nat)
        (body : ItemsCertificate)
    deriving DecidableEq, Repr

  /-- Finite data for left-to-right execution of a structural item vector.
  The redundant cursors are intentional: replay rejects a corrupted seam
  instead of repairing it from adjacent nodes. -/
  inductive ItemsCertificate where
    | nil (cursor : Nat)
    | terminal (matcher : TerminalMatcher) (start stop : Nat)
        (rest : ItemsCertificate)
    | nonterminal (resultSort : String) (start stop : Nat)
        (head : Certificate) (rest : ItemsCertificate)
    deriving DecidableEq, Repr
end

set_option autoImplicit true in
mutual
  /-- Exact replay of finite certificate data against a supplied ParserPack
  plan and scalar input.  This relation validates the plan row, matcher,
  result sort, rule label, spans, and CST output rather than trusting fields
  copied into the certificate. -/
  inductive Replays (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat) :
      Certificate → String → Nat → Nat → CST → Type where
    | lexical
        (position : Nat)
        (valid : position < plan.lexical.productions.length)
        {matcher : TerminalMatcher} {resultSort ruleLabel : String}
        {children : List CST}
        (matcher_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).matcher = matcher)
        (resultSort_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).resultSort =
            resultSort)
        (ruleLabel_exact :
          (plan.lexical.productions.get ⟨position, valid⟩).label = ruleLabel)
        (matched : CSTTerminalMatchesAt profile input matcher
          start stop children) :
        Replays profile plan input (.lexical position matcher start stop)
          resultSort start stop (.node ruleLabel start stop children)
    | structural
        (position : Nat) (valid : position < plan.structural.length)
        {resultSort ruleLabel : String} {bodyCertificate : ItemsCertificate}
        (resultSort_exact :
          (plan.structural.get ⟨position, valid⟩).resultSort = resultSort)
        (ruleLabel_exact :
          (plan.structural.get ⟨position, valid⟩).label = ruleLabel)
        (body : ItemsReplays profile plan input bodyCertificate
          (plan.structural.get ⟨position, valid⟩).items
          start stop children) :
        Replays profile plan input
          (.structural position start stop bodyCertificate)
          resultSort start stop (.node ruleLabel start stop children)

  /-- Exact replay of the item evidence carried by a structural certificate.
  Structural terminals constrain the cursor but remain absent from CST
  children, exactly as in `ParserPackItemsDeriveAt`. -/
  inductive ItemsReplays (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat) :
      ItemsCertificate → List PackItem → Nat → Nat → List CST → Type where
    | nil :
        ItemsReplays profile plan input (.nil cursor) [] cursor cursor []
    | terminal
        (matched : TerminalMatchesAt profile input matcher start middle)
        (rest : ItemsReplays profile plan input restCertificate items
          middle stop children) :
        ItemsReplays profile plan input
          (.terminal matcher start middle restCertificate)
          (.terminal matcher :: items) start stop children
    | nonterminal
        (head : Replays profile plan input headCertificate resultSort
          start middle tree)
        (rest : ItemsReplays profile plan input restCertificate items
          middle stop children) :
        ItemsReplays profile plan input
          (.nonterminal resultSort start middle
            headCertificate restCertificate)
          (.nonterminal resultSort :: items) start stop (tree :: children)
end

mutual
  /-- Erase a target derivation to finite certificate data. -/
  def Certificate.ofDerivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {resultSort : String} {start stop : Nat}
      {tree : CST} :
      ParserPackDerivesAt profile plan input resultSort start stop tree →
        Certificate
    | @ParserPackDerivesAt.lexical _ _ _ derivationStart derivationStop
        position _ matcher _ _ _ _ _ _ _ =>
        .lexical position matcher derivationStart derivationStop
    | .structural position _ _ _ body =>
        .structural position start stop (ItemsCertificate.ofDerivation body)

  /-- Erase target item execution to finite certificate data. -/
  def ItemsCertificate.ofDerivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat}
      {children : List CST} :
      ParserPackItemsDeriveAt profile plan input items start stop children →
        ItemsCertificate
    | @ParserPackItemsDeriveAt.nil _ _ _ cursor => .nil cursor
    | @ParserPackItemsDeriveAt.terminal _ _ _ matcher
        derivationStart middle _ _ _ _ rest =>
        .terminal matcher derivationStart middle
          (ItemsCertificate.ofDerivation rest)
    | @ParserPackItemsDeriveAt.nonterminal _ _ _ resultSort
        derivationStart middle _ _ _ _ head rest =>
        .nonterminal resultSort derivationStart middle
          (Certificate.ofDerivation head)
          (ItemsCertificate.ofDerivation rest)
end

mutual
  /-- Every operational derivation produces replay evidence for its erased
  certificate. -/
  def Replays.ofDerivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {resultSort : String} {start stop : Nat}
      {tree : CST} :
      (derivation : ParserPackDerivesAt profile plan input
        resultSort start stop tree) →
      Replays profile plan input (Certificate.ofDerivation derivation)
        resultSort start stop tree
    | .lexical position valid matcherExact resultSortExact ruleLabelExact
        matched =>
        .lexical position valid matcherExact resultSortExact ruleLabelExact
          matched
    | .structural position valid resultSortExact ruleLabelExact body =>
        .structural position valid resultSortExact ruleLabelExact
          (ItemsReplays.ofDerivation body)

  /-- Every operational item derivation produces replay evidence for its
  erased item certificate. -/
  def ItemsReplays.ofDerivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat}
      {children : List CST} :
      (derivation : ParserPackItemsDeriveAt profile plan input
        items start stop children) →
      ItemsReplays profile plan input
        (ItemsCertificate.ofDerivation derivation)
        items start stop children
    | .nil => .nil
    | .terminal matched rest =>
        .terminal matched (ItemsReplays.ofDerivation rest)
    | .nonterminal head rest =>
        .nonterminal (Replays.ofDerivation head)
          (ItemsReplays.ofDerivation rest)
end

mutual
  /-- Replay evidence reconstructs an operational ParserPack derivation. -/
  def Replays.derivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate}
      {resultSort : String} {start stop : Nat} {tree : CST} :
      Replays profile plan input certificate resultSort start stop tree →
        ParserPackDerivesAt profile plan input resultSort start stop tree
    | .lexical position valid matcherExact resultSortExact ruleLabelExact
        matched =>
        .lexical position valid matcherExact resultSortExact ruleLabelExact
          matched
    | .structural position valid resultSortExact ruleLabelExact body =>
        .structural position valid resultSortExact ruleLabelExact
          (ItemsReplays.derivation body)

  /-- Item replay evidence reconstructs operational item execution. -/
  def ItemsReplays.derivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate}
      {items : List PackItem} {start stop : Nat} {children : List CST} :
      ItemsReplays profile plan input certificate items start stop children →
        ParserPackItemsDeriveAt profile plan input items start stop children
    | .nil => .nil
    | .terminal matched rest =>
        .terminal matched (ItemsReplays.derivation rest)
    | .nonterminal head rest =>
        .nonterminal (Replays.derivation head)
          (ItemsReplays.derivation rest)
end

@[simp] theorem Replays.derivation_ofDerivation
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat}
    {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree) :
    (Replays.ofDerivation derivation).derivation = derivation := by
  induction derivation using ParserPackDerivesAt.rec
    (motive_2 := fun _ _ _ _ itemDerivation =>
      (ItemsReplays.ofDerivation itemDerivation).derivation =
        itemDerivation) with
  | lexical => simp [Replays.ofDerivation, Replays.derivation]
  | structural _ _ _ _ _ bodyIH =>
      simp [Replays.ofDerivation, Replays.derivation, bodyIH]
  | nil => simp [ItemsReplays.ofDerivation, ItemsReplays.derivation]
  | terminal _ _ restIH =>
      simp [ItemsReplays.ofDerivation, ItemsReplays.derivation, restIH]
  | nonterminal _ _ headIH restIH =>
      simp [ItemsReplays.ofDerivation, ItemsReplays.derivation,
        headIH, restIH]

@[simp] theorem ItemsReplays.derivation_ofDerivation
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {items : List PackItem} {start stop : Nat}
    {children : List CST}
    (derivation : ParserPackItemsDeriveAt profile plan input
      items start stop children) :
    (ItemsReplays.ofDerivation derivation).derivation = derivation := by
  induction derivation using ParserPackItemsDeriveAt.rec
    (motive_1 := fun _ _ _ _ completeDerivation =>
      (Replays.ofDerivation completeDerivation).derivation =
        completeDerivation) with
  | lexical => simp [Replays.ofDerivation, Replays.derivation]
  | structural _ _ _ _ _ bodyIH =>
      simp [Replays.ofDerivation, Replays.derivation, bodyIH]
  | nil => simp [ItemsReplays.ofDerivation, ItemsReplays.derivation]
  | terminal _ _ restIH =>
      simp [ItemsReplays.ofDerivation, ItemsReplays.derivation, restIH]
  | nonterminal _ _ headIH restIH =>
      simp [ItemsReplays.ofDerivation, ItemsReplays.derivation,
        headIH, restIH]

mutual
  /-- Encoding the derivation reconstructed by replay returns the exact
  certificate that was replayed. -/
  @[simp] theorem Replays.certificate_derivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate}
      {resultSort : String} {start stop : Nat} {tree : CST}
      (replay : Replays profile plan input certificate
        resultSort start stop tree) :
      Certificate.ofDerivation replay.derivation = certificate := by
    cases replay with
    | lexical => rfl
    | structural position valid resultSortExact ruleLabelExact body =>
        simp only [Replays.derivation, Certificate.ofDerivation]
        rw [ItemsReplays.certificate_derivation body]

  /-- Encoding reconstructed item execution returns the exact item
  certificate that was replayed. -/
  @[simp] theorem ItemsReplays.certificate_derivation
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate}
      {items : List PackItem} {start stop : Nat} {children : List CST}
      (replay : ItemsReplays profile plan input certificate
        items start stop children) :
      ItemsCertificate.ofDerivation replay.derivation = certificate := by
    cases replay with
    | nil => rfl
    | terminal matched rest =>
        simp only [ItemsReplays.derivation,
          ItemsCertificate.ofDerivation]
        rw [ItemsReplays.certificate_derivation rest]
    | nonterminal head rest =>
        simp only [ItemsReplays.derivation,
          ItemsCertificate.ofDerivation]
        rw [Replays.certificate_derivation head,
          ItemsReplays.certificate_derivation rest]
end

mutual
  /-- Replay evidence is canonical once its finite certificate and semantic
  indices are fixed. -/
  theorem Replays.unique
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate}
      {resultSort : String} {start stop : Nat} {tree : CST}
      (left right : Replays profile plan input certificate
        resultSort start stop tree) : left = right := by
    cases left with
    | lexical _ _ _ _ _ leftMatched =>
        cases right with
        | lexical _ _ _ _ _ rightMatched =>
            congr
            exact cstTerminalRecognition_unique leftMatched rightMatched
    | structural _ _ _ _ leftBody =>
        cases right with
        | structural _ _ _ _ rightBody =>
            congr
            exact ItemsReplays.unique leftBody rightBody

  /-- Item replay evidence is likewise canonical. -/
  theorem ItemsReplays.unique
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate}
      {items : List PackItem} {start stop : Nat} {children : List CST}
      (left right : ItemsReplays profile plan input certificate
        items start stop children) : left = right := by
    cases left with
    | nil => cases right; rfl
    | terminal leftMatched leftRest =>
        cases right with
        | terminal rightMatched rightRest =>
            congr
            · exact terminalRecognition_unique leftMatched rightMatched
            · exact ItemsReplays.unique leftRest rightRest
    | nonterminal leftHead leftRest =>
        cases right with
        | nonterminal rightHead rightRest =>
            congr
            · exact Replays.unique leftHead rightHead
            · exact ItemsReplays.unique leftRest rightRest
end

instance Replays.instSubsingleton
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate}
    {resultSort : String} {start stop : Nat} {tree : CST} :
    Subsingleton (Replays profile plan input certificate
      resultSort start stop tree) where
  allEq := Replays.unique

instance ItemsReplays.instSubsingleton
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : ItemsCertificate}
    {items : List PackItem} {start stop : Nat} {children : List CST} :
    Subsingleton (ItemsReplays profile plan input certificate
      items start stop children) where
  allEq := ItemsReplays.unique

/-- A portable certificate is admitted only when exact replay is inhabited.
The replay proof is erased from the boundary; the finite certificate remains
the observable evidence object. -/
abbrev AdmittedCertificate
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (resultSort : String) (start stop : Nat)
    (tree : CST) : Type :=
  { certificate : Certificate //
    Nonempty (Replays profile plan input certificate
      resultSort start stop tree) }

/-- Every proof-relevant ParserPack fibre is exactly equivalent to its finite,
replayable certificate fibre.  This is the boundary that independent native
parsers may target. -/
noncomputable def derivationCertificateEquiv
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (resultSort : String) (start stop : Nat)
    (tree : CST) :
    ParserPackDerivesAt profile plan input resultSort start stop tree ≃
      AdmittedCertificate profile plan input resultSort start stop tree where
  toFun derivation :=
    ⟨Certificate.ofDerivation derivation,
      ⟨Replays.ofDerivation derivation⟩⟩
  invFun admitted :=
    (Classical.choice admitted.property).derivation
  left_inv derivation := by
    let chosen := Classical.choice
      (show Nonempty (Replays profile plan input
        (Certificate.ofDerivation derivation) resultSort start stop tree) from
        ⟨Replays.ofDerivation derivation⟩)
    have chosenEq : chosen = Replays.ofDerivation derivation :=
      Replays.unique _ _
    change chosen.derivation = derivation
    rw [chosenEq]
    exact Replays.derivation_ofDerivation derivation
  right_inv admitted := by
    apply Subtype.ext
    exact Replays.certificate_derivation
      (Classical.choice admitted.property)

/-- Whole-input certificate admission starts at the plan's authored start
sort and consumes the complete scalar input. -/
abbrev AdmittedRootCertificate
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (tree : CST) : Type :=
  AdmittedCertificate profile plan input plan.lexical.startSort
    0 input.length tree

/-- Exact whole-input ParserPack derivations and admitted portable root
certificates have equivalent fibres. -/
noncomputable def rootDerivationCertificateEquiv
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (tree : CST) :
    ParserPackRootDerives profile plan input tree ≃
      AdmittedRootCertificate profile plan input tree :=
  derivationCertificateEquiv profile plan input
    plan.lexical.startSort 0 input.length tree

/-! ## Occurrence controls -/

/-- The physical production position is recoverable from a lexical
certificate equality. -/
theorem lexical_position_injective
    {leftPosition rightPosition leftStart rightStart leftStop rightStop : Nat}
    {matcher : TerminalMatcher}
    (equal : Certificate.lexical leftPosition matcher leftStart leftStop =
      Certificate.lexical rightPosition matcher rightStart rightStop) :
    leftPosition = rightPosition := by
  cases equal
  rfl

/-- Equal structural payloads at two different physical rows cannot collapse
to one certificate. -/
theorem structural_positions_remain_distinct
    {leftPosition rightPosition start stop : Nat}
    {body : ItemsCertificate} (different : leftPosition ≠ rightPosition) :
    Certificate.structural leftPosition start stop body ≠
      Certificate.structural rightPosition start stop body := by
  intro equal
  exact different (by cases equal; rfl)

/-- Negative control: changing a terminal seam changes the certificate, so a
backend cannot silently repair a corrupted cursor transition during replay. -/
theorem terminal_stop_mutation_is_visible
    {matcher : TerminalMatcher} {start leftStop rightStop : Nat}
    {rest : ItemsCertificate}
    (different : leftStop ≠ rightStop) :
    ItemsCertificate.terminal matcher start leftStop rest ≠
      ItemsCertificate.terminal matcher start rightStop rest := by
  intro equal
  exact different (by cases equal; rfl)

end Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
