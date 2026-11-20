import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleInstances

/-! # Actual closed rewrites of the finite context traversal equations -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextRewrites

open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

variable {all : List (ProgramBinders.Equation MSig [] ())}

theorem binary_seek_left (tag leftFrame rightFrame : String)
    (included : ∀ rule ∈ ContextRules.binary tag leftFrame rightFrame, rule ∈ all)
    (left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC tag [left, right]) context continuation)
      (seekC left (nodeC leftFrame [right, context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 4) "hd-seek" [node tag [slot 0, slot 1], slot 2, slot 3])
    (ContextRules.active "hd-seek" [slot 0, node leftFrame [slot 1, slot 2], slot 3])
    (included _ (by simp [ContextRules.binary])) ![left, right, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem binary_seek_right (tag leftFrame rightFrame : String)
    (included : ∀ rule ∈ ContextRules.binary tag leftFrame rightFrame, rule ∈ all)
    (left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC tag [left, right]) context continuation)
      (seekC right (nodeC rightFrame [left, context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 4) "hd-seek" [node tag [slot 0, slot 1], slot 2, slot 3])
    (ContextRules.active "hd-seek" [slot 1, node rightFrame [slot 0, slot 2], slot 3])
    (included _ (by simp [ContextRules.binary])) ![left, right, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem binary_plug_left (tag leftFrame rightFrame : String)
    (included : ∀ rule ∈ ContextRules.binary tag leftFrame rightFrame, rule ∈ all)
    (left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC left (nodeC leftFrame [right, context]) continuation)
      (plugC (nodeC tag [left, right]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 4) "hd-plug" [slot 0, node leftFrame [slot 1, slot 2], slot 3])
    (ContextRules.active "hd-plug" [node tag [slot 0, slot 1], slot 2, slot 3])
    (included _ (by simp [ContextRules.binary])) ![left, right, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step

theorem binary_plug_right (tag leftFrame rightFrame : String)
    (included : ∀ rule ∈ ContextRules.binary tag leftFrame rightFrame, rule ∈ all)
    (left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC right (nodeC rightFrame [left, context]) continuation)
      (plugC (nodeC tag [left, right]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 4) "hd-plug" [slot 0, node rightFrame [slot 1, slot 2], slot 3])
    (ContextRules.active "hd-plug" [node tag [slot 1, slot 0], slot 2, slot 3])
    (included _ (by simp [ContextRules.binary])) ![right, left, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step

theorem unary_seek (tag frame : String)
    (included : ∀ rule ∈ ContextRules.unary tag frame, rule ∈ all)
    (term context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC tag [term]) context continuation)
      (seekC term (nodeC frame [context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-seek" [node tag [slot 0], slot 1, slot 2])
    (ContextRules.active "hd-seek" [slot 0, node frame [slot 1], slot 2])
    (included _ (by simp [ContextRules.unary])) ![term, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem unary_plug (tag frame : String)
    (included : ∀ rule ∈ ContextRules.unary tag frame, rule ∈ all)
    (term context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC term (nodeC frame [context]) continuation)
      (plugC (nodeC tag [term]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-plug" [slot 0, node frame [slot 1], slot 2])
    (ContextRules.active "hd-plug" [node tag [slot 0], slot 1, slot 2])
    (included _ (by simp [ContextRules.unary])) ![term, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step

theorem identity_seek_type
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
      (seekC carrier (nodeC "hd-context-id-type" [left, right, context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (ContextRules.active "hd-seek" [slot 0, node "hd-context-id-type" [slot 1, slot 2, slot 3], slot 4])
    (included _ (by simp [ContextRules.identity])) ![carrier, left, right, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem identity_plug_type
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC carrier (nodeC "hd-context-id-type" [left, right, context]) continuation)
      (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-plug" [slot 0, node "hd-context-id-type" [slot 1, slot 2, slot 3], slot 4])
    (ContextRules.active "hd-plug" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (included _ (by simp [ContextRules.identity])) ![carrier, left, right, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step

theorem identity_seek_left
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
      (seekC left (nodeC "hd-context-id-left" [carrier, right, context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (ContextRules.active "hd-seek" [slot 1, node "hd-context-id-left" [slot 0, slot 2, slot 3], slot 4])
    (included _ (by simp [ContextRules.identity])) ![carrier, left, right, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem identity_plug_left
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC left (nodeC "hd-context-id-left" [carrier, right, context]) continuation)
      (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-plug" [slot 0, node "hd-context-id-left" [slot 1, slot 2, slot 3], slot 4])
    (ContextRules.active "hd-plug" [node "prime-tm-id" [slot 1, slot 0, slot 2], slot 3, slot 4])
    (included _ (by simp [ContextRules.identity])) ![left, carrier, right, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step

theorem identity_seek_right
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
      (seekC right (nodeC "hd-context-id-right" [carrier, left, context]) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-seek" [node "prime-tm-id" [slot 0, slot 1, slot 2], slot 3, slot 4])
    (ContextRules.active "hd-seek" [slot 2, node "hd-context-id-right" [slot 0, slot 1, slot 3], slot 4])
    (included _ (by simp [ContextRules.identity])) ![carrier, left, right, context, continuation]
  simpa [seekC, activeC, ContextRules.active] using step

theorem identity_plug_right
    (included : ∀ rule ∈ ContextRules.identity, rule ∈ all)
    (carrier left right context continuation : MClosed) :
    ProgramBinders.Rewrites all.get
      (plugC right (nodeC "hd-context-id-right" [carrier, left, context]) continuation)
      (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 5) "hd-plug" [slot 0, node "hd-context-id-right" [slot 1, slot 2, slot 3], slot 4])
    (ContextRules.active "hd-plug" [node "prime-tm-id" [slot 1, slot 2, slot 0], slot 3, slot 4])
    (included _ (by simp [ContextRules.identity])) ![right, carrier, left, context, continuation]
  simpa [plugC, activeC, ContextRules.active] using step


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextRewrites
