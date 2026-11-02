import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocationControls
import Mettapedia.Logic.KernelFoundationManifest

/-! Owned-module foundation audit for typed scalar callback extraction. -/

#print axioms Mettapedia.Machines.TypedScalar.Expr.eval_agrees
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource.Elaborates.returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource.extracted_completed_iff
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody.Compiles.returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarDependencies.transport
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation.Prepared.call_completed_iff
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls.no_sort_blind_decoder
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls.source_never_completes_as_integer_one

#foundation_manifest_module Mettapedia.Machines.TypedScalar
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarDependencies
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls
#foundation_manifest_module Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocationControls
