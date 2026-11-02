import Mettapedia.Logic.BDD.SymbolicCTLControls
import Mettapedia.Logic.BDD.RelationalImage
import Mettapedia.Machines.PrivateScalarFold
import Mettapedia.Logic.KernelFoundationManifest

/-! Owned-module audit for symbolic state regions and private fold attempts. -/

#print axioms Mettapedia.Logic.BDDCore.StatePredicates.equivalent_iff
#print axioms Mettapedia.Logic.BDDCore.StateTransducer.checkRule_iff
#print axioms Mettapedia.Logic.BDDCore.StateTransducer.pre_eval
#print axioms Mettapedia.Logic.BDDCore.RelationalImage.pushForward_eval
#print axioms Mettapedia.Logic.BDDCore.RelationalImage.image_must_adjunction
#print axioms Mettapedia.Logic.CTLFixedPoints.until_iff_lfp
#print axioms Mettapedia.Logic.CTLFixedPoints.globally_iff_gfp
#print axioms Mettapedia.Logic.BDDCore.FixedPointSolver.resume_split
#print axioms Mettapedia.Logic.BDDCore.FixedPointSolver.least_eventually_finishes
#print axioms Mettapedia.Logic.BDDCore.FixedPointSolver.greatest_eventually_finishes
#print axioms Mettapedia.Logic.BDDCore.SymbolicCTL.until_complete_iff_path
#print axioms Mettapedia.Logic.BDDCore.SymbolicCTL.globally_complete_iff_path
#print axioms Mettapedia.Logic.BDDCore.DecisionTable.table_exact
#print axioms Mettapedia.Logic.BDDCore.DecisionTable.successful_visits
#print axioms Mettapedia.Machines.PrivateScalarFold.completed_exact

#foundation_manifest_module Mettapedia.Algebra.Order.FixedPointIteration
#foundation_manifest_module Mettapedia.Logic.CTLFixedPoints
#foundation_manifest_module Mettapedia.Logic.BDD.StatePredicates
#foundation_manifest_module Mettapedia.Logic.BDD.StateTransducer
#foundation_manifest_module Mettapedia.Logic.BDD.RelationalImage
#foundation_manifest_module Mettapedia.Logic.BDD.FixedPointSolver
#foundation_manifest_module Mettapedia.Logic.BDD.SymbolicCTL
#foundation_manifest_module Mettapedia.Logic.BDD.DecisionTable
#foundation_manifest_module Mettapedia.Logic.BDD.SymbolicCTLControls
#foundation_manifest_module Mettapedia.Machines.PrivateScalarFold
