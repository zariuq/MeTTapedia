(: PlainDemandPair (-> $t $t DemandRange))
(: plain-demand-result (-> DemandRange))
(= (plain-demand-result) (PlainDemandPair 1 2))

(: OtherDemandPair (-> $t $t DemandRange))
(: (OtherDemandPair 1 2) OtherDemandRange)
(: other-demand-result (-> DemandRange))
(= (other-demand-result) (OtherDemandPair 1 2))

(: AssertedDemandPair (-> $t $t DemandRange))
(: (AssertedDemandPair 1 2) DemandRange)
(: asserted-demand-result (-> DemandRange))
(= (asserted-demand-result) (AssertedDemandPair 1 2))

(: use-demand (-> DemandRange DemandRange))
(= (use-demand $value) $value)

!(use-demand (plain-demand-result))
!(use-demand (asserted-demand-result))
!(use-demand (other-demand-result))
