!(import! &self generic_inference_checker_v0)

!(assertEqual
  (gic-check-trace-pathmap (gic-presentation)
    (TraceCheckCons
      (GTraceCheck (gic-proves (gic-B)) (gic-proof-b-trace) True)
      (TraceCheckCons
        (GTraceCheck (gic-proves (gic-A))
          (GaCons (GRef 0) GaNil) False)
        TraceCheckNil)))
  True)

!(GICPathMapSummary 2 2 0)
