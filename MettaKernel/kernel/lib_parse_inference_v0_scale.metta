!(import! &self lib_parse_inference_v0)

!(println!
  (case
    (lib_parse:generate-presentation
      (Cons (VarD x Expr) Nil)
      "scale-source"
      (repeat-atom 4096 x))
    (((LPInferencePresentation $presentation) ScaleOK)
     ((LPInferenceError $reason) ScaleError)
     ($other ScaleOther))))

!(LPInferenceScaleSummary 4096 1 1 0)
