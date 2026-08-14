import PowerFlowLimits.Certificate.Wire

/-!
# Certificate checker entry point

`qpf-check <model.qpf> <policy.qpf> <certificate.qpf>` replays the exact cut bound and prints a
verdict. Exit code 0 is acceptance, 1 is `INCONCLUSIVE`, and 2 is malformed input, an unreadable
file, or wrong usage. Every rejection prints a reason line.
-/

open PowerFlowLimits.Certificate

private def usage : String := "usage: qpf-check <model.qpf> <policy.qpf> <certificate.qpf>"

private def inconclusive (reason : String) : IO UInt32 := do
  IO.println "verdict      INCONCLUSIVE"
  IO.println s!"reason       {reason}"
  return 1

private def runCheck (modelText policyText certificateText : String) : IO UInt32 := do
  match parseModel modelText, parsePolicy policyText, parseCertificate certificateText with
  | some model, some policy, some witness =>
      if !policy.valid then
        inconclusive "invalid policy constants"
      else
        match cutLowerBound model witness with
        | none => inconclusive "invalid model or cut witness"
        | some conditionLower =>
            IO.println s!"buses        {model.buses}"
            IO.println s!"branches     {model.branches.length}"
            IO.println s!"condition >= {conditionLower.num}/{conditionLower.den}"
            IO.println (s!"classical <= {(classicalCost model policy).num}/" ++
              s!"{(classicalCost model policy).den}")
            IO.println
              (s!"quantum >=   {(quantumCostLower model policy conditionLower).num}/" ++
                s!"{(quantumCostLower model policy conditionLower).den}")
            if checkNoAdvantage model policy witness then
              IO.println "verdict      NO"
              IO.println "scope        worst case balanced injection; full angle vector readout"
              return 0
            else
              inconclusive "inequality not established"
  | _, _, _ =>
      IO.eprintln "qpf-check: malformed model, policy, or certificate"
      return 2

private def unreadable (error : IO.Error) : IO UInt32 := do
  IO.eprintln s!"qpf-check: {error}"
  return 2

/-- Entry point of `qpf-check`. Exit code `0` reports an accepted no advantage certificate,
`1` reports an inconclusive check, and `2` reports unreadable or malformed input. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [modelPath, policyPath, certificatePath] =>
      try
        let modelText ← IO.FS.readFile modelPath
        let policyText ← IO.FS.readFile policyPath
        let certificateText ← IO.FS.readFile certificatePath
        runCheck modelText policyText certificateText
      catch error => unreadable error
  | _ => IO.eprintln usage; return (2 : UInt32)
