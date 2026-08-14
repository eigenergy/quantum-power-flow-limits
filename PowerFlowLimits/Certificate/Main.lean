import PowerFlowLimits.Certificate.Wire

open PowerFlowLimits.Certificate

private def usage : String := "usage: qpf-check <model.qpf> <policy.qpf> <certificate.qpf>"

def main (args : List String) : IO UInt32 := do
  match args with
  | [modelPath, policyPath, certificatePath] =>
      let modelText ← IO.FS.readFile modelPath
      let policyText ← IO.FS.readFile policyPath
      let certificateText ← IO.FS.readFile certificatePath
      match parseModel modelText, parsePolicy policyText, parseCertificate certificateText with
      | some model, some policy, some witness =>
          match cutLowerBound model witness with
          | none =>
              IO.println "verdict      INCONCLUSIVE"
              IO.println "reason       invalid model or cut witness"
              return 1
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
                IO.println "verdict      INCONCLUSIVE"
                return 1
      | _, _, _ =>
          IO.eprintln "qpf-check: malformed model, policy, or certificate"
          return 2
  | _ => IO.eprintln usage; return 2
