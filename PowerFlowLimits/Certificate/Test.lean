import PowerFlowLimits.Certificate.Wire

/-!
# Compile time vectors for the certificate kernel

Each `#guard` runs during elaboration, so building this module fails if a parser, the exact cut
bound, the acceptance verdict, or the disconnected model rejection changes.
-/

open PowerFlowLimits.Certificate

private def pathModelText : String :=
  "QPFMODEL 1 N 4 M 3 BRANCHES 0 1 1 0 1 2 1 0 2 3 1 0 END"

private def policyText : String :=
  "QPFPOLICY 1 ERROR 1 10 TOMO 1 1 GAP 1 1 HYBRID 1 1 CLASSICAL 1 1 LOG 1 1 END"

private def certificateText : String :=
  "QPFCERT 1 SIDE 4 1 1 0 0 END"

#guard parseModel pathModelText |>.isSome
#guard parsePolicy policyText |>.isSome
#guard parseCertificate certificateText |>.isSome

#guard
  match parseModel pathModelText, parsePolicy policyText, parseCertificate certificateText with
  | some model, some policy, some witness => cutLowerBound model witness = some (3 / 2) &&
      checkNoAdvantage model policy witness
  | _, _, _ => false

#guard
  match parseModel "QPFMODEL 1 N 3 M 1 BRANCHES 0 1 1 0 END" with
  | some model => !model.valid
  | none => false

#guard (parseCertificate "QPFCERT 1 SIDE 4 1 2 0 0 END").isNone
