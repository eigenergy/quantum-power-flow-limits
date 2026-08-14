import PowerFlowLimits.Certificate.Core

/-!
# Versioned text format for computable certificates

All rationals are written as signed numerator and positive denominator tokens. The format is
deliberately small enough to parse without JSON or floating point arithmetic.
-/

namespace PowerFlowLimits.Certificate

private def digitsOf (chars : List Char) : Option Nat :=
  if chars.isEmpty || !chars.all Char.isDigit then none
  else some (chars.foldl (fun value char ↦ value * 10 + (char.toNat - '0'.toNat)) 0)

private def parseNat (token : List Char) : Option Nat := digitsOf token

private def parseInt (token : List Char) : Option Int := do
  match token with
  | '-' :: rest => pure (-(← digitsOf rest : Int))
  | '+' :: rest => pure (← digitsOf rest : Nat)
  | _ => pure (← digitsOf token : Nat)

private def parseRat (num den : List Char) : Option Rat := do
  let numerator ← parseInt num
  let denominator ← parseNat den
  if denominator = 0 then none else pure ((numerator : Rat) / (denominator : Rat))

/-- Binary64 dyadic exponents lie in `[-1074, 971]`; the bound rejects a document whose
exponent would force an enormous exact numeral without describing any binary64 weight. -/
private def maxDyadicExponent : Nat := 1100

private def parseDyadic (significand exponent : List Char) : Option Rat := do
  let sig ← parseNat significand
  let exp ← parseInt exponent
  if sig = 0 || maxDyadicExponent < exp.natAbs then none
  else if 0 ≤ exp then
    pure ((sig * 2 ^ exp.natAbs : Nat) : Rat)
  else
    pure ((sig : Rat) / ((2 ^ exp.natAbs : Nat) : Rat))

private def tokenizeAux : List Char → List Char → List (List Char) → List (List Char)
  | [], current, output =>
      (if current.isEmpty then output else current.reverse :: output).reverse
  | char :: rest, current, output =>
      if char.isWhitespace then
        tokenizeAux rest [] (if current.isEmpty then output else current.reverse :: output)
      else tokenizeAux rest (char :: current) output

def tokens (text : String) : List (List Char) := tokenizeAux text.toList [] []

private def parseBranches : Nat → List (List Char) → Option (List Branch × List (List Char))
  | 0, rest => some ([], rest)
  | count + 1, source :: target :: significand :: exponent :: rest => do
      let branch : Branch :=
        ⟨← parseNat source, ← parseNat target, ← parseDyadic significand exponent⟩
      let (branches, tail) ← parseBranches count rest
      pure (branch :: branches, tail)
  | _, _ => none

/-- `QPFMODEL 1 N <n> M <m> BRANCHES <u> <v> <significand> <exponent> ... END`,
where each exact branch weight is `significand * 2^exponent`. -/
def parseModel (text : String) : Option Model := do
  match tokens text with
  | magic :: version :: nTag :: nToken :: mTag :: mToken :: branchesTag :: rest =>
      if String.ofList magic != "QPFMODEL" || String.ofList version != "1" ||
          String.ofList nTag != "N" || String.ofList mTag != "M" ||
          String.ofList branchesTag != "BRANCHES" then none
      else
        let n ← parseNat nToken
        let m ← parseNat mToken
        let (branches, tail) ← parseBranches m rest
        if tail.map String.ofList = ["END"] then pure ⟨n, branches⟩ else none
  | _ => none

/-- `QPFPOLICY 1 ERROR n d TOMO n d GAP n d HYBRID n d CLASSICAL n d LOG n d END`. -/
def parsePolicy (text : String) : Option Policy := do
  match tokens text with
  | [magic, version, errorTag, en, ed, tomoTag, tn, td, gapTag, gn, gd,
      hybridTag, hn, hd, classicalTag, cn, cd, logTag, ln, ld, endTag] =>
      if String.ofList magic != "QPFPOLICY" || String.ofList version != "1" ||
          String.ofList errorTag != "ERROR" || String.ofList tomoTag != "TOMO" ||
          String.ofList gapTag != "GAP" || String.ofList hybridTag != "HYBRID" ||
          String.ofList classicalTag != "CLASSICAL" || String.ofList logTag != "LOG" ||
          String.ofList endTag != "END" then none
      else pure ⟨← parseRat en ed, ← parseRat tn td, ← parseRat gn gd,
        ← parseRat hn hd, ← parseRat cn cd, ← parseRat ln ld⟩
  | _ => none

private def parseSides : Nat → List (List Char) → Option (List Bool × List (List Char))
  | 0, rest => some ([], rest)
  | count + 1, value :: rest => do
      let inside ←
        match String.ofList value with | "0" => some false | "1" => some true | _ => none
      let (sides, tail) ← parseSides count rest
      pure (inside :: sides, tail)
  | _, _ => none

/-- `QPFCERT 1 SIDE <n> <0|1>... END`. -/
def parseCertificate (text : String) : Option CutWitness := do
  match tokens text with
  | magic :: version :: sideTag :: countToken :: rest =>
      if String.ofList magic != "QPFCERT" || String.ofList version != "1" ||
          String.ofList sideTag != "SIDE" then none
      else
        let count ← parseNat countToken
        let (side, tail) ← parseSides count rest
        if tail.map String.ofList = ["END"] then pure ⟨side⟩ else none
  | _ => none

end PowerFlowLimits.Certificate
