import Kaplansky.Final.Main
import Kaplansky.Main.CorLean
import Kaplansky.Main.TheoremB

/-! Independent audit (lead). The `example`s check that the proved theorems have exactly the
types of the trusted Challenge definitions; `#print axioms` checks the axiom footprint. -/

example : Kaplansky.MainTheorem := Kaplansky.Final.mainTheorem_proof
example : Kaplansky.MainTheoremConsequences := Kaplansky.Final.mainTheoremConsequences_proof
example : Kaplansky.HyperbolicZeroDivisors := Kaplansky.Main.hyperbolicZeroDivisors_proof

#print axioms Kaplansky.Final.mainTheorem_proof
#print axioms Kaplansky.Final.mainTheoremConsequences_proof
#print axioms Kaplansky.Main.hyperbolicZeroDivisors_proof
#print axioms Kaplansky.Main.theoremB
#print axioms Kaplansky.Random.Odd.exists_patternFree
#print axioms Kaplansky.Random.OAI197a.exists_patternFree
#print axioms Kaplansky.Exclusion.wordHyperbolic_of_patternFree

#print Kaplansky.MainTheorem
#print Kaplansky.GoodHyperbolic
