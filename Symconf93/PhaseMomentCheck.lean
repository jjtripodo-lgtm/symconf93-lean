module
public import Symconf93.PhaseMomentData
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Exhaustive kernel replay over the small actual four-moment records.
Two roots per second-moment discriminant, not a search over all shifts. -/
namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def squareRoots31 (a : Nat) : List Nat := rootTable31[a]?.getD []

def phaseMomentVeto31 (A B C : PhaseM31) : Bool :=
  (squareRoots31 (discriminant31 A B C)).all (fun r =>
    let x := decodedSecond31 A B C r
    let y := decodedThird31 A B C x
    ((A.c+thirdShiftedM31 B x+thirdShiftedM31 C y)%31 != 0) ||
    ((A.d+fourthShiftedM31 B x+fourthShiftedM31 C y)%31 != 0))

def pairMomentVeto31 (B : PairM31) : Bool :=
  B.X.all (fun A => B.Y.all (fun C => B.Z.all (fun D => phaseMomentVeto31 A C D)))

theorem squareRoot31_lookup : ∀ a r : Fin 31,
    (squareRoots31 a.val).contains r.val = decide (r.val*r.val%31=a.val) := by decide +kernel

theorem roster_root_replay31 : (phaseMomentsData31.all pairMomentVeto31)=true := by decide +kernel

theorem roster_literal_moments31 : phaseMomentsData31 = phasePairs31.map pairMoments31 := by decide +kernel

end Symconf93

#print axioms Symconf93.squareRoot31_lookup
#print axioms Symconf93.roster_root_replay31
#print axioms Symconf93.roster_literal_moments31
