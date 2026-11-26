module
public import Symconf93.PhasePairsBase

@[expose] public section

/-! Four moments, in small literal modular integer arithmetic. -/
namespace Symconf93

structure PhaseM31 where
  n : Nat
  s : Nat
  q : Nat
  c : Nat
  d : Nat
deriving DecidableEq, Repr

def momentsRaw31 (S : List Nat) : PhaseM31 :=
  ⟨S.length, S.sum%31, (S.map (fun x=>x^2)).sum%31,
    (S.map (fun x=>x^3)).sum%31,(S.map (fun x=>x^4)).sum%31⟩

def momentSignChoices31 (A B : List Nat) : List PhaseM31 :=
  (signVariants31 A B).map momentsRaw31

structure PairM31 where
  X : List PhaseM31
  Y : List PhaseM31
  Z : List PhaseM31
deriving DecidableEq, Repr

def pairMoments31 (S : SixSupports31) : PairM31 :=
  ⟨momentSignChoices31 S.a0 S.b0,
   momentSignChoices31 S.a1 S.b1,
   momentSignChoices31 S.a2 S.b2⟩

def firstOffset31 (A B C : PhaseM31) : Nat :=
  (31-(28*(A.s+B.s+C.s))%31)%31

def secondLinear31 (A B C : PhaseM31) : Nat :=
  (2*B.s+28*C.s+firstOffset31 A B C)%31

def secondConstant31 (A B C : PhaseM31) : Nat :=
  let t := firstOffset31 A B C
  (A.q+B.q+C.q+2*t*C.s+10*t*t)%31

def discriminant31 (A B C : PhaseM31) : Nat :=
  let b := secondLinear31 A B C
  let d := secondConstant31 A B C
  (b*b+31-(88*d)%31)%31

def decodedSecond31 (A B C : PhaseM31) (root : Nat) : Nat :=
  (12*(root+31-secondLinear31 A B C))%31

def decodedThird31 (A B C : PhaseM31) (x : Nat) : Nat :=
  (firstOffset31 A B C+14*x)%31

def thirdShiftedM31 (M : PhaseM31) (x : Nat) : Nat :=
  (M.c+3*x*M.q+3*x*x*M.s+M.n*x*x*x)%31

def fourthShiftedM31 (M : PhaseM31) (x : Nat) : Nat :=
  (M.d+4*x*M.c+6*x*x*M.q+4*x*x*x*M.s+M.n*x*x*x*x)%31

end Symconf93
