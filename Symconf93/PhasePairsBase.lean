module
public import Symconf93.PhasePairsData
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Exact first-moment guided cover veto for every shift and reflection of
the 35 literal prototype pairs. This stage is not the support coverage proof. -/
namespace Symconf93

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def supportReflect31 (neg : Bool) (S : List ℕ) : List ℕ :=
  if neg then S.map (fun s => (31-s)%31) else S

def rawDiff31 (A B : List ℕ) : List ℕ :=
  A.flatMap (fun a => B.map (fun b => (31+b-a)%31))

def shifted31 (D : List ℕ) (u : ℕ) : List ℕ := D.map (fun d => (d+u)%31)

def isCover31 (D : List ℕ) : Bool := (List.range 31).all (fun d => D.count d==1)

/-- First moment =0, with lengths 6,15,10, gives the only possible final
shift once the first shift is globally removed and the second is fixed. -/
def lastShift31 (D E F : List ℕ) (u : ℕ) : ℕ :=
  (31-(28*(D.sum+E.sum+F.sum+15*u))%31)%31

def rawTripleVeto31 (D E F : List ℕ) : Bool :=
  (List.range 31).all (fun u => !(isCover31 (D ++ shifted31 E u ++ shifted31 F (lastShift31 D E F u))))

def signVariants31 (A B : List ℕ) : List (List ℕ) :=
  [false,true].flatMap (fun sa => [false,true].map (fun sb =>
    rawDiff31 (supportReflect31 sa A) (supportReflect31 sb B)))

def supportsVeto31 (B : SixSupports31) : Bool :=
  (signVariants31 B.a0 B.b0).all (fun D =>
    (signVariants31 B.a1 B.b1).all (fun E =>
      (signVariants31 B.a2 B.b2).all (fun F => rawTripleVeto31 D E F)))

end Symconf93
