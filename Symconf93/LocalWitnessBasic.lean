module
public import Symconf93.LocalWitnessBuckets
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Symconf93

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def validWitness31 (P : List (List Nat)) (w : LocalWitness31) : Bool :=
    match P[w.idx]? with
    | none => false
    | some T =>
      let S := translateReflect31 T w.neg w.shift
      decide (w.shift<31) && S.contains 0 && (supportCode31 S == w.code)

def coveredBucket31 (Ws : List LocalWitness31) (k u : Nat) : Bool :=
  let codes := Ws.map LocalWitness31.code
  (normalizedFirst31 k u).all (fun s => !(validLocal31 s) || codes.contains (supportCode31 s))

def chosenBucket31 (R : List (List LocalWitness31)) (u : Nat) : List LocalWitness31 :=
  R[u]?.getD []

theorem witnessBuckets2_valid : witnessBuckets2.all (fun row => row.all (validWitness31 proto2))=true := by decide +kernel
theorem witnessBuckets3_valid : witnessBuckets3.all (fun row => row.all (validWitness31 proto3))=true := by decide +kernel
theorem witnessBuckets5_valid : witnessBuckets5.all (fun row => row.all (validWitness31 proto5))=true := by decide +kernel

theorem witnessBuckets2_cover : ∀ u : Fin 31, 0<u.val →
    coveredBucket31 (chosenBucket31 witnessBuckets2 u.val) 2 u.val=true := by decide +kernel

theorem witnessBuckets3_cover : ∀ u : Fin 31, 0<u.val →
    coveredBucket31 (chosenBucket31 witnessBuckets3 u.val) 3 u.val=true := by decide +kernel


end Symconf93

#print axioms Symconf93.witnessBuckets2_cover
#print axioms Symconf93.witnessBuckets3_cover
#print axioms Symconf93.witnessBuckets5_valid
