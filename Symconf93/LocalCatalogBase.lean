module
public import Symconf93.LocalCatalogData
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The finite proof only checks raw normalized representative-orbit
coverage. No reliance on Gaussian or untrusted proof instructions. -/
namespace Symconf93

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def unsignedGaps31 : List Nat → List Nat
  | [] => []
  | a::xs => (xs.map (fun b => min (b-a) (31-(b-a)))) ++ unsignedGaps31 xs

def validLocal31 (s : List Nat) : Bool :=
  let d := unsignedGaps31 s
  decide d.Nodup && d.all (fun u => decide (2≤u ∧ u≤15))

def supportCode31 (s : List Nat) : Nat := s.foldr (fun x acc => (1<<<x) ||| acc) 0

def translateReflect31 (s : List Nat) (neg : Bool) (t : Nat) : List Nat :=
  s.map (fun x => (t+(if neg then 31-x else x))%31)

def orbitNormalized31 (s : List Nat) : List (List Nat) :=
  [false,true].flatMap (fun b => (List.range 31).filterMap (fun t =>
    let z := translateReflect31 s b t
    if z.contains 0 then some z else none))

def localOrbitCodes31 (P : List (List Nat)) : List Nat :=
  (P.flatMap orbitNormalized31).map supportCode31

/-- Every possible normalized support with specified first nonzero entry
comes from this list. Duplicating zero in a hint cannot create coverage. -/
def normalizedFirst31 (k u : Nat) : List (List Nat) :=
  (((List.range' (u+1) (30-u)).sublistsLen (k-2)).map (fun t => 0::u::t))

def coverage31At (P : List (List Nat)) (k u : Nat) : Bool :=
  let codes := localOrbitCodes31 P
  (normalizedFirst31 k u).all (fun s => !(validLocal31 s) || codes.contains (supportCode31 s))

end Symconf93
