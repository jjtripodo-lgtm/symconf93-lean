module
public import Symconf93.PhasePairsBase
public import Symconf93.LocalCatalogBase

@[expose] public section

/-! The joint 35-pair roster is derived from the individual prototype
domains using both native rows and shared physical column disjointness. -/
namespace Symconf93

set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev GapRow31 := List Nat × List Nat × List Nat

def gapCode31 (s : List Nat) : Nat := supportCode31 (unsignedGaps31 s)
def allNative31 : Nat := supportCode31 (List.range' 2 14)

def rowMaskFits31 (A B C : Nat) : Bool :=
  (A &&& B)==0 && (A &&& C)==0 && (B &&& C)==0 && ((A ||| B) ||| C)==allNative31

def marked (L : List (List Nat)) : List (List Nat × Nat) := L.map (fun x => (x,gapCode31 x))

def family31_for_a (am : List Nat × Nat) : List GapRow31 :=
  (marked proto3).flatMap (fun bm =>
    if am.2 &&& bm.2 == 0 then
      ((marked proto5).filter (fun cm => rowMaskFits31 am.2 bm.2 cm.2)).map
        (fun cm => (am.1,bm.1,cm.1))
    else [])

def allFamilies31 : List GapRow31 := (marked proto2).flatMap family31_for_a

def pairCompatible31 (A B : GapRow31) : Bool :=
  gapCode31 A.1 &&& gapCode31 B.2.1 == 0 &&
  gapCode31 A.2.1 &&& gapCode31 B.2.2 == 0 &&
  gapCode31 A.2.2 &&& gapCode31 B.1 == 0

def packRows31 (A B : GapRow31) : List (List Nat) :=
  [A.1,B.2.1,A.2.1,B.2.2,A.2.2,B.1]

def projectedRoster31 : List (List (List Nat)) := phasePairs31.map (fun x =>
  [x.a0,x.b0,x.a1,x.b1,x.a2,x.b2])

def possibleRoster31 : List (List (List Nat)) :=
  allFamilies31.flatMap (fun A =>
    (allFamilies31.filter (pairCompatible31 A)).map (fun B => packRows31 A B))

theorem finite_roster_join31 : possibleRoster31.Perm projectedRoster31 := by decide +kernel

theorem known_prototypes_join_31 {a b c : List Nat}
    (ha : a∈proto2) (hb : b∈proto3) (hc : c∈proto5)
    (hp : rowMaskFits31 (gapCode31 a) (gapCode31 b) (gapCode31 c)=true) :
    (a,b,c)∈allFamilies31 := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,gapCode31 a), List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(b,gapCode31 b), List.mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
  have h0 : gapCode31 a &&& gapCode31 b == 0 := by
    unfold rowMaskFits31 at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.1.1.1
  simp only [h0,if_true]
  apply List.mem_map.mpr
  refine ⟨(c,gapCode31 c),List.mem_filter.mpr ⟨?_,hp⟩,rfl⟩
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

theorem fixed_families_give_roster31 {A B : GapRow31}
    (hA : A∈allFamilies31) (hB : B∈allFamilies31)
    (hc : pairCompatible31 A B=true) : packRows31 A B∈projectedRoster31 := by
  apply (finite_roster_join31.mem_iff).mp
  exact List.mem_flatMap.mpr ⟨A,hA,
    List.mem_map.mpr ⟨B,List.mem_filter.mpr ⟨hB,hc⟩,rfl⟩⟩

end Symconf93

#print axioms Symconf93.finite_roster_join31
#print axioms Symconf93.fixed_families_give_roster31
