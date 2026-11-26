module
public import Symconf93.WitnessBucketsSound
public import Symconf93.LocalCatalogSound
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-! Split the literal degree-five coverage by both smallest positive
sites. Witnesses must independently check their actual sign/translation;
the split serves only to control kernel evaluation cost. -/
namespace Symconf93

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def normalizedFirstTwo31 (u v : Nat) : List (List Nat) :=
  (((List.range' (v+1) (30-v)).sublistsLen 2).map (fun t=>0::u::v::t))

def doubleCoverage31 (W : List LocalWitness31) (u v : Nat) : Bool :=
  let codes := W.map LocalWitness31.code
  (normalizedFirstTwo31 u v).all (fun s =>
    let d := unsignedGaps31 s
    !(d.all (fun w=>decide (2≤w ∧ w≤15)) && decide d.Nodup) || codes.contains (supportCode31 s))

private theorem checked_double_witness {P : List (List Nat)}
    {w : LocalWitness31} (h : validWitness31 P w=true) :
    w.code∈localOrbitCodes31 P := by
  cases hp : P[w.idx]? with
  | none => simp [validWitness31,hp] at h
  | some T =>
    have hc : w.shift<31 ∧ 0∈translateReflect31 T w.neg w.shift ∧
        supportCode31 (translateReflect31 T w.neg w.shift)=w.code := by
      simp [validWitness31,hp,Bool.and_eq_true] at h
      exact ⟨h.1.1,h.1.2,h.2⟩
    apply List.mem_map.mpr
    refine ⟨translateReflect31 T w.neg w.shift,?_ ,hc.2.2⟩
    apply List.mem_flatMap.mpr
    refine ⟨T,List.mem_of_getElem? hp,?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨w.neg,(by cases w.neg <;> simp),?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨w.shift,List.mem_range.mpr hc.1,?_⟩
    simp [hc.2.1]

def CellCovers31 (u v : Nat) : Prop :=
  ∀ S∈normalizedFirstTwo31 u v, validLocal31 S=true →
    (localOrbitCodes31 proto5).contains (supportCode31 S)=true

theorem double_coverage_sound31 {W : List LocalWitness31} {u v : Nat}
    (hW : W.all (validWitness31 proto5)=true)
    (hC : doubleCoverage31 W u v=true) : CellCovers31 u v := by
  intro S hs hv
  have hh := List.all_eq_true.mp hC S hs
  have hl : ((unsignedGaps31 S).all (fun w=>decide (2≤w ∧ w≤15)) &&
      decide (unsignedGaps31 S).Nodup)=true := by
    rw [Bool.and_comm]
    exact hv
  simp only [hl,Bool.not_true,Bool.false_or] at hh
  obtain ⟨w,hw,hEq⟩ := List.mem_map.mp (List.contains_iff_mem.mp hh)
  have hp := checked_double_witness (List.all_eq_true.mp hW w hw)
  exact List.contains_iff_mem.mpr (hEq ▸ hp)

private theorem split_normalized31 {u : Fin 31} {S : List Nat}
    (hS : S∈normalizedFirst31 5 u.val) :
    ∃ v : Fin 31, u.val<v.val ∧ S∈normalizedFirstTwo31 u.val v.val := by
  obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hS
  obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hR
  cases R with
  | nil => simp at hlen
  | cons v T =>
    have hTlen : T.length=2 := by simp only [List.length_cons] at hlen; omega
    have hRange (x : Nat) (hx : x∈v::T) : u.val<x ∧ x<31 := by
      have hh := hsub.subset hx
      rw [List.mem_range'_1] at hh
      have hu := u.isLt
      omega
    have hv := hRange v (by simp)
    have hsort : (v::T).Pairwise (·<·) :=
      (List.sortedLT_range' (u.val+1) (30-u.val) (by decide : (1:Nat)≠0)).pairwise.sublist hsub
    refine ⟨⟨v,hv.2⟩,hv.1,List.mem_map.mpr ⟨T,List.mem_sublistsLen.mpr ⟨?_,hTlen⟩,rfl⟩⟩
    apply List.sublist_of_subperm_of_sortedLE
    · apply List.subperm_of_subset ((List.pairwise_cons.mp hsort).2.imp (fun h=>ne_of_lt h))
      intro x hx
      have h1 := (List.pairwise_cons.mp hsort).1 x hx
      have h2 := (hRange x (List.mem_cons_of_mem _ hx)).2
      rw [List.mem_range'_1]
      change v+1≤x ∧ x<v+1+(30-v)
      omega
    · exact ((List.pairwise_cons.mp hsort).2.imp (fun h=>le_of_lt h)).sortedLE
    · exact List.sortedLE_range' _ _ _

theorem local5_coverage_of_double_cells31
    (h : ∀ u v : Fin 31, 0<u.val → u.val<v.val → CellCovers31 u.val v.val) :
    ∀ u : Fin 31, 0<u.val → coverage31At proto5 5 u.val=true := by
  intro u hu
  apply List.all_eq_true.mpr
  intro S hS
  obtain ⟨v,hv,hD⟩ := split_normalized31 hS
  cases he : validLocal31 S
  · rfl
  · simp only [Bool.not_true,Bool.false_or]
    exact h u v hu hv S hD he

end Symconf93

#print axioms Symconf93.double_coverage_sound31
#print axioms Symconf93.local5_coverage_of_double_cells31
