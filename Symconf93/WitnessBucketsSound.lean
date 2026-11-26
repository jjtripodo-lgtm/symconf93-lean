module
public import Symconf93.LocalWitnessBasic

@[expose] public section

/-! Check the supplied orbit hints instead of trusting an indexed value.
Bucketed witnesses only accelerate the finite evaluation. -/
namespace Symconf93

private theorem checked_witness_appearance {P : List (List Nat)}
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

theorem bucket_decision_gives_coverage {P : List (List Nat)} {B : List LocalWitness31}
    {k u : Nat} (hV : B.all (validWitness31 P)=true) (hC : coveredBucket31 B k u=true) :
    coverage31At P k u=true := by
  apply List.all_eq_true.mpr
  intro S hs
  have hh := List.all_eq_true.mp hC S hs
  by_cases hv : validLocal31 S=true
  · simp only [hv,Bool.not_true,Bool.false_or] at hh ⊢
    obtain ⟨W,hW,hEq⟩ := List.mem_map.mp (List.contains_iff_mem.mp hh)
    have hp := checked_witness_appearance (List.all_eq_true.mp hV W hW)
    exact List.contains_iff_mem.mpr (hEq ▸ hp)
  · have h0 : validLocal31 S=false := Bool.eq_false_of_not_eq_true hv
    simp [h0]

private theorem chosen_witness_safe {P : List (List Nat)} {T : List (List LocalWitness31)}
    (h : T.all (fun row => row.all (validWitness31 P))=true) (u : Nat) :
    (chosenBucket31 T u).all (validWitness31 P)=true := by
  unfold chosenBucket31
  cases hg : T[u]? with
  | none => rfl
  | some B => exact List.all_eq_true.mp h B (List.mem_of_getElem? hg)

theorem local2_coverage_verified : ∀ u : Fin 31, 0<u.val →
    coverage31At proto2 2 u.val=true :=
  fun u hu=>bucket_decision_gives_coverage
    (chosen_witness_safe witnessBuckets2_valid u.val) (witnessBuckets2_cover u hu)

theorem local3_coverage_verified : ∀ u : Fin 31, 0<u.val →
    coverage31At proto3 3 u.val=true :=
  fun u hu=>bucket_decision_gives_coverage
    (chosen_witness_safe witnessBuckets3_valid u.val) (witnessBuckets3_cover u hu)

theorem local5_coverage_verified_of_cells
    (hC : ∀ u : Fin 31, 0<u.val →
      coveredBucket31 (chosenBucket31 witnessBuckets5 u.val) 5 u.val=true) :
    ∀ u : Fin 31, 0<u.val →
    coverage31At proto5 5 u.val=true :=
  fun u hu=>bucket_decision_gives_coverage
    (chosen_witness_safe witnessBuckets5_valid u.val) (hC u hu)

end Symconf93

#print axioms Symconf93.local5_coverage_verified_of_cells
