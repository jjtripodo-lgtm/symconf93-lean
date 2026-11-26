module
public import Symconf93.ActualMomentCover

@[expose] public section

/-! Every literal roster record is a correctly weighted physical block
pair, not an untyped moment multiset with assumed multiplicities. -/
namespace Symconf93

private theorem shape31 (B : SixSupports31) (hB : B∈phasePairs31) :
    B.a0.length=2 ∧ B.b0.length=3 ∧ B.a1.length=3 ∧ B.b1.length=5 ∧
    B.a2.length=5 ∧ B.b2.length=2 := by
  have h : phasePairs31.all (fun B => decide (B.a0.length=2 ∧ B.b0.length=3 ∧
    B.a1.length=3 ∧ B.b1.length=5 ∧ B.a2.length=5 ∧ B.b2.length=2))=true := by decide +kernel
  exact decide_eq_true_eq.mp (List.all_eq_true.mp h _ hB)

private theorem length_raw31 (A B : List Nat) :
    (rawDiff31 A B).length=A.length*B.length := by
  induction A with
  | nil => simp [rawDiff31]
  | cons a T ih =>
    change (B.map (fun b => (31+b-a)%31) ++ rawDiff31 T B).length =
      (T.length+1)*B.length
    rw [List.length_append,List.length_map,ih,Nat.add_mul,one_mul,Nat.add_comm]

private theorem reflect_len (S : List Nat) (b : Bool) :
    (supportReflect31 b S).length=S.length := by
  cases b <;> simp [supportReflect31]

private theorem variants_len {A B D : List Nat} (h : D∈signVariants31 A B) :
    D.length=A.length*B.length := by
  obtain ⟨a,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp h
  rw [length_raw31,reflect_len,reflect_len]

private theorem variants_bound {A B D : List Nat} (h : D∈signVariants31 A B) (x : Nat)
    (hx : x∈D) : x<31 := by
  obtain ⟨a,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp h
  obtain ⟨s,_,hy⟩ := List.mem_flatMap.mp hx
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
  exact Nat.mod_lt _ (by decide)

/-- All six endpoint reflections and arbitrary shifts are paid for every
literal roster row. The first relative shift is normalized to zero. -/
theorem no_literal_roster_phase_cover
    (B : SixSupports31) (hB : B∈phasePairs31)
    {D E T : List Nat} (hd : D∈signVariants31 B.a0 B.b0)
    (he : E∈signVariants31 B.a1 B.b1) (ht : T∈signVariants31 B.a2 B.b2)
    (x y : Nat) : isCover31 (D++shifted31 E x++shifted31 T y)=false := by
  obtain ⟨_,_,h1,h2,h3,h4⟩ := shape31 B hB
  apply literal_roster_phase_exclusion B hB D E T hd he ht (variants_bound hd)
  · rw [variants_len he,h1,h2]
  · rw [variants_len ht,h3,h4]

end Symconf93
#print axioms Symconf93.no_literal_roster_phase_cover
