module
public import Symconf93.Terminal93
public import Symconf93.InflatedTail93

@[expose] public section

/-! Structural completeness for the parity-free order-93 profile gate:
every Boolean row fit yields a literal weak-period row, and every profile
in the original general partition list satisfies the exact shape bounds. -/
namespace Symconf93

open scoped List

theorem partitionLists_sound93 {P : List Nat} {fuel rem hi : Nat}
    (h : P∈Symconf59.partitionLists fuel rem hi) :
    P.sum=rem ∧ P.Pairwise (·≥·) ∧ ∀ b∈P,3≤b ∧ b≤hi := by
  induction fuel generalizing P rem hi with
  | zero =>
    by_cases hz : rem=0
    · have hp : P=[] := by simpa [Symconf59.partitionLists,hz] using h
      subst P
      simp [hz]
    · simp [Symconf59.partitionLists,hz] at h
  | succ f ih =>
    by_cases hz : rem=0
    · have hp : P=[] := by simpa [Symconf59.partitionLists,hz] using h
      subst P
      simp [hz]
    · simp only [Symconf59.partitionLists,hz,if_false,List.mem_flatMap,List.mem_filter,
        List.mem_range,List.mem_map,decide_eq_true_eq] at h
      obtain ⟨b,⟨hb,h3⟩,Q,hQ,rfl⟩ := h
      have hB : b≤rem ∧ b≤hi := Nat.le_min.mp (Nat.lt_succ_iff.mp hb)
      obtain ⟨hs,hsort,hbound⟩ := ih hQ
      refine ⟨by simp only [List.sum_cons,hs]; omega,?_,?_⟩
      · exact List.pairwise_cons.mpr ⟨fun x hx=>(hbound x hx).2,hsort⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · exact ⟨h3,hB.2⟩
        · exact ⟨(hbound x hx).1,(hbound x hx).2.trans hB.2⟩

theorem rowSieve93_sound {a : Nat} {P : List Nat} {s q : Nat} {cap : Nat→Nat}
    (h : rowSieve93 a P s q cap=true) : RowWitness a P s q cap := by
  induction P generalizing s q cap with
  | nil =>
    have hp : s=0 ∧ q=0 := by simpa [rowSieve93,Bool.and_eq_true] using h
    obtain ⟨rfl,rfl⟩ := hp
    exact RowWitness.nil cap
  | cons b Q ih =>
    rw [rowSieve93,List.any_eq_true] at h
    obtain ⟨u,hu,hh⟩ := h
    let v := a*u/b
    have hS : u≤s ∧ u≤10 := Nat.le_min.mp (Nat.lt_succ_iff.mp (List.mem_range.mp hu))
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨⟨⟨hb,he,hv,hq⟩,hp⟩,ht⟩ := hh
    have hCap (d : Nat) (hd : 0<d) (hda : d<a) : expenditure a b u d≤cap d := by
      have hD := List.all_eq_true.mp hp d (List.mem_range.mpr hda)
      have hd' : d≠0 := by omega
      have hz : (d==0)=false := by simpa using hd'
      simpa [hz] using hD
    have H := RowWitness.cons b Q u v (s-u) (q-u*v) cap hb hS.2 hv he hCap (ih ht)
    have h1 : u+(s-u)=s := by omega
    have h2 : u*v+(q-u*v)=q := by
      change u*v≤q at hq
      omega
    simpa only [h1,h2] using H

theorem passing_profile_row_loose93 {P : List Nat} {a : Nat} (ha : a∈P)
    (ha0 : 0<a) (h : profileSieve93 P=true) : LooseRow93 a P 10 (a+7) := by
  have hh : P.all (fun b=>rowSieve93 b P 10 (b+7) (fun _=>1))=true := by
    unfold profileSieve93 at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  exact physical_row_to_loose ha0 (rowSieve93_sound (List.all_eq_true.mp hh a ha)) (fun _=>le_rfl)

theorem passing_profile_no_four93 {P : List Nat} (h : profileSieve93 P=true) : 4∉P := by
  unfold profileSieve93 at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact fun hm=>Bool.noConfusion (h.1.symm.trans (List.contains_iff_mem.mpr hm))

end Symconf93

#print axioms Symconf93.partitionLists_sound93
#print axioms Symconf93.rowSieve93_sound
