module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Enumerate actual component labels in decreasing length order, permitting ties. -/
namespace Symconf59

structure OrderedLengths {C : Type*} (len : C → ℕ) where
  values : List ℕ
  label : Fin values.length ≃ C
  size_eq : ∀ i, values.get i=len (label i)
  sorted : values.Pairwise (· ≥ ·)

/-- Sort the actual labels, then use the list positions as a literal
bijection. Ties in length are retained and do not merge labels. -/
noncomputable def order_actual_lengths {C : Type*} [Fintype C] (len : C → ℕ) :
    OrderedLengths len := by
  classical
  let e := Fintype.equivFin C
  let L := List.ofFn e.symm
  let T := L.mergeSort (fun x y => decide (len x≥len y))
  have hperm : T.Perm L := List.mergeSort_perm _ _
  have hg (c : C) : c∈T := hperm.mem_iff.mpr (List.mem_ofFn.mpr ⟨e c,e.symm_apply_apply c⟩)
  have hn : T.Nodup := hperm.nodup_iff.mpr (List.nodup_ofFn_ofInjective e.symm.injective)
  have hsurj : Function.Surjective T.get := fun c => List.get_of_mem (hg c)
  let F := Equiv.ofBijective T.get ⟨hn.injective_get,hsurj⟩
  let P := T.map len
  have hlen : P.length=T.length := List.length_map len
  let Q := (finCongr hlen).trans F
  have hsort : T.Pairwise (fun x y => len x≥len y) := by
    have h := List.pairwise_mergeSort (le := fun x y => decide (len x≥len y))
      (fun a b c ab bc => decide_eq_true_eq.mpr
        ((decide_eq_true_eq.mp bc).trans (decide_eq_true_eq.mp ab)))
      (fun a b => by simp [le_total (len b) (len a)]) L
    simpa only [T,decide_eq_true_eq] using h
  refine ⟨P,Q,?_ ,List.pairwise_map.mpr hsort⟩
  intro i
  change (T.map len)[i.val]=len (T[i.val]'(hlen ▸ i.isLt))
  exact List.getElem_map len

theorem sum_get_nat (P : List ℕ) : P.sum=∑ j,P.get j := by
  induction P with
  | nil => simp
  | cons a P ih =>
    change a+P.sum=∑j : Fin (P.length+1),(a::P).get j
    rw [Fin.sum_univ_succ,ih]
    rfl

theorem OrderedLengths.sum_values {C : Type*} [Fintype C] {len : C → ℕ}
    (O : OrderedLengths len) : O.values.sum=∑ c,len c := by
  rw [sum_get_nat]
  simp only [O.size_eq]
  exact Equiv.sum_comp O.label len

end Symconf59
