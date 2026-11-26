module
public import Symconf59.CycleLayout
public import Symconf93.Incidence
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

namespace Symconf93
open Symconf59 SimpleGraph
open scoped BigOperators Matrix
open Matrix

def leaveGraph (M : Int93) (hdiag : ∀i,M i i=0) (hs : Mᵀ=M) : SimpleGraph Site where
  Adj i j := M i j=1
  symm := ⟨by
    intro i j h
    have he := congrArg (fun (B : Int93) => B i j) hs
    exact he.trans h⟩
  loopless := ⟨by
    intro i h
    change M i i=1 at h
    rw [hdiag] at h
    contradiction⟩

private theorem int_count_ones (f : Site → ℤ) (h : ∀ i, f i=0 ∨ f i=1) :
    (∑ i,f i)=((Finset.univ.filter (fun i=>f i=1)).card:ℤ) := by
  have h' (i : Site) : f i=(if f i=1 then 1 else 0 : ℤ) := by
    rcases h i with h | h <;> simp [h]
  calc
    _ = ∑ i, (if f i=1 then 1 else 0 : ℤ) := Finset.sum_congr rfl (fun i _ => h' i)
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem binary_leave_graph_two_regular (M : Int93)
    (hdiag : ∀i,M i i=0) (hs : Mᵀ=M) (hb : ∀i j,M i j=0 ∨ M i j=1)
    (hm : ∀i,(∑ j,M i j)=2) :
    ∀ i, ((leaveGraph M hdiag hs).neighborSet i).ncard=2 := by
  intro i
  let S := (leaveGraph M hdiag hs).neighborSet i
  have he : S.toFinite.toFinset=Finset.univ.filter (fun j => M i j=1) := by
    ext j
    simp [S,leaveGraph,SimpleGraph.mem_neighborSet]
  calc
    S.ncard = S.toFinite.toFinset.card := Set.ncard_eq_toFinset_card _ _
    _ = (Finset.univ.filter (fun j => M i j=1)).card := by rw [he]
    _ = 2 := by
      have h := int_count_ones (M i) (hb i)
      rw [hm] at h
      omega

theorem both_cycle_conditions (M : Int93)
    (hd : ∀i,M i i=0) (hs : Mᵀ=M) (hb : ∀ i j,M i j=0 ∨ M i j=1)
    (hR : ∀i,(∑j,M i j)=2) :
    (leaveGraph M hd hs).IsCycles ∧ ∀v, ((leaveGraph M hd hs).neighborSet v).Nonempty := by
  have hk := binary_leave_graph_two_regular M hd hs hb hR
  exact ⟨fun {_} _ => hk _,fun v => Set.nonempty_of_ncard_ne_zero (by rw [hk]; decide)⟩

/-- Actual one-by-one cyclic components of the original row leave, no
assumption on the number of components or the incidence automorphism. -/
noncomputable def originalRowLayout {A : Int93} (h : Incidence93 A) :
    CycleLayout (leaveGraph (rowLeave A) (rowLeave_diag h) (rowLeave_symm A)) := by
  have hc := both_cycle_conditions (rowLeave A) (rowLeave_diag h) (rowLeave_symm A)
    (rowLeave_binary h) (rowLeave_sum h)
  exact cycleLayout_of_two_regular _ hc.1 hc.2

end Symconf93
