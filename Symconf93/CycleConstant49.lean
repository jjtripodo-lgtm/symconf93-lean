module
public import Symconf59.CycleLayout
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! A cyclic second difference in characteristic 7 with a nonzero
cycle length has exactly the constant kernel. -/
namespace Symconf93.AffineFiber49
open Symconf59
open scoped BigOperators

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem cprev_next49 {n : ℕ} (i : Fin n) : cprev (cnext i)=i := by
  haveI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  change (i+1)-1=i
  exact add_sub_cancel_right i 1

def cycleNext49 (n : Nat) : Equiv.Perm (Fin n) :=
  ⟨cnext,cprev,cprev_next49,cnext_prev⟩

theorem sum_cycleNext49 {n : Nat} {R : Type*} [AddCommMonoid R]
    (a : Fin n→R) : (∑ j,a (cnext j))=∑ j,a j :=
  Equiv.sum_comp (cycleNext49 n) a

theorem sum_cyclePrev49 {n : Nat} {R : Type*} [AddCommMonoid R]
    (a : Fin n→R) : (∑ j,a (cprev j))=∑ j,a j :=
  Equiv.sum_comp (cycleNext49 n).symm a

private theorem cnext_castSucc49 {n : Nat} (j : Fin n) :
    cnext j.castSucc=j.succ := by
  apply Fin.ext
  change (j.val+1%(n+1))%(n+1)=j.val+1
  have h := j.isLt
  rw [Nat.mod_eq_of_lt (show 1<n+1 by omega),Nat.mod_eq_of_lt (show j.val+1<n+1 by omega)]

theorem cyclic_prev_invariant49 {n : Nat} {R : Type*} [NeZero n]
    (f : Fin n→R) (h : ∀ i, f i=f (cprev i)) : ∀ i, f i=f 0 := by
  cases n with
  | zero => intro i; exact i.elim0
  | succ n =>
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      have he : cprev j.succ=j.castSucc := by
        rw [←cnext_castSucc49 j,cprev_next49]
      exact (h _).trans (he.symm ▸ ih)

/-- Every vector satisfying the cycle recurrence is constant if the
cycle length is invertible. No classification of general cycle spectra. -/
theorem nondivisible_cycle_steady49 {n : Nat} [NeZero n]
    (hn : (n:ZMod 7)≠0) (a : Fin n→ZMod 7) (s : ZMod 7)
    (h : ∀ i, 2*a i+s-a (cnext i)-a (cprev i)=0) :
    s=0 ∧ ∀ i,a i=a 0 := by
  have hS : (∑ i, (2*a i+s-a (cnext i)-a (cprev i)))=0 :=
    Finset.sum_eq_zero (fun i _=>h i)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    sum_cycleNext49,sum_cyclePrev49] at hS
  have hw : (n:ZMod 7)*s=0 := by linear_combination hS
  have hz : s=0 := (mul_eq_zero.mp hw).resolve_left hn
  let d (i : Fin n) := a (cnext i)-a i
  have hD i : d i=d (cprev i) := by
    dsimp only [d]
    rw [cnext_prev]
    have ht := h i
    rw [hz] at ht
    linear_combination -ht
  have hc : ∀ i,d i=d 0 := cyclic_prev_invariant49 d hD
  have hDsum : (∑ i,d i)=0 := by
    simp [d,Finset.sum_sub_distrib,sum_cycleNext49]
  simp only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hDsum
  have hDz : ∀ i, d i=0 := fun i=>(hc i).trans ((mul_eq_zero.mp hDsum).resolve_left hn)
  have ha i : a i=a (cprev i) := by
    have hh := hDz (cprev i)
    dsimp only [d] at hh
    rwa [cnext_prev,sub_eq_zero] at hh
  exact ⟨hz,cyclic_prev_invariant49 a ha⟩

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.nondivisible_cycle_steady49
