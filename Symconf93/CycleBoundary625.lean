module
public import Symconf93.CycleTransfer625

@[expose] public section

namespace Symconf93.AffineCycle625
open Symconf59
open Matrix
open scoped BigOperators Matrix

private theorem next_wrap_b {n : ℕ} [NeZero n] (k : ℕ) :
    cnext (wrap n k)=wrap n (k+1) := by
  apply Fin.ext
  change ((k%n)+(1%n))%n=(k+1)%n
  exact (Nat.add_mod _ _ _).symm

private theorem prev_next_b {n : ℕ} [NeZero n] (i : Fin n) :
    cprev (cnext i)=i := by
  change (i+1)-1=i
  exact add_sub_cancel_right i 1

private theorem wrap_self_b (n : ℕ) [NeZero n] : wrap n n=wrap n 0 := by
  ext; simp [wrap]

private theorem wrap_val_b {n : ℕ} [NeZero n] (i : Fin n) :
    wrap n i.val=i := by
  ext; exact Nat.mod_eq_of_lt i.isLt

private theorem next_val_b {n : ℕ} [NeZero n] (i : Fin n) :
    cnext i=wrap n (i.val+1) :=
  (congrArg cnext (wrap_val_b i).symm).trans (next_wrap_b _)

/-- The quadratic form on a forward recurrence is a boundary term.
The input pair is (x_0,x_{-1}), the output pair is (x_l,x_{l−1}).
No cyclic condition or division is assumed. -/
theorem fromSeed_quad_boundary {R : Type*} [CommRing R] (k : ℕ) (u : R×R) :
    let x : Fin (k+2) → R := fromSeed u
    let v := run (k+2) u
    (∑ i, x i * (9*x i-x (cnext i)-x (cprev i))) =
      u.1*(u.2-v.2)+v.2*(v.1-u.1) := by
  let n := k+2
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  let x : Fin n → R := fromSeed u
  let v := run n u
  let a : Fin n := wrap n 0
  let b : Fin n := ⟨n-1,by have hn := NeZero.pos n; omega⟩
  change (∑ i, x i * (9*x i-x (cnext i)-x (cprev i))) = _
  have hn : 2≤n := by dsimp [n]; omega
  have ha : a.val=0 := by simp [a,wrap]
  have hb : b.val=n-1 := rfl
  have hab : a≠b := fun he => by
    have hh := congrArg Fin.val he
    rw [ha,hb] at hh
    omega
  have hx_a : x a=u.1 := fromSeed_zero u
  have hx_b : x b=v.2 := by
    change (run (n-1) u).1=(run n u).2
    conv_rhs => rw [← show n-1+1=n by omega]
    rfl
  have hnxt (i : Fin n) (hi : i.val+1<n) :
      x (cnext i)=(run (i.val+1) u).1 := by
    rw [next_val_b]
    change (run ((i.val+1)%n) u).1=_
    rw [Nat.mod_eq_of_lt hi]
  have hprv (i : Fin n) (hi : 0 < i.val) :
      x (cprev i)=(run i.val u).2 := by
    have h1 : i.val-1+1=i.val := by omega
    have hlt : i.val-1<n := by have h := i.isLt; omega
    have hp := prev_next_b (wrap n (i.val-1))
    rw [next_wrap_b,h1,wrap_val_b] at hp
    rw [hp]
    change (run ((i.val-1)%n) u).1=_
    rw [Nat.mod_eq_of_lt hlt]
    conv_rhs => rw [← h1]
    rfl
  let f (i : Fin n) := x i*(9*x i-x (cnext i)-x (cprev i))
  have hf_a : f a=u.1*(u.2-v.2) := by
    have ht : x (cprev a)=v.2 := by
      change fromSeed u (cprev (wrap n 0))=v.2
      rw [fromSeed_prev_zero]
      exact hx_b
    have hh : a.val+1<n := by rw [ha]; omega
    dsimp [f]
    rw [hnxt a hh,ha,ht,hx_a]
    simp only [run,step]
    ring
  have hf_b : f b=v.2*(v.1-u.1) := by
    have ht : cnext b=a := by
      rw [next_val_b,hb,show n-1+1=n by omega,wrap_self_b]
    have hh : 0 < b.val := by rw [hb]; omega
    have hv : 9*x b-(run b.val u).2=v.1 := by
      change 9*(run b.val u).1-(run b.val u).2=(run n u).1
      conv_rhs => rw [← show b.val+1=n by rw [hb]; omega]
      rfl
    dsimp [f]
    rw [ht,hx_a,hprv b hh]
    calc
      _ = x b*((9*x b-(run b.val u).2)-u.1) := by ring
      _ = _ := by rw [hv,hx_b]
  have hz (i : Fin n) (ha' : i≠a) (hb' : i≠b) : f i=0 := by
    have hi₀ : 0 < i.val := by
      by_contra hh
      exact ha' (Fin.ext (by rw [ha]; omega))
    have hi₁ : i.val+1<n := by
      by_contra hh
      have hl := i.isLt
      exact hb' (Fin.ext (by rw [hb]; omega))
    dsimp [f]
    rw [hnxt i hi₁,hprv i hi₀]
    simp only [x,fromSeed,run,step]
    ring
  calc
    (∑ i, f i) = ∑ i ∈ ({a,b}:Finset (Fin n)), f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hz i (by intro he; apply hi; simp [he]) (by intro he; apply hi; simp [he])
    _ = f a+f b := by simp [hab]
    _ = _ := by rw [hf_a,hf_b]

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.fromSeed_quad_boundary
