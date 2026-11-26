module
public import Symconf93.CycleFifteenScalar625

@[expose] public section

/-! A local finite convolution law propagates through actual products.
These lemmas work on any finite factors and any additive target group. -/
namespace Symconf93.AffineCycle625
open scoped BigOperators
set_option maxHeartbeats 6000000

def DiffAction {R α : Type*} [AddCommGroup R] [Fintype α]
    (δ : R) (Q : α→R) (c : ℤ) : Prop :=
  ∀ (f : R→ℤ) (t : R),
    (∑ x, (f (t-Q x)-f (t+δ-Q x))) = c*(f t-f (t+δ))

private theorem fiber_sum {α D : Type*} [Fintype α] [Fintype D]
    [DecidableEq D] (Q : α→D) (g : D→ℤ) :
    (∑ x, g (Q x)) =
     ∑ r, ((Finset.univ.filter fun x => Q x=r).card:ℤ)*g r := by
  classical
  rw [← Fintype.sum_fiberwise' Q g]
  apply Finset.sum_congr rfl
  intro r _
  simp [Fintype.card_subtype]

theorem diffAction_of_hist {R D α : Type*} [AddCommGroup R] [AddCommGroup D]
    [Fintype α] [Fintype D] [DecidableEq D]
    (δ : R) (σ : D) (L : D→R) (Q : α→D) (c : ℤ) (N : D→ℕ)
    (h0 : L 0=0) (hL : ∀ r, L (r+σ)=L r+δ)
    (hQ : ∀ r, (Finset.univ.filter fun x => Q x=r).card=N r)
    (hN : ∀ r, (N r:ℤ)-N (r+σ) =
      c*((if r=0 then (1:ℤ) else 0)-(if r+σ=0 then 1 else 0))) :
    DiffAction δ (fun x => L (Q x)) c := by
  intro f t
  change (∑ x, (f (t-L (Q x))-f (t+δ-L (Q x)))) = _
  rw [Finset.sum_sub_distrib,fiber_sum Q (fun r => f (t-L r)),
    fiber_sum Q (fun r => f (t+δ-L r))]
  simp_rw [hQ]
  have shift : (∑ r, (N r:ℤ)*f (t+δ-L r)) =
      ∑ r, (N (r+σ):ℤ)*f (t-L r) := by
    calc
      _ = ∑ r, (N (r+σ):ℤ)*f (t+δ-L (r+σ)) :=
        (Equiv.sum_comp (Equiv.addRight σ) (fun r => (N r:ℤ)*f (t+δ-L r))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hL]
        congr 2
        abel
  rw [shift,← Finset.sum_sub_distrib]
  simp_rw [← sub_mul,hN,mul_assoc,sub_mul,ite_mul,one_mul,zero_mul]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hn : L (-σ)=-δ := by
    have h := hL (-σ)
    rw [neg_add_cancel,h0] at h
    calc
      L (-σ) = (L (-σ)+δ)-δ := (add_sub_cancel_right _ _).symm
      _ = -δ := by rw [← h,zero_sub]
  have hz (r : D) : r+σ=0 ↔ r=-σ := by
    constructor
    · intro h
      rw [← add_sub_cancel_right r σ,h,zero_sub]
    · intro h
      rw [h,neg_add_cancel]
  simp_rw [hz]
  simp [h0,hn,sub_neg_eq_add]

theorem diffAction_transport {R A B : Type*} [AddCommGroup R] [Fintype A] [Fintype B]
    (δ : R) (Q : A→R) (W : B→R) (c : ℤ) (e : A≃B)
    (hE : ∀ x, Q x=W (e x)) (hW : DiffAction δ W c) :
    DiffAction δ Q c := by
  intro f t
  simp_rw [hE]
  exact (Equiv.sum_comp e (fun y : B => f (t-W y)-f (t+δ-W y))).trans (hW f t)

theorem diffAction_pi {R : Type*} [AddCommGroup R] (δ : R)
    {n : ℕ} (A : Fin n→Type*) [∀ i,Fintype (A i)]
    (Q : ∀ i, A i→R) (c : Fin n→ℤ)
    (h : ∀ i, DiffAction δ (Q i) (c i)) :
    DiffAction δ (fun x : ∀ i,A i => ∑ i, Q i (x i)) (∏ i,c i) := by
  classical
  induction n with
  | zero =>
    intro f t
    simp [Finset.sum_const]
  | succ n ih =>
    intro f t
    have htail := ih (fun i : Fin n => A i.succ)
      (fun i => Q i.succ) (fun i => c i.succ) (fun i => h i.succ)
    let C := ∀ i : Fin n,A i.succ
    let q (x : C) := ∑ i : Fin n,Q i.succ (x i)
    let e := Fin.consEquiv A
    rw [← Equiv.sum_comp e,Fintype.sum_prod_type_right]
    simp only [Fin.sum_univ_succ,Fin.prod_univ_succ]
    change (∑ x : C, ∑ y : A 0,
      (f (t-(Q 0 y+q x))-f (t+δ-(Q 0 y+q x)))) =
       c 0*(∏ i : Fin n,c i.succ)*(f t-f (t+δ))
    have middle (x : C) (y : A 0) :
        f (t-(Q 0 y+q x))-f (t+δ-(Q 0 y+q x)) =
        f ((t-q x)-Q 0 y)-f ((t-q x)+δ-Q 0 y) := by
      congr 2 <;> abel
    simp_rw [middle,h 0 f]
    rw [← Finset.mul_sum]
    have mid2 (x : C) : t-q x+δ=t+δ-q x := by abel
    simp_rw [mid2]
    rw [htail f t]
    ring

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.diffAction_of_hist
#print axioms Symconf93.AffineCycle625.diffAction_pi
