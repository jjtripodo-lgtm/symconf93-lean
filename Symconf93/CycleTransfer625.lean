module
public import Symconf93.EvenReduction93
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Small two-coordinate transfer across one literal cycle, independently
of any Gram diagonalization, finite contrast or pivot checker. -/
namespace Symconf93.AffineCycle625
open Symconf59
open Matrix
open scoped BigOperators Matrix

def step {R : Type*} [Ring R] (u : R×R) : R×R :=
  (9*u.1-u.2,u.1)

def run {R : Type*} [Ring R] : ℕ → (R×R) → R×R
  | 0,u => u
  | k+1,u => step (run k u)

theorem run_add {R : Type*} [Ring R] (k l : ℕ) (u : R×R) :
    run (k+l) u=run l (run k u) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [Nat.add_succ]
    change step (run (k+l) u)=step (run l (run k u))
    rw [ih]

def act {R : Type*} [Ring R] (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R) : R×R :=
  ((M.1.1 : R)*u.1+(M.2.1 : R)*u.2,
   (M.1.2 : R)*u.1+(M.2.2 : R)*u.2)

def cols (k : ℕ) : (ℤ×ℤ)×(ℤ×ℤ) :=
  (run k ((1:ℤ),0),run k ((0:ℤ),1))

theorem run_eq_act {R : Type*} [CommRing R] (k : ℕ) (u : R×R) :
    run k u=act (cols k) u := by
  induction k with
  | zero => simp [run,act,cols]
  | succ k ih =>
    change step (run k u) = act (step (run k ((1:ℤ),0)), step (run k ((0:ℤ),1))) u
    rw [ih]
    unfold act step cols
    push_cast
    exact Prod.ext (by ring) (by ring)

def rowEq {R : Type*} [Ring R] {n : ℕ} (x : Fin n→R) : Prop :=
  ∀ i, 9*x i-x (cnext i)-x (cprev i)=0

theorem cycleH_action {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n→R) (i : Fin n) :
    (((cycleH93 n).map (Int.castRingHom R)) *ᵥ x) i =
      9*x i-x (cnext i)-x (cprev i) := by
  change (∑ j, ((cycleH93 n i j:ℤ):R)*x j)=_
  have h (j : Fin n) :
      ((cycleH93 n i j:ℤ):R)*x j =
        (if j=i then 9*x j else 0)-(if j=cnext i then x j else 0)-
          (if j=cprev i then x j else 0) := by
    simp only [cycleH93,apply_ite,Int.cast_sub,Int.cast_one,Int.cast_zero,
      eq_comm (a:=i)]
    split_ifs <;> ring
  simp_rw [h,Finset.sum_sub_distrib]
  simp

def wrap (n : ℕ) [NeZero n] (k : ℕ) : Fin n :=
  ⟨k%n,Nat.mod_lt _ (NeZero.pos _)⟩

private theorem next_wrap {n : ℕ} [NeZero n] (k : ℕ) :
    cnext (wrap n k)=wrap n (k+1) := by
  apply Fin.ext
  change ((k%n)+(1%n))%n=(k+1)%n
  exact (Nat.add_mod _ _ _).symm

private theorem prev_next {n : ℕ} [NeZero n] (i : Fin n) :
    cprev (cnext i)=i := by
  change (i+1)-1=i
  exact add_sub_cancel_right i 1

private theorem wrap_self (n : ℕ) [NeZero n] :
    wrap n n=wrap n 0 := by
  ext
  simp [wrap]

def seed {R : Type*} {n : ℕ} [NeZero n] (x : Fin n→R) : R×R :=
  (x (wrap n 0),x (cprev (wrap n 0)))

theorem run_seed {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (x : Fin n→R) (h : rowEq x) (k : ℕ) :
    run k (seed x) = (x (wrap n k),x (cprev (wrap n k))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change step (run k (seed x))=_
    rw [ih,← next_wrap,prev_next]
    apply Prod.ext
    · change 9*x (wrap n k)-x (cprev (wrap n k))=x (cnext (wrap n k))
      linear_combination h (wrap n k)
    · rfl

theorem seed_fixed {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (x : Fin n→R) (h : rowEq x) : run n (seed x) = seed x := by
  rw [run_seed x h,wrap_self]
  rfl

theorem seed_recovers {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (x : Fin n→R) (h : rowEq x) (j : Fin n) : (run j.val (seed x)).1=x j := by
  rw [run_seed x h]
  suffices wrap n j.val=j by rw [this]
  ext
  exact Nat.mod_eq_of_lt j.isLt

private theorem wrap_val {n : ℕ} [NeZero n] (i : Fin n) :
    wrap n i.val=i := by
  ext
  exact Nat.mod_eq_of_lt i.isLt

private theorem next_val {n : ℕ} [NeZero n] (i : Fin n) :
    cnext i=wrap n (i.val+1) :=
  (congrArg cnext (wrap_val i).symm).trans (next_wrap _)

private theorem prev_zero {n : ℕ} [NeZero n] :
    cprev (wrap n 0)=wrap n (n-1) := by
  have h := prev_next (wrap n (n-1))
  rw [next_wrap,show n-1+1=n by have hn := NeZero.pos n; omega,wrap_self] at h
  exact h

def fromSeed {R : Type*} [Ring R] {n : ℕ} (u : R×R) (i : Fin n) : R :=
  (run i.val u).1

theorem fromSeed_zero {R : Type*} [Ring R] {n : ℕ} [NeZero n] (u : R×R) :
    fromSeed u (wrap n 0)=u.1 := by
  simp [fromSeed,wrap,run]

theorem fromSeed_prev_zero {R : Type*} [Ring R] {n : ℕ} [NeZero n] (u : R×R) :
    fromSeed u (cprev (wrap n 0))=(run (n-1) u).1 := by
  have hlt : n-1<n := by have hn := NeZero.pos n; omega
  rw [prev_zero]
  change (run ((n-1)%n) u).1=(run (n-1) u).1
  rw [Nat.mod_eq_of_lt hlt]

private theorem fromSeed_row_next {R : Type*} [Ring R] {n : ℕ} [NeZero n]
    (u : R×R) (hu : run n u=u) (i : Fin n) :
    fromSeed u (cnext i)=(run (i.val+1) u).1 := by
  rw [next_val]
  change (run ((i.val+1)%n) u).1=(run (i.val+1) u).1
  by_cases h : i.val+1=n
  · rw [h,Nat.mod_self,hu]; rfl
  · rw [Nat.mod_eq_of_lt (by have hi := i.isLt; omega)]

private theorem fromSeed_row_prev {R : Type*} [Ring R] {n : ℕ} [NeZero n]
    (u : R×R) (hu : run n u=u) (i : Fin n) :
    fromSeed u (cprev i)=(run i.val u).2 := by
  by_cases h : i.val=0
  · have hi : i=wrap n 0 := by ext; simpa [wrap] using h
    rw [hi,fromSeed_prev_zero]
    have hh := congrArg Prod.snd hu
    rw [← show n-1+1=n by have hn := NeZero.pos n; omega] at hh
    change (run (n-1) u).1=u.2 at hh
    exact hh
  · have h1 : i.val-1+1=i.val := by omega
    have hlt : i.val-1<n := by have hi := i.isLt; omega
    have hp := prev_next (wrap n (i.val-1))
    rw [next_wrap,h1,wrap_val] at hp
    rw [hp]
    change (run ((i.val-1)%n) u).1=(run i.val u).2
    rw [Nat.mod_eq_of_lt hlt]
    conv_rhs => rw [← h1]
    rfl

theorem fromSeed_rowEq {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (u : R×R) (hu : run n u=u) : rowEq (fromSeed u : Fin n→R) := by
  intro i
  rw [fromSeed_row_next u hu i,fromSeed_row_prev u hu i]
  simp only [fromSeed,run,step]
  ring

theorem seed_fromSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (u : R×R) (hu : run n u=u) : seed (fromSeed u : Fin n→R)=u := by
  apply Prod.ext
  · exact fromSeed_zero u
  · change fromSeed u (cprev (wrap n 0))=u.2
    rw [fromSeed_prev_zero]
    have hh := congrArg Prod.snd hu
    rw [← show n-1+1=n by have hn := NeZero.pos n; omega] at hh
    exact hh

def kernelSeedEquiv {R : Type*} [CommRing R] (n : ℕ) [NeZero n] :
    {x : Fin n→R // rowEq x} ≃ {u : R×R // run n u=u} where
  toFun x := ⟨seed x.val,seed_fixed x.val x.property⟩
  invFun u := ⟨fromSeed u.val,fromSeed_rowEq u.val u.property⟩
  left_inv x := by ext j; exact seed_recovers x.val x.property j
  right_inv u := Subtype.ext (seed_fromSeed u.val u.property)

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.cycleH_action
#print axioms Symconf93.AffineCycle625.seed_fixed
#print axioms Symconf93.AffineCycle625.seed_recovers

#print axioms Symconf93.AffineCycle625.kernelSeedEquiv
