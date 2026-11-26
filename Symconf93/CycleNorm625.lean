module
public import Symconf93.CycleReducedForms625

@[expose] public section

/-! The exact norm of lifted fixed-seed cycle solutions at modulus 625. -/
namespace Symconf93.AffineCycle625
open Symconf59
open scoped BigOperators Matrix

def cycleNorm {R : Type*} [CommRing R] (n : ℕ) (x : Fin n→R) : R :=
  ∑ i, x i * (((cycleH93 n).map (Int.castRingHom R)) *ᵥ x) i

private theorem lengths_lower : ∀ j : Fin 11, 2≤lengths j := by decide +kernel

theorem cycleNorm_seed_factored (j : Fin 11) (u : ZMod 625×ZMod 625) :
    cycleNorm (lengths j) (fromSeed u) =
      (5:ZMod 625)^layers j * phase (normalized j) u+
      ((5:ZMod 625)^layers j)^2*
        (act (normalized j) u).1*(act (normalized j) u).2 := by
  let k := lengths j-2
  have hk : k+2=lengths j := by
    have hj := lengths_lower j; dsimp [k]; omega
  have h := boundary_inflated k ((5:ℤ)^layers j) (normalized j) u (by
    rw [hk]; exact cols_normalized j)
  rw [hk] at h
  simp only [Int.cast_pow,Int.cast_ofNat] at h
  unfold cycleNorm
  simp_rw [cycleH_action]
  exact h

theorem cycleNorm_active625 (j : Fin 11) (hj : layers j=1)
    (u : ZMod 625×ZMod 625) :
    cycleNorm (lengths j) (fromSeed (5*u.1,5*u.2)) =
      125 * phase (normalized j) u := by
  rw [cycleNorm_seed_factored,hj,pow_one]
  unfold phase act
  have hz : (625:ZMod 625)=0 := by decide +kernel
  linear_combination
     (((normalized j).1.1:ZMod 625)*u.1+((normalized j).2.1:ZMod 625)*u.2)*
     (((normalized j).1.2:ZMod 625)*u.1+((normalized j).2.2:ZMod 625)*u.2)*hz

theorem cycleNorm_deep625 (j : Fin 11) (hj : layers j=2)
    (u : ZMod 625×ZMod 625) :
    cycleNorm (lengths j) (fromSeed u) =
      25 * phase (normalized j) u := by
  rw [cycleNorm_seed_factored,hj,show (5:ZMod 625)^2=25 by decide +kernel,
    show (25:ZMod 625)^2=0 by decide +kernel,zero_mul,zero_mul,add_zero]

theorem run_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S) (k : ℕ) (u : R×R) :
    (f (run k u).1,f (run k u).2)=run k (f u.1,f u.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (f (9*(run k u).1-(run k u).2), f (run k u).1)=
      step (run k (f u.1,f u.2))
    rw [←ih]
    simp [step,map_ofNat]

theorem fromSeed_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (u : R×R) {n : ℕ} (i : Fin n) :
    f (fromSeed u i)=fromSeed (f u.1,f u.2) i :=
  congrArg Prod.fst (run_map f i.val u)

theorem phase_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R) :
    f (phase M u)=phase M (f u.1,f u.2) := by
  simp [phase,act]

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.cycleNorm_active625
#print axioms Symconf93.AffineCycle625.cycleNorm_deep625
#print axioms Symconf93.AffineCycle625.fromSeed_map
