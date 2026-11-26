module
public import Symconf93.CycleSeed625
public import Symconf93.CycleBoundary625

@[expose] public section

/-! Small cycle phase forms on the low-digit kernel. -/
namespace Symconf93.AffineCycle625
open Symconf59
open scoped BigOperators

def phase {R : Type*} [Ring R] (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R) : R :=
  u.2*(act M u).1-u.1*(act M u).2

theorem run_inflated {R : Type*} [CommRing R] (l : ℕ) (q : ℤ)
    (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R) (h : cols l=inflated q M) :
    run l u=(u.1+(q:R)*(act M u).1,u.2+(q:R)*(act M u).2) := by
  rw [run_eq_act,h]
  unfold inflated act
  push_cast
  exact Prod.ext (by ring) (by ring)

theorem boundary_inflated {R : Type*} [CommRing R] (k : ℕ) (q : ℤ)
    (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R) (h : cols (k+2)=inflated q M) :
    let x : Fin (k+2) → R := fromSeed u
    (∑ i, x i*(9*x i-x (cnext i)-x (cprev i))) =
      (q:R)*phase M u+(q:R)^2*(act M u).1*(act M u).2 := by
  change (∑ i : Fin (k+2), fromSeed u i*
    (9*fromSeed u i-fromSeed u (cnext i)-fromSeed u (cprev i))) = _
  rw [fromSeed_quad_boundary, run_inflated (k+2) q M u h]
  simp only [phase]
  ring

def fixPhase (j : Fin 11) (u : ZMod 5×ZMod 5) : ZMod 5 :=
  phase (normalized j) u

private theorem active_coeffs :
    ∀ j : Fin 11, layers j=1 →
      let m : ZMod 5 := (lengths j/3:ℕ)
      let M := normalized j
      (M.1.1:ZMod 5)=2*m ∧ (M.1.2:ZMod 5)=m ∧
        (M.2.1:ZMod 5)=4*m ∧ (M.2.2:ZMod 5)=3*m ∧ m≠0 := by
  decide +kernel

theorem active_phase (j : Fin 11) (hj : layers j=1) (u : ZMod 5×ZMod 5) :
    fixPhase j u=binaryActive (lengths j/3:ℕ) u := by
  obtain ⟨h1,h2,h3,h4,_⟩ := active_coeffs j hj
  unfold fixPhase phase act binaryActive
  rw [h1,h2,h3,h4]
  have hz : (5:ZMod 5)=0 := by decide +kernel
  linear_combination -((lengths j/3:ℕ):ZMod 5)*(u.1^2+u.1*u.2)*hz

theorem active_phase_count (j : Fin 11) (hj : layers j=1) (t : ZMod 5) :
    (Finset.univ.filter fun u : ZMod 5×ZMod 5 => fixPhase j u=t).card =
      if t=0 then 1 else 6 := by
  simp_rw [active_phase j hj]
  exact binaryActive_count _ _ (active_coeffs j hj).2.2.2.2

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.boundary_inflated
#print axioms Symconf93.AffineCycle625.active_phase_count
