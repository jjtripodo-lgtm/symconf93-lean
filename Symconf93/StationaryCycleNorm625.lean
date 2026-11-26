module
public import Symconf93.CycleNorm625
public import Symconf93.AffineKernel625

@[expose] public section

namespace Symconf93.AffineCycle625
open Symconf59 AffineFiber625 Matrix
open scoped BigOperators Matrix

def cycleM (n : ℕ) : Fin n→Fin n→ZMod 625 :=
  (cycleH93 n).map (Int.castRingHom (ZMod 625))

theorem cycleH_symmetric {n : ℕ} (i j : Fin n) :
    cycleH93 n i j=cycleH93 n j i := by
  letI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  have pn (x : Fin n) : cprev (cnext x)=x := by
    change (x+1)-1=x
    exact add_sub_cancel_right x 1
  have h1 : (j=cnext i)=(i=cprev j) := propext <| by
    constructor
    · intro h; rw [h,pn]
    · intro h; rw [h,cnext_prev]
  have h2 : (j=cprev i)=(i=cnext j) := propext <| by
    constructor
    · intro h; rw [h,cnext_prev]
    · intro h; rw [h,pn]
  unfold cycleH93
  have e0 : (if i=j then (1:ℤ) else 0)=(if j=i then 1 else 0) :=
    if_congr eq_comm rfl rfl
  have e1 : (if j=cnext i then (1:ℤ) else 0)=(if i=cprev j then 1 else 0) :=
    if_congr (Iff.of_eq h1) rfl rfl
  have e2 : (if j=cprev i then (1:ℤ) else 0)=(if i=cnext j then 1 else 0) :=
    if_congr (Iff.of_eq h2) rfl rfl
  rw [e0,e1,e2]
  ring

theorem cycleM_symmetric (n : ℕ) : ∀ i j, cycleM n i j=cycleM n j i := by
  intro i j
  change ((cycleH93 n i j:ℤ):ZMod 625) = ((cycleH93 n j i:ℤ):ZMod 625)
  rw [cycleH_symmetric]

theorem cycleNorm_eq_quad (n : ℕ) (x : Fin n→ZMod 625) :
    cycleNorm n x=quad (cycleM n) x := by
  unfold cycleNorm quad cycleM
  simp only [mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem cycle_is_stationary (n : ℕ) (x : Fin n→ZMod 25) (hx : rowEq x) :
    derivative (cycleM n) (fun i=>lowCast (x i))=0 := by
  apply (derivative_zero_iff_kernel _ _).2
  intro j
  have hline (i : Fin n) :
      x i*lowReduce (cycleM n i j) =
        (((cycleH93 n).map (Int.castRingHom (ZMod 25))) j i)*x i := by
    rw [cycleM_symmetric n i j]
    change x i*lowReduce (((cycleH93 n j i:ℤ):ZMod 625)) =
      ((cycleH93 n j i:ℤ):ZMod 25)*x i
    rw [map_intCast,mul_comm]
  simp_rw [hline]
  change ((((cycleH93 n).map (Int.castRingHom (ZMod 25))) *ᵥ x) j)=_
  rw [cycleH_action]
  exact hx j

def stationaryCycleQuad (n : ℕ) (x : {x : Fin n→ZMod 25 // rowEq x}) : ZMod 625 :=
  quad (cycleM n) (fun i => lowCast (x.val i))

theorem stationaryCycleQuad_lift {n : ℕ} [NeZero n]
    (x : {x : Fin n→ZMod 25 // rowEq x}) (u : ZMod 625×ZMod 625)
    (hu : (lowReduce u.1,lowReduce u.2)=seed x.val) :
    stationaryCycleQuad n x=cycleNorm n (fromSeed u) := by
  unfold stationaryCycleQuad
  rw [cycleNorm_eq_quad]
  symm
  apply stationary_lift_invariant _ (cycleM_symmetric _) _
    (cycle_is_stationary _ _ x.property)
  intro i
  rw [fromSeed_map,hu]
  exact seed_recovers x.val x.property i

def low5Map : ZMod 625→+*ZMod 5 := ZMod.castHom (by decide : 5 ∣ 625) (ZMod 5)
def fiveLift (a : ZMod 5) : ZMod 625 := 125*(a.val:ZMod 625)

theorem fiveLift_map : ∀ x : ZMod 625, fiveLift (low5Map x)=125*x := by
  decide +kernel

theorem local_norm_deep625 (j : Fin 11) [NeZero (lengths j)]
    (hj : layers j=2) (x : {x : Fin (lengths j)→ZMod 25 // rowEq x}) :
    stationaryCycleQuad (lengths j) x=highLift (phase (normalized j) (seed x.val)) := by
  let p := seed x.val
  let u := (lowCast p.1,lowCast p.2)
  have hU : (lowReduce u.1,lowReduce u.2)=seed x.val := by
    simp [u,p,reduce_lowCast]
  rw [stationaryCycleQuad_lift x u hU,cycleNorm_deep625 j hj,
      ←highLift_reduce,phase_map,hU]

def seedDigit (a : ZMod 25) : ZMod 5 := (a.val/5:ℕ)
def seedLift (a : ZMod 5) : ZMod 25 := 5*(a.val:ZMod 25)

theorem seed_digit_roundtrip :
    ∀ a : ZMod 25, 5*a=0 → seedLift (seedDigit a)=a := by
  decide +kernel

theorem seed_lift_roundtrip : ∀ a : ZMod 5, seedDigit (seedLift a)=a := by
  decide +kernel

theorem seed_lift_annihilator : ∀ a : ZMod 5, 5*seedLift a=0 := by
  decide +kernel

def seedDigitPair (u : ZMod 25×ZMod 25) : ZMod 5×ZMod 5 :=
  (seedDigit u.1,seedDigit u.2)

theorem local_norm_active625 (j : Fin 11) [NeZero (lengths j)]
    (hj : layers j=1) (x : {x : Fin (lengths j)→ZMod 25 // rowEq x}) :
    stationaryCycleQuad (lengths j) x=fiveLift (fixPhase j (seedDigitPair (seed x.val))) := by
  let p := seed x.val
  have hp := (fixed_seed625 j p).mp (seed_fixed x.val x.property)
  rw [hj,pow_one] at hp
  let u : ZMod 625×ZMod 625 := ((seedDigit p.1).val,(seedDigit p.2).val)
  have hu : (lowReduce (5*u.1),lowReduce (5*u.2))=seed x.val := by
    apply Prod.ext
    · change lowReduce (5*((seedDigit p.1).val:ZMod 625))=p.1
      simp only [map_mul,map_ofNat,map_natCast]
      exact seed_digit_roundtrip _ hp.1
    · change lowReduce (5*((seedDigit p.2).val:ZMod 625))=p.2
      simp only [map_mul,map_ofNat,map_natCast]
      exact seed_digit_roundtrip _ hp.2
  have hd (a : ZMod 5) : low5Map (a.val:ZMod 625)=a := by
    rw [map_natCast,ZMod.natCast_zmod_val]
  rw [stationaryCycleQuad_lift x (5*u.1,5*u.2) hu,cycleNorm_active625 j hj,←fiveLift_map,phase_map]
  unfold fixPhase seedDigitPair u
  rw [hd,hd]

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.local_norm_deep625
#print axioms Symconf93.AffineCycle625.local_norm_active625
