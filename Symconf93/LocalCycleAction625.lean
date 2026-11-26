module
public import Symconf93.ContrastProduct625
public import Symconf93.ProfileBlock625

@[expose] public section

namespace Symconf93.AffineCycle625
open AffineFiber625
open scoped BigOperators

def cycleFactor625 (j : Fin 11) : ℤ :=
  if layers j=1 then -5 else if layers j=2 then 25 else 1

theorem cycleLayer_cases : ∀ j : Fin 11, layers j=0 ∨ layers j=1 ∨ layers j=2 := by
  decide +kernel
private theorem cycleLen_pos : ∀ j : Fin 11, lengths j≠0 := by decide +kernel
private theorem deep_is_fifteen : ∀ j : Fin 11, layers j=2 → j=5 := by decide +kernel

private theorem act5_hist_aux :
    ∀ r : ZMod 5, ((if r=0 then 1 else 6 : ℕ):ℤ)-
      (if r+1=0 then 1 else 6 : ℕ) =
      (-5)*((if r=0 then (1:ℤ) else 0)-(if r+1=0 then 1 else 0)) := by
  decide +kernel

private theorem act25_hist_aux :
    ∀ r : ZMod 25, (binary15Expected r:ℤ)-binary15Expected (r+5) =
      25*((if r=0 then (1:ℤ) else 0)-(if r+5=0 then 1 else 0)) := by
  decide +kernel

private theorem diffActive (j : Fin 11) (hj : layers j=1) :
    DiffAction (125:ZMod 625) (fun u => fiveLift (fixPhase j u)) (-5) :=
  diffAction_of_hist 125 1 fiveLift (fixPhase j) (-5)
    (fun t => if t=0 then 1 else 6)
    (by decide +kernel) (by decide +kernel) (active_phase_count j hj) act5_hist_aux

private theorem diffDeep :
    DiffAction (125:ZMod 625) (fun u => highLift (binary15 u)) 25 :=
  diffAction_of_hist 125 5 highLift binary15 25 binary15Expected
    (by decide +kernel) (fun r => by rw [highLift_add,highLift_five])
    binary15_histogram act25_hist_aux

private def activeDigits :
    {u : ZMod 25×ZMod 25 // 5*u.1=0 ∧ 5*u.2=0} ≃ (ZMod 5×ZMod 5) where
  toFun u := seedDigitPair u.val
  invFun u := ⟨(seedLift u.1,seedLift u.2),
    seed_lift_annihilator u.1,seed_lift_annihilator u.2⟩
  left_inv u := Subtype.ext (Prod.ext
    (seed_digit_roundtrip _ u.property.1) (seed_digit_roundtrip _ u.property.2))
  right_inv _u := Prod.ext (seed_lift_roundtrip _) (seed_lift_roundtrip _)

private def activeCycleEquiv (j : Fin 11) (hj : layers j=1)
    [NeZero (lengths j)] : CycleKernel (lengths j) ≃ (ZMod 5×ZMod 5) :=
  (kernelSeedEquiv (R:=ZMod 25) (lengths j)).trans
    (((Equiv.refl (ZMod 25×ZMod 25)).subtypeEquiv
      (p:=fun u => run (lengths j) u=u)
      (q:=fun u => 5*u.1=0 ∧ 5*u.2=0)
      (fun u => by simpa [hj] using fixed_seed625 j u)).trans activeDigits)

private def deepSeedEquiv (j : Fin 11) (hj : layers j=2) :
    {u : ZMod 25×ZMod 25 // run (lengths j) u=u} ≃ (ZMod 25×ZMod 25) where
  toFun u := u.val
  invFun u := ⟨u,(fixed_seed625 j u).mpr (by
    rw [hj,show (5:ZMod 25)^2=0 by decide +kernel]
    simp)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem run_zero {R : Type*} [Ring R] (n : ℕ) : run n ((0:R),0)=(0,0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (run n ((0:R),0))=(0,0)
    rw [ih]; simp [step]

private theorem zeroCycle_unique (j : Fin 11) (hj : layers j=0)
    [NeZero (lengths j)] (x : CycleKernel (lengths j)) : x.val=0 := by
  have hs := (fixed_seed625 j (seed x.val)).mp (seed_fixed x.val x.property)
  simp [hj] at hs
  have hS : seed x.val=(0,0) := Prod.ext hs.1 hs.2
  funext i
  rw [← seed_recovers x.val x.property i,hS,run_zero]
  rfl

private def zeroCycleEquiv (j : Fin 11) (hj : layers j=0) [NeZero (lengths j)] :
    CycleKernel (lengths j) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0,by intro i; simp⟩
  left_inv x := Subtype.ext (zeroCycle_unique j hj x).symm
  right_inv _ := Subsingleton.elim _ _

theorem localCycleAction625 (j : Fin 11) :
    DiffAction (125:ZMod 625)
      (fun x : CycleKernel (lengths j) => stationaryCycleQuad (lengths j) x)
      (cycleFactor625 j) := by
  letI : NeZero (lengths j) := ⟨cycleLen_pos j⟩
  rcases cycleLayer_cases j with hz|ha|hd
  · rw [cycleFactor625,hz]
    simp only [Nat.reduceEqDiff,if_false]
    refine diffAction_transport 125 _ (fun _ : Unit => 0) 1
      (zeroCycleEquiv j hz) ?_ ?_
    · intro x
      unfold stationaryCycleQuad
      rw [zeroCycle_unique j hz x]
      simp [quad,lowCast]
    · intro f t
      simp
  · simp only [cycleFactor625,ha,ite_true]
    exact diffAction_transport 125 _ _ (-5) (activeCycleEquiv j ha)
      (fun x => local_norm_active625 j ha x) (diffActive j ha)
  · have hEq := deep_is_fifteen j hd
    subst j
    rw [cycleFactor625,hd]
    simp only [Nat.reduceEqDiff,if_false,ite_true]
    let e0 := (kernelSeedEquiv (R:=ZMod 25) (lengths (5:Fin 11))).trans
      (deepSeedEquiv 5 hd)
    let e := e0.trans seed15Equiv
    refine diffAction_transport 125 _ _ 25 e ?_ diffDeep
    intro x
    calc
      _ = highLift (phase (normalized (5 : Fin 11)) (seed x.val)) :=
        local_norm_deep625 5 hd x
      _ = highLift (binary15 (seed15Equiv (seed x.val))) :=
        congrArg highLift (phase_fifteen_as_diag (seed x.val))
      _ = _ := rfl

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.localCycleAction625
