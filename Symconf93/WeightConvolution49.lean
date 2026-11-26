module
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Direct 7 by 7 integer dynamic programming. The pair state records the
weighted sum and the weighted square sum, without diagonalization. -/
namespace Symconf93.AffineFiber49
open scoped BigOperators

abbrev Joint49 := ZMod 7 × ZMod 7

def blockWeight (s : Nat) (v : ZMod 7) : Joint49 :=
  ((s:ZMod 7)*v,(s:ZMod 7)*v*v)

def jointValue (P : List Nat) (a : Fin P.length→ZMod 7) : Joint49 :=
  ∑ i,blockWeight (P.get i) (a i)

noncomputable def jointCount (P : List Nat) (u : Joint49) : Nat :=
  Nat.card {a : Fin P.length→ZMod 7 // jointValue P a=u}

private theorem joint_cons (d : Nat) (P : List Nat) (b : ZMod 7)
    (a : Fin P.length→ZMod 7) :
    jointValue (d::P) (Fin.cons b a)=blockWeight d b+jointValue P a := by
  simp only [jointValue,List.length_cons,Fin.sum_univ_succ,List.get_cons_zero,
    Fin.cons_zero,List.get_cons_succ',Fin.cons_succ]

theorem jointCount_cons (d : Nat) (P : List Nat) (t : Joint49) :
    jointCount (d::P) t = ∑ b : ZMod 7, jointCount P (t-blockWeight d b) := by
  classical
  let V (b : ZMod 7) := {a : Fin P.length→ZMod 7 // jointValue P a=t-blockWeight d b}
  let E : {a : Fin (d::P).length→ZMod 7 // jointValue (d::P) a=t} ≃
    Σ b : ZMod 7,V b :=
    {toFun := fun x => ⟨x.val 0,⟨Fin.tail x.val,by
      have h := x.property
      rw [←Fin.cons_self_tail x.val,joint_cons] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)⟩⟩
     invFun := fun b => ⟨Fin.cons b.1 b.2.val,by rw [joint_cons,b.2.property]; abel⟩
     left_inv := by intro x; exact Subtype.ext (Fin.cons_self_tail x.val)
     right_inv := by
       rintro ⟨b,a⟩
       have h : (Fin.cons (α:=fun _=>ZMod 7) b a.val) 0=b := Fin.cons_zero _ _
       refine Sigma.ext h ?_
       simp only [Fin.tail_cons]
       rfl}
  unfold jointCount
  rw [Nat.card_congr E,Nat.card_sigma]

theorem jointCount_nil (t : Joint49) : jointCount [] t=if t=0 then 1 else 0 := by
  classical
  unfold jointCount
  by_cases h : t=0
  · subst t
    haveI : Unique {a : Fin ([] : List Nat).length→ZMod 7 // jointValue [] a=0} :=
      {default := ⟨Fin.elim0,by simp [jointValue]⟩,
       uniq := fun x=>Subtype.ext (funext fun i=>i.elim0)}
    simp
  · haveI : IsEmpty {a : Fin ([] : List Nat).length→ZMod 7 // jointValue [] a=t} :=
      ⟨by rintro ⟨a,ha⟩; exact h (by simpa [jointValue] using ha.symm)⟩
    simp [h]

theorem jointValue_fst (P : List Nat) (a : Fin P.length→ZMod 7) :
    (jointValue P a).1=∑i,(P.get i:ZMod 7)*a i := by
  unfold jointValue
  exact map_sum (AddMonoidHom.fst _ _) _ _

theorem jointValue_snd (P : List Nat) (a : Fin P.length→ZMod 7) :
    (jointValue P a).2=∑i,(P.get i:ZMod 7)*a i*a i := by
  unfold jointValue
  exact map_sum (AddMonoidHom.snd _ _) _ _

def liftLookup49 (L : List Nat) (t : Joint49) : Nat := L.getD (7*t.1.val+t.2.val) 0

def jointStep (d : Nat) (L : List Nat) (t : Joint49) : Nat :=
  ∑ b : ZMod 7, liftLookup49 L (t-blockWeight d b)

theorem liftLookup49_base {L : List Nat}
    (h : ∀ t : Joint49,liftLookup49 L t=if t=0 then 1 else 0) :
    ∀ t,jointCount [] t=liftLookup49 L t :=
  fun t=>(jointCount_nil t).trans (h t).symm

theorem liftLookup49_step {P : List Nat} {d : Nat} {L K : List Nat}
    (hP : ∀ t,jointCount P t=liftLookup49 L t)
    (h : ∀ t : Joint49,liftLookup49 K t=jointStep d L t) :
    ∀ t,jointCount (d::P) t=liftLookup49 K t := by
  intro t
  rw [jointCount_cons,h,jointStep]
  exact Finset.sum_congr rfl (fun b _=>hP _)

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.jointCount_cons
#print axioms Symconf93.AffineFiber49.liftLookup49_step
