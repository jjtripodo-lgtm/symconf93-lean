module
public import Symconf93.AffineCount49
public import Symconf93.CycleConstant49
public import Symconf93.WeightConvolution49
public import Symconf93.Terminal93

@[expose] public section

/-! The pivot-free q49 kernel is attached to the literal profile Gram:
nine on the diagonal, all ones, minus literal neighboring cycle sites. -/
namespace Symconf93.AffineFiber49
open Symconf59 Matrix
open scoped BigOperators Matrix

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def siteNext {P : List Nat} (v : BlocksOf P) : BlocksOf P := ⟨v.1,cnext v.2⟩
def sitePrev {P : List Nat} (v : BlocksOf P) : BlocksOf P := ⟨v.1,cprev v.2⟩

theorem sitePrev_next {P : List Nat} (v : BlocksOf P) : sitePrev (siteNext v)=v := by
  rcases v with ⟨k,r⟩; simp [sitePrev,siteNext,cprev_next49]

theorem siteNext_prev {P : List Nat} (v : BlocksOf P) : siteNext (sitePrev v)=v := by
  rcases v with ⟨k,r⟩; simp [sitePrev,siteNext,cnext_prev]

def profileForm49 (P : List Nat) : Matrix (BlocksOf P) (BlocksOf P) (ZMod 49) :=
  fun x y => 9*(if x=y then 1 else 0)+1 -
    ((if y=siteNext x then 1 else 0)+(if y=sitePrev x then 1 else 0))

theorem form_is_original49 (P : List Nat) :
    profileForm49 P=Symconf59.reduceMatrix 49 (profileGram93 P) := by
  ext x y
  change profileForm49 P x y=((profileGram93 P x y:ℤ):ZMod 49)
  unfold profileForm49 profileGram93 profileAdj93 siteNext sitePrev
  split_ifs <;> push_cast <;> rfl

theorem form_symm49 (P : List Nat) (x y : BlocksOf P) :
    profileForm49 P x y=profileForm49 P y x := by
  have hN : y=siteNext x ↔ x=sitePrev y :=
    ⟨fun h=>by rw [h,sitePrev_next],fun h=>by rw [h,siteNext_prev]⟩
  have hP : y=sitePrev x ↔ x=siteNext y :=
    ⟨fun h=>by rw [h,siteNext_prev],fun h=>by rw [h,sitePrev_next]⟩
  unfold profileForm49
  simp only [hN,hP]
  have hd : (if x=y then (1:ZMod 49) else 0)=(if y=x then 1 else 0) := by
    by_cases h : x=y
    · subst y; rfl
    · simp [h,Ne.symm h]
  rw [hd]
  ring


theorem form_mv49 (P : List Nat) (a : BlocksOf P→ZMod 49) (v : BlocksOf P) :
    (profileForm49 P *ᵥ a) v=9*a v+(∑ j,a j)-a (siteNext v)-a (sitePrev v) := by
  unfold mulVec dotProduct
  calc
    _ = ∑ j, ((if v=j then 9*a j else 0)+a j -
        ((if j=siteNext v then a j else 0)+(if j=sitePrev v then a j else 0))) := by
      apply Finset.sum_congr rfl
      intro j _
      change (9*(if v=j then 1 else 0)+1 -
        ((if j=siteNext v then 1 else 0)+(if j=sitePrev v then 1 else 0)))*a j=_
      split_ifs <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_ite_eq,
        Finset.sum_ite_eq',Finset.mem_univ,if_true]
      ring

theorem form_derivative49 (P : List Nat)
    (a : Digits (BlocksOf P)) (v : BlocksOf P) :
    lowDeriv (profileForm49 P) a v=
      2*(2*a v+(∑ j,a j)-a (siteNext v)-a (sitePrev v)) := by
  have he : (∑ j,lowCast (a j)*profileForm49 P j v)=
      (profileForm49 P *ᵥ (lowCast ∘ a)) v := by
    unfold mulVec dotProduct
    apply Finset.sum_congr rfl
    intro j _
    rw [form_symm49 P j v,mul_comm]
    all_goals rfl
  change lowReduce (2*(∑ j,lowCast (a j)*profileForm49 P j v))=_
  rw [he,form_mv49]
  simp only [Function.comp_apply,map_mul,map_ofNat,map_sub,map_add,map_sum,reduce_lowCast]
  rw [show (9:ZMod 7)=2 by decide +kernel]

def cycleConstant49 (P : List Nat) (c : Fin P.length→ZMod 7) :
    Digits (BlocksOf P) := fun x=>c x.1

theorem sum_cycleConstant49 (P : List Nat) (c : Fin P.length→ZMod 7) :
    (∑ j,cycleConstant49 P c j)=(jointValue P c).1 := by
  rw [Fintype.sum_sigma,jointValue_fst]
  simp [cycleConstant49,nsmul_eq_mul]

def posCycle49 {P : List Nat} (h : ∀ b : Fin P.length,(P.get b:ZMod 7)≠0)
    (b : Fin P.length) : 0<P.get b := by
  apply Nat.pos_of_ne_zero
  intro hh
  exact h b (by rw [hh,Nat.cast_zero])

def startCycle49 {P : List Nat} (h : ∀ b : Fin P.length,(P.get b:ZMod 7)≠0)
    (b : Fin P.length) : Fin (P.get b) := ⟨0,posCycle49 h b⟩

/-- Odd characteristic recurses along the literal cycles. The full
global sum is forced zero by any one invertible cycle length. -/
theorem derivative_kernel49 {P : List Nat} (hp : 0<P.length)
    (hL : ∀ b : Fin P.length,(P.get b:ZMod 7)≠0)
    (a : Digits (BlocksOf P)) :
    lowDeriv (profileForm49 P) a=0 ↔
      a=cycleConstant49 P (fun b => a ⟨b,startCycle49 hL b⟩) ∧ (∑ j,a j)=0 := by
  constructor
  · intro h
    have court (b : Fin P.length) :=
      @nondivisible_cycle_steady49 (P.get b) ⟨(posCycle49 hL b).ne'⟩ (hL b)
        (fun j=>a ⟨b,j⟩) (∑ j,a j) (by
          intro j
          have hh := congrFun h ⟨b,j⟩
          rw [form_derivative49] at hh
          exact (mul_eq_zero.mp hh).resolve_left (by decide +kernel))
    refine ⟨funext (fun ⟨b,j⟩=> (court b).2 j),(court ⟨0,hp⟩).1⟩
  · rintro ⟨he,hs⟩
    funext j
    rw [form_derivative49,hs]
    rw [he]
    let z := a ⟨j.1,startCycle49 hL j.1⟩
    change (2:ZMod 7)*(2*z+0-z-z)=0
    ring

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.form_is_original49
#print axioms Symconf93.AffineFiber49.derivative_kernel49
