module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-! Counting finite norm fibers by literal matrix multiplication. No Hasse
or Gauss-sum theorems, and no quotient of cardinalities is formed. -/
namespace Symconf93
open scoped BigOperators Matrix

section Fibers
variable {V W R : Type*} [AddGroup V] [AddGroup W]

/-- A nonempty additive fiber has exactly as many points as the kernel;
this bijection counts all preimages of the selected target fiber. -/
theorem count_addHom_fibers (f : V →+ W) (q : W → R) (t : R) :
    Nat.card {x : V // q (f x)=t} =
      Nat.card {x : V // f x=0} *
        Nat.card {y : W // (∃ x, f x=y) ∧ q y=t} := by
  classical
  let B := {y : W // (∃ x, f x=y) ∧ q y=t}
  let pick : B → V := fun y => Classical.choose y.property.1
  have hp (y : B) : f (pick y)=y.val := Classical.choose_spec y.property.1
  let toB (x : {x : V // q (f x)=t}) : B :=
    ⟨f x.val,⟨⟨x.val,rfl⟩,x.property⟩⟩
  let e : {x : V // q (f x)=t} ≃ ({x : V // f x=0} × B) :=
    { toFun := fun x => (⟨x.val - pick (toB x), by rw [map_sub,hp]; exact sub_self _⟩,toB x)
      invFun := fun y => ⟨y.1.val+pick y.2,by rw [map_add,y.1.property,hp,zero_add]; exact y.2.property.2⟩
      left_inv := by intro x; apply Subtype.ext; exact sub_add_cancel _ _
      right_inv := by
        intro y
        have hb : toB ⟨y.1.val+pick y.2, by
            rw [map_add,y.1.property,hp,zero_add]
            exact y.2.property.2⟩=y.2 := by
          apply Subtype.ext
          change f (y.1.val+pick y.2)=y.2.val
          rw [map_add,y.1.property,hp,zero_add]
        apply Prod.ext
        · apply Subtype.ext
          change y.1.val+pick y.2-pick _=y.1.val
          rw [hb,add_sub_cancel_right]
        · exact hb }
  rw [Nat.card_congr e, Nat.card_prod]

/-- Ordered target partition, including the complement; avoids any
assumption that the ambient norm ignores the nonimage residue classes. -/
theorem count_norm_partition {V₀ : Type*} [Finite V₀] (q : V₀ → R) (s : V₀ → Prop) (t : R) :
    Nat.card {x : V₀ // q x=t} =
      Nat.card {x : V₀ // s x ∧ q x=t}+Nat.card {x : V₀ // ¬s x ∧ q x=t} := by
  classical
  let e : {x : V₀ // q x=t} ≃
      ({x : V₀ // s x ∧ q x=t} ⊕ {x : V₀ // ¬s x ∧ q x=t}) :=
    { toFun := fun x => if h:s x.val then Sum.inl ⟨x.val,h,x.property⟩
        else Sum.inr ⟨x.val,h,x.property⟩
      invFun := fun x => x.elim (fun y => ⟨y.val,y.property.2⟩) (fun y => ⟨y.val,y.property.2⟩)
      left_inv := by
        intro x
        by_cases he : s x.val <;> simp [he]
      right_inv := by
        intro x
        cases x with
        | inl y => simp [y.property.1]
        | inr y => simp [y.property.1] }
  rw [Nat.card_congr e,Nat.card_sum]

/-- Exact sign conversion. The central cancellation hypothesis is a literal
bijection between the two norm fibers outside the image, not an average. -/
theorem signed_norm_count_transport [Finite W] (f : V →+ W) (q : W → R) (s t : R)
    (hcancel : {y : W // (¬ ∃x, f x=y) ∧ q y=s} ≃
      {y : W // (¬ ∃x, f x=y) ∧ q y=t}) :
    (Nat.card {x : V // q (f x)=s}:ℤ) - Nat.card {x : V // q (f x)=t} =
      (Nat.card {x : V // f x=0}:ℤ) *
        ((Nat.card {y : W // q y=s}:ℤ)-Nat.card {y : W // q y=t}) := by
  have hs := count_norm_partition q (fun y => ∃ x, f x=y) s
  have ht := count_norm_partition q (fun y => ∃ x, f x=y) t
  have hc := Nat.card_congr hcancel
  rw [count_addHom_fibers, count_addHom_fibers, hs, ht]
  push_cast
  rw [hc]
  ring

end Fibers

section Shift
variable {ι R S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [CommRing R] [AddGroup S] [DecidableEq S]

def coordinateNorm (v : ι → R) : R := ∑ i, v i * v i

omit [Nonempty ι] in
theorem norm_shift_single (v : ι → R) (i : ι) (a : R) :
    coordinateNorm (v + Pi.single i a) =
      coordinateNorm v + (2*v i*a+a*a) := by
  classical
  unfold coordinateNorm
  calc
    _ = ∑ j, (v j*v j+(if j=i then 2*v i*a+a*a else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j=i
      · subst j
        simp only [Pi.add_apply,Pi.single_eq_same,if_true]
        ring
      · simp [h]
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_ite_eq']; simp

/-- Fixed-low-digit cosets give an explicit inverse-paired translation on
the complement of the image. The scalar inputs are finite, independently
checkable equalities for the two moduli used in the application. -/
noncomputable def complement_norm_fibers_equiv
    (L : AddSubgroup (ι → R)) (c : R →+ S) (hcontain : ∀ v, (∀ i, c (v i)=0) → v∈L)
    (step : S → R) (hzero : ∀ a, c (step a)=0) (t : R)
    (hchange : ∀ a : R, c a≠0 → 2*a*step (c a)+step (c a)*step (c a)=t) :
    {v : ι→R // v∉L ∧ coordinateNorm v=0} ≃
      {v : ι→R // v∉L ∧ coordinateNorm v=t} := by
  classical
  let V := {v : ι→R // v∉L}
  have exists_bad (v : V) : ∃ i, c (v.val i)≠0 := by
    by_contra! hn
    exact v.property (hcontain _ hn)
  let index (v : V) := Classical.epsilon (fun i => c (v.val i)≠0)
  let vstep (v : V) : ι → R := Pi.single (index v) (step (c (v.val (index v))))
  have bad_index (v : V) : c (v.val (index v))≠0 := Classical.epsilon_spec (exists_bad v)
  have zero_step (v : V) (i : ι) : c (vstep v i)=0 := by
    by_cases hi : i=index v
    · subst i; simp [vstep,hzero]
    · simp [vstep,Pi.single_eq_of_ne hi]
  have in_L (v : V) : vstep v ∈ L := hcontain _ (zero_step v)
  let addV (v : V) : V := ⟨v.val+vstep v,by
    intro hv
    exact v.property (by simpa only [add_sub_cancel_right] using L.sub_mem hv (in_L v))⟩
  let subV (v : V) : V := ⟨v.val-vstep v,by
    intro hv
    exact v.property (by simpa only [sub_add_cancel] using L.add_mem hv (in_L v))⟩
  have tags_add (v : V) : (fun i => c ((addV v).val i))=(fun i => c (v.val i)) := by
    funext i
    change c (v.val i+vstep v i)=c (v.val i)
    rw [map_add,zero_step,add_zero]
  have tags_sub (v : V) : (fun i => c ((subV v).val i))=(fun i => c (v.val i)) := by
    funext i
    change c (v.val i-vstep v i)=c (v.val i)
    rw [map_sub,zero_step,sub_zero]
  have hx (u v : V) (h : (fun i => c (u.val i))=(fun i => c (v.val i))) :
      index u=index v ∧ vstep u=vstep v := by
    have hi : index u=index v :=
      congrArg (fun w : ι → S => Classical.epsilon (fun i => w i≠0)) h
    refine ⟨hi,?_⟩
    change (Pi.single (index u) (step (c (u.val (index u)))) : ι → R) =
      (Pi.single (index v) (step (c (v.val (index v)))) : ι → R)
    rw [hi,congrFun h (index v)]
  have out_add (v : V) : coordinateNorm (addV v).val=coordinateNorm v.val+t := by
    change coordinateNorm (v.val+Pi.single (index v) (step (c (v.val (index v)))))=_
    rw [norm_shift_single,hchange _ (bad_index v)]
  have back (v : V) : addV (subV v)=v := by
    apply Subtype.ext
    change v.val-vstep v+vstep (subV v)=v.val
    rw [(hx _ _ (tags_sub v)).2,sub_add_cancel]
  have back' (v : V) : subV (addV v)=v := by
    apply Subtype.ext
    change v.val+vstep v-vstep (addV v)=v.val
    rw [(hx _ _ (tags_add v)).2,add_sub_cancel_right]
  let e : V ≃ V := ⟨addV,subV,back',back⟩
  have hp (v : V) : coordinateNorm v.val=0 ↔ coordinateNorm (e v).val=t := by
    change coordinateNorm v.val=0 ↔ coordinateNorm (addV v).val=t
    rw [out_add]
    constructor
    · intro hh
      rw [hh,zero_add]
    · intro hh
      exact add_right_cancel (hh.trans (zero_add t).symm)
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : ι→R => v∉L)
      (fun v => coordinateNorm v=0)).symm.trans
    ((Equiv.subtypeEquiv e hp).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : ι→R => v∉L)
      (fun v => coordinateNorm v=t)))

end Shift
end Symconf93

#print axioms Symconf93.count_addHom_fibers
#print axioms Symconf93.signed_norm_count_transport
#print axioms Symconf93.complement_norm_fibers_equiv
