module
public import Symconf93.ExactSmallShifts

@[expose] public section

/-! Ambient contrast by the cancellation outside a subgroup whose
internal squared norms all vanish at the square modulus. -/
namespace Symconf93
open scoped BigOperators Matrix

section
variable {ι R S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [CommRing R] [Finite R] [AddGroup S] [DecidableEq S]

theorem ambient_contrast_pos_of_nilpotent_scale (a : R) (ha : a*a=0)
    (c : R→+S) (s : S→R) (t : R) (ht : t≠0)
    (hTag : ∀ x:R, c x=0 → ∃ y, x=a*y)
    (hStep : ∀ b,c (s b)=0)
    (hCross : ∀ x:R,c x≠0 → 2*x*s (c x)+s (c x)*s (c x)=t) :
    0<contrast (coordinateNorm (ι:=ι)) t := by
  classical
  let L : AddSubgroup (ι → R) :=
    { carrier := {v | ∀ i,c (v i)=0}
      zero_mem' := by intro i; exact map_zero c
      add_mem' := by
        intro u v hu hv i
        change c (u i+v i)=0
        rw [map_add,hu i,hv i,zero_add]
      neg_mem' := by
        intro v hv i
        change c (-v i)=0
        rw [map_neg,hv i,neg_zero] }
  have hcontain (v : ι→R) (hv : ∀ i,c (v i)=0) : v∈L := hv
  have hin (v : ι→R) (hv : v∈L) : coordinateNorm v=0 := by
    unfold coordinateNorm
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨y,hy⟩ := hTag (v i) (hv i)
    rw [hy,show a*y*(a*y)=a*a*(y*y) by ring,ha,zero_mul]
  have he := Nat.card_congr (complement_norm_fibers_equiv L c hcontain s hStep t hCross)
  have h0 := count_norm_partition (coordinateNorm (ι:=ι)) (· ∈ L) 0
  have h1 := count_norm_partition (coordinateNorm (ι:=ι)) (· ∈ L) t
  letI : Nonempty {v : ι→R // v∈L ∧ coordinateNorm v=0} :=
    ⟨⟨0,L.zero_mem,hin _ L.zero_mem⟩⟩
  have hp : 0<Nat.card {v : ι→R // v∈L ∧ coordinateNorm v=0} := Finite.card_pos
  letI : IsEmpty {v : ι→R // v∈L ∧ coordinateNorm v=t} :=
    ⟨fun v => ht (v.property.2.symm.trans (hin v.val v.property.1))⟩
  have hz : Nat.card {v : ι→R // v∈L ∧ coordinateNorm v=t}=0 := by simp
  unfold contrast
  rw [h0,h1,hz,zero_add,he]
  push_cast
  omega

end

section N
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
open Matrix

theorem ambient49_contrast_positive :
    0<contrast (coordinateNorm (ι:=ι)) (7:ZMod 49) :=
  ambient_contrast_pos_of_nilpotent_scale (7:ZMod 49) (by decide) tag49 shift49 7
    (by decide) (fun a h => ⟨(a.val/7:ℕ),tag49_zero_exact a h⟩)
    shift49_same_tag shift49_norm_step

theorem ambient625_contrast_positive :
    0<contrast (coordinateNorm (ι:=ι)) (125:ZMod 625) :=
  ambient_contrast_pos_of_nilpotent_scale (25:ZMod 625) (by decide) tag625 shift625 125
    (by decide) (fun a h => ⟨(a.val/25:ℕ),tag625_zero_exact a h⟩)
    shift625_same_tag shift625_norm_step

theorem genuineGram49_contrast_nonnegative
    (A M : Matrix ι ι (ZMod 49))
    (hm : Aᵀ*M=(7:ZMod 49) • (1:Matrix ι ι (ZMod 49))) :
    0≤contrast (gramNorm (A*Aᵀ)) (7:ZMod 49) :=
  prime49_gram_contrast A M hm (le_of_lt ambient49_contrast_positive)

theorem genuineGram625_contrast_nonnegative
    (A M : Matrix ι ι (ZMod 625))
    (hm : Aᵀ*M=(25:ZMod 625) • (1:Matrix ι ι (ZMod 625))) :
    0≤contrast (gramNorm (A*Aᵀ)) (125:ZMod 625) :=
  prime625_gram_contrast A M hm (le_of_lt ambient625_contrast_positive)

end N
end Symconf93

#print axioms Symconf93.ambient49_contrast_positive
#print axioms Symconf93.ambient625_contrast_positive
#print axioms Symconf93.genuineGram49_contrast_nonnegative
#print axioms Symconf93.genuineGram625_contrast_nonnegative
