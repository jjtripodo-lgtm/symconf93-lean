module
public import Symconf93.PhaseMomentSound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Attach the tested moment veto to the actual lists of residues.
This is a physical cover exclusion for literal prototypes, not a proof
that every arbitrary support belongs to the 35-row catalog. -/
namespace Symconf93
open OffsetMoments

def lm31 (D : List Nat) (n : Nat) : F :=
  (D.map (fun x : Nat => (x:F)^n)).sum

private theorem lm31_append (D E : List Nat) (n : Nat) :
    lm31 (D++E) n=lm31 D n+lm31 E n := by
  simp [lm31,List.sum_append]

private theorem lm31_cons (a : Nat) (T : List Nat) (n : Nat) :
    lm31 (a::T) n=(a:F)^n+lm31 T n := rfl

private theorem shifted31_cons (a : Nat) (T : List Nat) (x : Nat) :
    shifted31 (a::T) x=(a+x)%31 :: shifted31 T x := rfl

private theorem lm31_as_nat (D : List Nat) (n : Nat) :
    (((D.map (fun x => x^n)).sum:Nat):F)=lm31 D n := by
  induction D with
  | nil => rfl
  | cons a T ih =>
    rw [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_pow,ih,lm31_cons]

private theorem lm31_cast_m1 (D : List Nat) : lm31 D 1=(momentsRaw31 D).s := by
  simp only [momentsRaw31,ZMod.natCast_mod]
  induction D with
  | nil => rfl
  | cons a T ih =>
    rw [lm31_cons,pow_one,List.sum_cons,Nat.cast_add,ih]

private theorem lm31_cast_m2 (D : List Nat) : lm31 D 2=(momentsRaw31 D).q := by
  simp only [momentsRaw31,ZMod.natCast_mod]
  exact (lm31_as_nat D 2).symm

private theorem lm31_cast_m3 (D : List Nat) : lm31 D 3=(momentsRaw31 D).c := by
  simp only [momentsRaw31,ZMod.natCast_mod]
  exact (lm31_as_nat D 3).symm

private theorem lm31_cast_m4 (D : List Nat) : lm31 D 4=(momentsRaw31 D).d := by
  simp only [momentsRaw31,ZMod.natCast_mod]
  exact (lm31_as_nat D 4).symm

private theorem shift_m1 (D : List Nat) (x : Nat) :
    lm31 (shifted31 D x) 1=lm31 D 1+(D.length:F)*(x:F) := by
  induction D with
  | nil => simp [lm31,shifted31]
  | cons a T ih =>
    rw [shifted31_cons,lm31_cons,ZMod.natCast_mod,Nat.cast_add,ih]
    simp only [lm31_cons,List.length_cons,Nat.cast_succ]
    ring

private theorem shift_m2 (D : List Nat) (x : Nat) :
    lm31 (shifted31 D x) 2=
      lm31 D 2+2*(x:F)*lm31 D 1+(D.length:F)*(x:F)^2 := by
  induction D with
  | nil => simp [lm31,shifted31]
  | cons a T ih =>
    rw [shifted31_cons,lm31_cons,ZMod.natCast_mod,Nat.cast_add,ih]
    simp only [lm31_cons,List.length_cons,Nat.cast_succ]
    ring

private theorem shift_m3 (D : List Nat) (x : Nat) :
    lm31 (shifted31 D x) 3=
      lm31 D 3+3*(x:F)*lm31 D 2+3*(x:F)^2*lm31 D 1+(D.length:F)*(x:F)^3 := by
  induction D with
  | nil => simp [lm31,shifted31]
  | cons a T ih =>
    rw [shifted31_cons,lm31_cons,ZMod.natCast_mod,Nat.cast_add,ih]
    simp only [lm31_cons,List.length_cons,Nat.cast_succ]
    ring

private theorem shift_m4 (D : List Nat) (x : Nat) :
    lm31 (shifted31 D x) 4=lm31 D 4+4*(x:F)*lm31 D 3+
      6*(x:F)^2*lm31 D 2+4*(x:F)^3*lm31 D 1+(D.length:F)*(x:F)^4 := by
  induction D with
  | nil => simp [lm31,shifted31]
  | cons a T ih =>
    rw [shifted31_cons,lm31_cons,ZMod.natCast_mod,Nat.cast_add,ih]
    simp only [lm31_cons,List.length_cons,Nat.cast_succ]
    ring

private theorem root_cover31_perm (D : List Nat)
    (hD : ∀ a∈D,a<31) (h : isCover31 D=true) : D.Perm (List.range 31) := by
  apply List.perm_iff_count.mpr
  intro a
  by_cases ha : a<31
  · have hc := List.all_eq_true.mp h _ (List.mem_range.mpr ha)
    simpa [List.count_range,ha] using hc
  · have hc : a∉D := fun hm => ha (hD a hm)
    rw [List.count_eq_zero_of_not_mem hc,List.count_range,if_neg ha]

private theorem moments_range31 :
    lm31 (List.range 31) 1=0 ∧ lm31 (List.range 31) 2=0 ∧
      lm31 (List.range 31) 3=0 ∧ lm31 (List.range 31) 4=0 := by decide +kernel

theorem actual_list_cover_disagrees_with_moment_veto
    (D E T : List Nat) (x y : Nat)
    (hD : ∀ a∈D,a<31) (hE : E.length=15) (hT : T.length=10)
    (hV : phaseMomentVeto31 (momentsRaw31 D) (momentsRaw31 E) (momentsRaw31 T)=true)
    (hcov : isCover31 (D++shifted31 E x++shifted31 T y)=true) : False := by
  let U := D++shifted31 E x++shifted31 T y
  have hb : ∀ a∈U,a<31 := by
    intro a ha
    rcases List.mem_append.mp ha with hleft|hTail
    · rcases List.mem_append.mp hleft with hLeft|hMid
      · exact hD _ hLeft
      · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hMid
        exact Nat.mod_lt _ (by decide)
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hTail
      exact Nat.mod_lt _ (by decide)
  have hperm := root_cover31_perm U hb hcov
  have H (k : Nat) : lm31 U k=lm31 (List.range 31) k :=
    (hperm.map (fun z : Nat => (z:F)^k)).sum_eq
  have h1 := (H 1).trans moments_range31.1
  have h2 := (H 2).trans moments_range31.2.1
  have h3 := (H 3).trans moments_range31.2.2.1
  have h4 := (H 4).trans moments_range31.2.2.2
  dsimp only [U] at h1 h2 h3 h4
  rw [lm31_append,lm31_append,shift_m1,shift_m1] at h1
  rw [lm31_append,lm31_append,shift_m2,shift_m2] at h2
  rw [lm31_append,lm31_append,shift_m3,shift_m3] at h3
  rw [lm31_append,lm31_append,shift_m4,shift_m4] at h4
  simp only [lm31_cast_m1,hE,hT] at h1
  simp only [lm31_cast_m1,lm31_cast_m2,hE,hT] at h2
  simp only [lm31_cast_m1,lm31_cast_m2,lm31_cast_m3] at h3
  simp only [lm31_cast_m1,lm31_cast_m2,lm31_cast_m3,lm31_cast_m4] at h4
  apply phaseMomentVeto31_excludes (momentsRaw31 D) (momentsRaw31 E) (momentsRaw31 T) x y hV
  · linear_combination h1
  · linear_combination h2
  · simpa only [thirdPoly31,momentsRaw31] using h3
  · simpa only [fourthPoly31,momentsRaw31] using h4

/-- The kernel-verified cells forbid a literal normalized phase cover at
each of the 35 roster records and all choices of six reflection signs. -/
theorem literal_roster_phase_exclusion (B : SixSupports31) (hB : B∈phasePairs31)
    (D E T : List Nat)
    (hd : D∈signVariants31 B.a0 B.b0)
    (he : E∈signVariants31 B.a1 B.b1)
    (ht : T∈signVariants31 B.a2 B.b2)
    (hD : ∀ a∈D,a<31) (hE : E.length=15) (hT : T.length=10)
    (x y : Nat) :
    isCover31 (D++shifted31 E x++shifted31 T y)=false := by
  have hm := roster_root_replay31
  rw [roster_literal_moments31] at hm
  have hMb : pairMoments31 B∈phasePairs31.map pairMoments31 :=
    List.mem_map.mpr ⟨_,hB,rfl⟩
  have hc := List.all_eq_true.mp hm _ hMb
  have hmD : momentsRaw31 D∈momentSignChoices31 B.a0 B.b0 :=
    List.mem_map.mpr ⟨D,hd,rfl⟩
  have hmE : momentsRaw31 E∈momentSignChoices31 B.a1 B.b1 :=
    List.mem_map.mpr ⟨E,he,rfl⟩
  have hmT : momentsRaw31 T∈momentSignChoices31 B.a2 B.b2 :=
    List.mem_map.mpr ⟨T,ht,rfl⟩
  have hEx := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc _ hmD) _ hmE) _ hmT
  cases h : isCover31 (D++shifted31 E x++shifted31 T y)
  · rfl
  · exact False.elim (actual_list_cover_disagrees_with_moment_veto D E T x y hD hE hT hEx h)

end Symconf93

#print axioms Symconf93.literal_roster_phase_exclusion
