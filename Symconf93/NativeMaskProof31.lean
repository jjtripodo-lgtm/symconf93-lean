module
public import Symconf93.ActualBlockOrbit31
public import Symconf93.RosterJoin31
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Link the literal prototype mask tests to actual original native and
shared-column overlaps. No appeal to equality of abstract signatures. -/
namespace Symconf93
open scoped BigOperators

structure GoodProto31 (T : List Nat) (n : Nat) : Prop where
  strict : T.Pairwise (·<·)
  bounded : ∀ a∈T,a<31
  gaps_nodup : (unsignedGaps31 T).Nodup
  gaps_range : ∀ d∈unsignedGaps31 T,2≤d ∧ d≤15
  gap_count : (unsignedGaps31 T).length=n

private def protoChecks31 (n : Nat) (T : List Nat) : Bool :=
  decide (T.Pairwise (·<·) ∧ (∀ a∈T, a<31) ∧
    (unsignedGaps31 T).Nodup ∧ (∀ d∈unsignedGaps31 T,2≤d ∧ d≤15) ∧
    (unsignedGaps31 T).length=n)

private theorem protoChecks31_sound (T : List Nat) (n : Nat) (h : protoChecks31 n T=true) :
    GoodProto31 T n := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := decide_eq_true_eq.mp h
  exact ⟨h₁,h₂,h₃,h₄,h₅⟩

theorem good_proto2 (T : List Nat) (h : T∈proto2) : GoodProto31 T 1 :=
  protoChecks31_sound T 1 (List.all_eq_true.mp (by decide +kernel) _ h)
theorem good_proto3 (T : List Nat) (h : T∈proto3) : GoodProto31 T 3 :=
  protoChecks31_sound T 3 (List.all_eq_true.mp (by decide +kernel) _ h)
theorem good_proto5 (T : List Nat) (h : T∈proto5) : GoodProto31 T 10 :=
  protoChecks31_sound T 10 (List.all_eq_true.mp (by decide +kernel) _ h)

private theorem gap_exists (T : List Nat) (hT : T.Pairwise (·<·)) (d : Nat)
    (hd : d∈unsignedGaps31 T) :
    ∃ a∈T, ∃ b∈T, a<b ∧ min (b-a) (31-(b-a))=d := by
  induction T with
  | nil => simp [unsignedGaps31] at hd
  | cons a S ih =>
    simp only [unsignedGaps31,List.mem_append,List.mem_map] at hd
    rcases hd with ⟨b,hb,hE⟩|hd
    · exact ⟨a,by simp,b,List.mem_cons_of_mem _ hb,
        (List.pairwise_cons.mp hT).1 _ hb,hE⟩
    · obtain ⟨x,hx,y,hy,hxy,he⟩ := ih (List.pairwise_cons.mp hT).2 hd
      exact ⟨x,List.mem_cons_of_mem _ hx,y,List.mem_cons_of_mem _ hy,hxy,he⟩

private theorem proto_gap_orientation {a b : Nat} (h : a<b) (hb : b<31)
    (d : Nat) (hgap : min (b-a) (31-(b-a))=d) :
    ((b:Z31)-(a:Z31)=(d:Z31)) ∨ ((a:Z31)-(b:Z31)=(d:Z31)) := by
  have hsub : ((b-a:Nat):Z31)=(b:Z31)-(a:Z31) := Nat.cast_sub (by omega)
  by_cases h0 : b-a≤31-(b-a)
  · rw [min_eq_left h0] at hgap
    exact Or.inl (hsub.symm.trans (congrArg (fun n:Nat=>(n:Z31)) hgap))
  · rw [min_eq_right (by omega)] at hgap
    right
    rw [←hgap,Nat.cast_sub (by omega),hsub,ZMod.natCast_self,zero_sub,neg_sub]

private def reflectOne31 (e : Bool) (a : Nat) : Nat :=
  if e then (31-a)%31 else a

private theorem reflectOne_mem (T : List Nat) (e : Bool) {a : Nat} (h : a∈T) :
    reflectOne31 e a∈supportReflect31 e T := by
  cases e
  · exact h
  · exact List.mem_map.mpr ⟨a,h,rfl⟩

private theorem reflectOne_cast {a : Nat} (ha : a<31) :
    (reflectOne31 true a:Z31)=-(a:Z31) := by
  unfold reflectOne31
  rw [if_pos rfl,ZMod.natCast_mod,Nat.cast_sub (by omega),ZMod.natCast_self,zero_sub]

/-- Every native token of a certified literal signed block is genuinely
paid by the actual within-cycle overlap at that residue. -/
theorem prototype_gap_pays_actual_auto
    (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1)
    (T : List Nat) (n : Nat) (hT : GoodProto31 T n)
    (e : Bool) (s : Z31)
    (hLift : ∀ z : Z31, (∃ x∈supportReflect31 e T,z=(x:Z31)+s)→f z=1)
    (d : Nat) (hd : d∈unsignedGaps31 T) : 1≤cycleAuto31 f (d:Z31) := by
  obtain ⟨a,ha,b,hb,hab,he⟩ := gap_exists T hT.strict d hd
  have hoa := proto_gap_orientation hab (hT.bounded b hb) d he
  have hx := hLift ((reflectOne31 e a:Z31)+s) ⟨_,reflectOne_mem T e ha,rfl⟩
  have hy := hLift ((reflectOne31 e b:Z31)+s) ⟨_,reflectOne_mem T e hb,rfl⟩
  let x := (reflectOne31 e a:Z31)+s
  let y := (reflectOne31 e b:Z31)+s
  have hx' : f x=1 := hx
  have hy' : f y=1 := hy
  have ho : y-x=(d:Z31) ∨ x-y=(d:Z31) := by
    have hx0 : x=(reflectOne31 e a:Z31)+s := rfl
    have hy0 : y=(reflectOne31 e b:Z31)+s := rfl
    rw [hx0,hy0,add_sub_add_right_eq_sub,add_sub_add_right_eq_sub]
    cases e
    · exact hoa
    · rw [reflectOne_cast (hT.bounded a ha),reflectOne_cast (hT.bounded b hb),
        neg_sub_neg,neg_sub_neg]
      exact Or.symm hoa
  have hn : (residuePairs31 f f (d:Z31)).Nonempty := by
    rcases ho with ho|ho
    · exact ⟨(x,y),by simp [residuePairs31,support31,hx',hy',ho]⟩
    · exact ⟨(y,x),by simp [residuePairs31,support31,hx',hy',ho]⟩
  have hc : 1≤(residuePairs31 f f (d:Z31)).card := Finset.card_pos.mpr hn
  unfold cycleAuto31
  rw [cycleCorr31_literal_pairs hf hf]
  exact_mod_cast hc

theorem cycleAuto31_nonnegative (f : Z31→ℤ) (hf : ∀ z, f z=0∨f z=1) (d : Z31) :
    0≤cycleAuto31 f d := by
  unfold cycleAuto31
  rw [cycleCorr31_literal_pairs hf hf]
  positivity

/-- Native allowed d pairs convert to the genuine nonspecial circle shifts. -/
theorem native_regular_shift31 (d : Nat) (hd : 2≤d ∧ d≤15) :
    (d:Z31)≠0 ∧ nativeRequired31 (d:Z31)=1 := by
  have h0 (k : Nat) (hk : k<31) (hn : d≠k) : (d:Z31)≠(k:Z31) := by
    intro he
    have hh := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt hk] at hh
    exact hn hh
  have hzero : (d:Z31)≠0 := h0 0 (by decide) (by omega)
  have hone : (d:Z31)≠1 := h0 1 (by decide) (by omega)
  have hneg : (d:Z31)≠-1 := by
    have hc : ((30:Nat):Z31)=(-1:Z31) := by decide
    rw [←hc]
    exact h0 30 (by decide) (by omega)
  exact ⟨hzero,by simp [nativeRequired31,hone,hneg]⟩

/-- Presence of a shared projected gap would pay twice at the original
column-shore overlap, which is impossible. -/
theorem code_disjoint31 (A B : List Nat)
    (h : ∀ d, d∈A → d∈B → False) :
    supportCode31 A &&& supportCode31 B=0 := by
  apply Nat.eq_of_testBit_eq
  intro d
  simp only [Nat.testBit_and]
  by_cases hh : (supportCode31 A).testBit d=true
  · have hB : (supportCode31 B).testBit d=false := by
      by_contra! hz
      exact h d ((supportCode31_char A d).mp hh)
        ((supportCode31_char B d).mp (Bool.eq_true_of_not_eq_false hz))
    simp [hh,hB]
  · have hA := Bool.eq_false_of_not_eq_true hh
    simp [hA]

end Symconf93

#print axioms Symconf93.prototype_gap_pays_actual_auto
#print axioms Symconf93.code_disjoint31

namespace Symconf93
open scoped BigOperators

theorem supportCode31_append (A B : List Nat) :
    supportCode31 (A++B)=supportCode31 A ||| supportCode31 B := by
  apply Nat.eq_of_testBit_eq
  intro d
  rw [Nat.testBit_or]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true,supportCode31_char,supportCode31_char,supportCode31_char,
    List.mem_append]

/-- Physical native row constraints imply the complete permitted mask
partition. Only the implication from literal gap to positive actual
overlap is needed; the converse follows from the 1+3+10 token count. -/
theorem all_native_masks_join31 (f : Fin 3→Z31→ℤ) (T : Fin 3→List Nat) (n : Fin 3→Nat)
    (hGood : ∀ j,GoodProto31 (T j) (n j)) (hn : n 0+n 1+n 2=14)
    (hBin : ∀ j z,f j z=0∨f j z=1)
    (hNative : ∀ d : Z31,d≠0 → (∑ j,cycleAuto31 (f j) d)=nativeRequired31 d)
    (hPays : ∀ j (d:Nat),d∈unsignedGaps31 (T j) → 1≤cycleAuto31 (f j) (d:Z31)) :
    rowMaskFits31 (gapCode31 (T 0)) (gapCode31 (T 1)) (gapCode31 (T 2))=true := by
  let G (j : Fin 3) := unsignedGaps31 (T j)
  have hD (j k : Fin 3) (hne : j≠k) : ∀ d,d∈G j → d∈G k → False := by
    intro d hj hk
    obtain ⟨h0,h1⟩ := native_regular_shift31 d ((hGood j).gaps_range d hj)
    have hh := hNative (d:Z31) h0
    rw [h1,Fin.sum_univ_three] at hh
    have hP := hPays j d hj
    have hQ := hPays k d hk
    have hN (i : Fin 3) := cycleAuto31_nonnegative (f i) (hBin i) (d:Z31)
    have hN0 := hN 0
    have hN1 := hN 1
    have hN2 := hN 2
    have hF (q : Fin 3) : q=0 ∨ q=1 ∨ q=2 := by fin_cases q <;> decide
    rcases hF j with rfl|rfl|rfl <;> rcases hF k with rfl|rfl|rfl <;>
      first | exact hne rfl | linarith only [hh,hP,hQ,hN0,hN1,hN2]
  have h01 := hD 0 1 (by decide)
  have h02 := hD 0 2 (by decide)
  have h12 := hD 1 2 (by decide)
  have hND : (G 0 ++ G 1 ++ G 2).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_,(hGood 2).gaps_nodup,?_⟩
    · exact List.nodup_append.mpr ⟨(hGood 0).gaps_nodup,(hGood 1).gaps_nodup,
        fun a ha b hb he => h01 a ha (he.symm ▸ hb)⟩
    · intro a ha b hb he
      subst b
      rcases List.mem_append.mp ha with hA|hB
      · exact h02 a hA hb
      · exact h12 a hB hb
  have hSub : List.Subperm (G 0 ++ G 1 ++ G 2) (List.range' 2 14) := by
    apply List.subperm_of_subset hND
    intro d hd
    have hr : 2≤d ∧ d≤15 := by
      rcases List.mem_append.mp hd with h|h
      · rcases List.mem_append.mp h with h0|h0
        · exact (hGood 0).gaps_range d h0
        · exact (hGood 1).gaps_range d h0
      · exact (hGood 2).gaps_range d h
    rw [List.mem_range'_1]
    omega
  obtain ⟨R,hp,hsub⟩ := hSub
  have hLen : R.length=14 := by
    rw [hp.length_eq,List.length_append,List.length_append]
    change (unsignedGaps31 (T 0)).length+
      (unsignedGaps31 (T 1)).length+(unsignedGaps31 (T 2)).length=14
    rw [(hGood 0).gap_count,(hGood 1).gap_count,(hGood 2).gap_count,hn]
  have hE : R=List.range' 2 14 := hsub.eq_of_length (by rw [hLen,List.length_range'])
  have hPerm : (G 0++G 1++G 2).Perm (List.range' 2 14) := hE ▸ hp.symm
  have hFull : supportCode31 (G 0++G 1++G 2)=supportCode31 (List.range' 2 14) := by
    apply Nat.eq_of_testBit_eq
    intro d
    apply Bool.eq_iff_iff.mpr
    simpa only [supportCode31_char] using hPerm.mem_iff
  rw [supportCode31_append,supportCode31_append] at hFull
  unfold rowMaskFits31 gapCode31 allNative31
  change ((supportCode31 (G 0) &&& supportCode31 (G 1))==0 &&
    (supportCode31 (G 0) &&& supportCode31 (G 2))==0 &&
    (supportCode31 (G 1) &&& supportCode31 (G 2))==0 &&
    ((supportCode31 (G 0) ||| supportCode31 (G 1)) ||| supportCode31 (G 2))==
      supportCode31 (List.range' 2 14))=true
  simp [code_disjoint31 _ _ h01,code_disjoint31 _ _ h02,code_disjoint31 _ _ h12,hFull]

end Symconf93

#print axioms Symconf93.all_native_masks_join31
