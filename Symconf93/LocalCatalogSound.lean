module
public import Symconf93.LocalCatalogBase
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Bits

@[expose] public section

namespace Symconf93

theorem supportCode31_char (S : List Nat) (k : Nat) :
    (supportCode31 S).testBit k=true ↔ k∈S := by
  induction S with
  | nil => simp [supportCode31]
  | cons x xs ih =>
    change (((1<<<x) ||| supportCode31 xs).testBit k=true) ↔ k∈x::xs
    have hh : (1<<<x : Nat).testBit k=true ↔ k=x := by
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · rintro ⟨h₁,h₂⟩
        omega
      · intro he
        subst k
        exact ⟨le_rfl,Nat.sub_self _⟩
    rw [Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,hh]

theorem equal_support_of_code31 {S T : List Nat} (h : supportCode31 S=supportCode31 T) :
    ∀ k, k∈S ↔ k∈T := by
  intro k
  rw [← supportCode31_char,← supportCode31_char,h]

theorem normalizedList31_complete (k u : Nat) (T : List Nat)
    (hS : T.SortedLE) (hN : T.Nodup) (hK : T.length=k-2)
    (hb : ∀ x∈T, u<x ∧ x<31) : (0::u::T)∈normalizedFirst31 k u := by
  unfold normalizedFirst31
  apply List.mem_map.mpr
  refine ⟨T,List.mem_sublistsLen.mpr ⟨?_,hK⟩,rfl⟩
  apply List.sublist_of_subperm_of_sortedLE
  · exact List.subperm_of_subset hN (fun x hx => by
      have h := hb x hx
      rw [List.mem_range'_1]
      omega)
  · exact hS
  · exact List.sortedLE_range' _ _ _

/-- Derived finite-coverage meaning, with exact translations and reflection,
not merely a catalog signature match. -/
theorem local_coverage31_sound {P : List (List Nat)} {k u : Nat} {S : List Nat}
    (h : coverage31At P k u=true) (hS : S∈normalizedFirst31 k u)
    (hv : validLocal31 S=true) :
    ∃ T∈P, ∃ e : Bool, ∃ t<31, ∀ x,
      x∈S ↔ x∈translateReflect31 T e t := by
  have hm := List.all_eq_true.mp h S hS
  simp only [hv,Bool.not_true,Bool.false_or] at hm
  have hc := List.contains_iff_mem.mp hm
  obtain ⟨W,hW,hcw⟩ := List.mem_map.mp hc
  obtain ⟨T,hT,hwt⟩ := List.mem_flatMap.mp hW
  obtain ⟨e,_,hew⟩ := List.mem_flatMap.mp hwt
  obtain ⟨t,ht,hv⟩ := List.mem_filterMap.mp hew
  have heq : translateReflect31 T e t=W := by
    change (if (translateReflect31 T e t).contains 0 then some (translateReflect31 T e t)
      else none)=some W at hv
    split at hv
    · exact Option.some.inj hv
    · contradiction
  exact ⟨T,hT,e,t,List.mem_range.mp ht,
    equal_support_of_code31 (hcw.symm.trans (congrArg supportCode31 heq).symm)⟩

end Symconf93

#print axioms Symconf93.local_coverage31_sound
