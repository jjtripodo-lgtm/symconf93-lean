module
public import Symconf93.TwoBankNormalize
public import Symconf93.PhaseRosterTerminal
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Exact actual fixed-bank mixed intersections force a complete natural
residue list after a harmless common shift. It suffices to witness every
residue, since the three raw lists have total length 31. -/
namespace Symconf93
open scoped BigOperators

private theorem raw_length31 (A B : List Nat) :
    (rawDiff31 A B).length=A.length*B.length := by
  induction A with
  | nil => simp [rawDiff31]
  | cons a T ih =>
    change (B.map (fun b => (31+b-a)%31) ++ rawDiff31 T B).length =
      (T.length+1)*B.length
    rw [List.length_append,List.length_map,ih,Nat.add_mul,one_mul,Nat.add_comm]

private theorem rawBound31 (A B : List Nat) (a : Nat) (ha : a∈rawDiff31 A B) :
    a<31 := by
  obtain ⟨b,_,h⟩ := List.mem_flatMap.mp ha
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp h
  exact Nat.mod_lt _ (by decide)

private theorem zero_raw_translation (A B : List Nat) :
    shifted31 (rawDiff31 A B) 0=rawDiff31 A B := by
  unfold shifted31
  calc
    _ = (rawDiff31 A B).map id := List.map_congr_left (fun d hd=>by
      change (d+0)%31=d
      rw [Nat.add_zero,Nat.mod_eq_of_lt (rawBound31 A B d hd)])
    _ = _ := List.map_id _

private theorem occurrence_gives_cover (C : List Nat)
    (hlen : C.length=31) (hall : ∀ d < 31, d∈C) : isCover31 C=true := by
  have hS : List.Subperm (List.range 31) C :=
    List.subperm_of_subset List.nodup_range (fun d hd => hall d (List.mem_range.mp hd))
  obtain ⟨W,hperm,hsub⟩ := hS
  have hW : W=C := hsub.eq_of_length (by rw [hperm.length_eq,List.length_range,hlen])
  subst W
  apply List.all_eq_true.mpr
  intro d hd
  have hD := List.mem_range.mp hd
  simp [List.perm_iff_count.mp hperm d,List.count_range,hD]

/-- If the supports of the two true physical banks are represented by the
given signed prototype lists and individual endpoint shifts, their three
physical cross-difference lists must cover the entire residue register. -/
theorem actual_banks_force_raw_cover31
    (X : FixedBanks31) (A B : Fin 3→List Nat) (a b : Fin 3→Z31)
    (ha : ∀ j x, x∈A j → x<31)
    (hLeft : ∀ j z, X.f j z=1 → ∃x∈A j, z=(x:Z31)+a j)
    (hRight : ∀ j z, X.g j z=1 → ∃y∈B j, z=(y:Z31)+b j)
    (hsize : (A 0).length*(B 0).length+(A 1).length*(B 1).length+
      (A 2).length*(B 2).length=31) :
    let lag := b 0-a 0
    let x := (b 1-a 1-lag).val
    let y := (b 2-a 2-lag).val
    isCover31 (rawDiff31 (A 0) (B 0) ++ shifted31 (rawDiff31 (A 1) (B 1)) x ++
      shifted31 (rawDiff31 (A 2) (B 2)) y)=true := by
  dsimp only
  apply occurrence_gives_cover
  · simp only [List.length_append,shifted31,List.length_map,raw_length31,hsize]
  · intro d hd
    let lag : Z31 := b 0-a 0
    let z0 : Z31 := (d:Z31)+lag
    have hfull := X.mixed_cover z0
    have hex : ∃ j : Fin 3, ∃ z : Z31, X.f j (z-z0)=1 ∧ X.g j z=1 := by
      by_contra! hnone
      have hz (j : Fin 3) (z : Z31) : X.f j (z-z0)*X.g j z=0 := by
        rcases X.binary_f j (z-z0) with h|h
        · simp [h]
        · rcases X.binary_g j z with hh|hh
          · simp [hh]
          · exact False.elim (hnone j z h hh)
      simp only [cycleCorr31,hz,Finset.sum_const_zero] at hfull
      omega
    obtain ⟨j,z,hf,hg⟩ := hex
    obtain ⟨p,hp,he⟩ := hLeft j (z-z0) hf
    obtain ⟨q,hq,hE⟩ := hRight j z hg
    let key : Nat := (31+q-p)%31
    have hKey : key∈rawDiff31 (A j) (B j) :=
      List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
    have hv : (key:Z31)=(q:Z31)-(p:Z31) := by
      dsimp only [key]
      have hh : p≤31+q := by have := ha j p hp; omega
      rw [ZMod.natCast_mod,Nat.cast_sub hh,Nat.cast_add,
        show ((31:Nat):Z31)=0 from ZMod.natCast_self 31,zero_add]
    let tj : Nat := (b j-a j-lag).val
    have hinc : ((key+tj)%31)∈shifted31 (rawDiff31 (A j) (B j)) tj :=
      List.mem_map.mpr ⟨key,hKey,rfl⟩
    have hD : ((key+tj)%31:Nat)=d := by
      have hf' : (((key+tj)%31:Nat):Z31)=(d:Z31) := by
        rw [ZMod.natCast_mod,Nat.cast_add,hv]
        dsimp only [tj]
        rw [ZMod.natCast_zmod_val]
        dsimp [z0] at he
        linear_combination he-hE
      have heq := congrArg ZMod.val hf'
      simpa only [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0<31)),
        ZMod.val_natCast_of_lt hd] using heq
    rw [hD] at hinc
    fin_cases j
    · change d∈shifted31 (rawDiff31 (A 0) (B 0)) ((b 0-a 0-lag).val) at hinc
      rw [show (b 0-a 0-lag).val=0 by simp [lag],zero_raw_translation] at hinc
      exact List.mem_append_left _ (List.mem_append_left _ hinc)
    · exact List.mem_append_left _ (List.mem_append_right _ hinc)
    · exact List.mem_append_right _ hinc

end Symconf93

#print axioms Symconf93.actual_banks_force_raw_cover31
