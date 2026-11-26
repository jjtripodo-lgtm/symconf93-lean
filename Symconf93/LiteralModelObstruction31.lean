module
public import Symconf93.RawPrototypeCover31

@[expose] public section

/-! The original normalized fixed-bank data cannot be realized by any of
the 35 rigorously joined signed prototype-pair records, with arbitrary
individual shifts. Coverage of all actual lists is separate. -/
namespace Symconf93

def leftPrototype31 (T : SixSupports31) (j : Fin 3) : List Nat :=
  if j=0 then T.a0 else if j=1 then T.a1 else T.a2

def rightPrototype31 (T : SixSupports31) (j : Fin 3) : List Nat :=
  if j=0 then T.b0 else if j=1 then T.b1 else T.b2

private theorem signchoice_mem (A B : List Nat) (e f : Bool) :
    rawDiff31 (supportReflect31 e A) (supportReflect31 f B)∈signVariants31 A B := by
  apply List.mem_flatMap.mpr
  refine ⟨e,(by cases e <;> simp),?_⟩
  exact List.mem_map.mpr ⟨f,(by cases f <;> simp),rfl⟩

private theorem support_sign_len (T : List Nat) (e : Bool) :
    (supportReflect31 e T).length=T.length := by cases e <;> simp [supportReflect31]

theorem no_fixed_banks_with_literal_roster_supports
    (X : FixedBanks31) (P : SixSupports31) (hP : P∈phasePairs31)
    (e f : Fin 3→Bool) (a b : Fin 3→Z31)
    (hLeft : ∀ j z, X.f j z=1 →
      ∃ x∈supportReflect31 (e j) (leftPrototype31 P j), z=(x:Z31)+a j)
    (hRight : ∀ j z, X.g j z=1 →
      ∃ x∈supportReflect31 (f j) (rightPrototype31 P j), z=(x:Z31)+b j) : False := by
  let A j := supportReflect31 (e j) (leftPrototype31 P j)
  let B j := supportReflect31 (f j) (rightPrototype31 P j)
  have H : phasePairs31.all (fun P => decide (
    (∀ x∈P.a0,x<31) ∧ (∀ x∈P.a1,x<31) ∧ (∀ x∈P.a2,x<31) ∧
    P.a0.length=2 ∧ P.b0.length=3 ∧ P.a1.length=3 ∧ P.b1.length=5 ∧
    P.a2.length=5 ∧ P.b2.length=2))=true := by decide +kernel
  obtain ⟨h0,h1,h2,l0,l1,l2,l3,l4,l5⟩ :=
    decide_eq_true_eq.mp (List.all_eq_true.mp H P hP)
  have hA (j : Fin 3) (x : Nat) (hx : x∈A j) : x<31 := by
    cases he : e j
    · fin_cases j
      · change e (0:Fin 3)=false at he
        change x ∈ supportReflect31 (e 0) P.a0 at hx
        rw [he] at hx
        exact h0 x hx
      · change e (1:Fin 3)=false at he
        change x ∈ supportReflect31 (e 1) P.a1 at hx
        rw [he] at hx
        exact h1 x hx
      · change e (2:Fin 3)=false at he
        change x ∈ supportReflect31 (e 2) P.a2 at hx
        rw [he] at hx
        exact h2 x hx
    · have hx' : x∈(leftPrototype31 P j).map (fun s=> (31-s)%31) := by
        simpa only [A,supportReflect31,he,if_true] using hx
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx'
      exact Nat.mod_lt _ (by decide)
  have hh : (A 0).length*(B 0).length+(A 1).length*(B 1).length+
      (A 2).length*(B 2).length=31 := by
    simp only [A,B,support_sign_len,leftPrototype31,rightPrototype31]
    simp [l0,l1,l2,l3,l4,l5]
  have hV := actual_banks_force_raw_cover31 X A B a b hA hLeft hRight hh
  dsimp only at hV
  have hn := no_literal_roster_phase_cover P hP
    (signchoice_mem P.a0 P.b0 (e 0) (f 0))
    (signchoice_mem P.a1 P.b1 (e 1) (f 1))
    (signchoice_mem P.a2 P.b2 (e 2) (f 2))
    ((b 1-a 1-(b 0-a 0)).val) ((b 2-a 2-(b 0-a 0)).val)
  have hc :
      isCover31 (rawDiff31 (A 0) (B 0) ++
        shifted31 (rawDiff31 (A 1) (B 1)) ((b 1-a 1-(b 0-a 0)).val) ++
        shifted31 (rawDiff31 (A 2) (B 2)) ((b 2-a 2-(b 0-a 0)).val))=false := by
    exact hn
  rw [hV] at hc
  contradiction

end Symconf93

#print axioms Symconf93.no_fixed_banks_with_literal_roster_supports
