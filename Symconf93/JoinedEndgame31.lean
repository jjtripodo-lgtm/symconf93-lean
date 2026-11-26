module
public import Symconf93.ActualSmallOrbits31
public import Symconf93.NativeMaskProof31
public import Symconf93.LiteralModelObstruction31
public import Symconf93.Terminal93
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Every original physical incidence constraint is joined in the 31-cubed
endgame, with only the raw degree-five local coverage test as premise. -/
namespace Symconf93
open scoped BigOperators

private theorem fin3_cases (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by fin_cases j <;> decide

private theorem native_upper31 (f : Fin 3→Z31→ℤ) (hb : ∀ j z,f j z=0∨f j z=1)
    (hN : ∀ d : Z31,d≠0 → (∑ j,cycleAuto31 (f j) d)=nativeRequired31 d)
    (j : Fin 3) (d : Z31) (hd : d≠0) : cycleAuto31 (f j) d≤nativeRequired31 d := by
  rw [← hN d hd]
  exact Finset.single_le_sum (s:=Finset.univ) (f:=fun k=>cycleAuto31 (f k) d)
    (fun k _=>cycleAuto31_nonnegative (f k) (hb k) d) (Finset.mem_univ j)

private theorem auto_one_zero31 (f : Fin 3→Z31→ℤ) (hb : ∀ j z,f j z=0∨f j z=1)
    (hN : ∀ d : Z31,d≠0 → (∑ j,cycleAuto31 (f j) d)=nativeRequired31 d)
    (j : Fin 3) : cycleAuto31 (f j) 1=0 := by
  have h := native_upper31 f hb hN j 1 (by decide)
  have hz := cycleAuto31_nonnegative (f j) (hb j) 1
  rw [show nativeRequired31 1=0 by decide] at h
  exact le_antisymm h hz

private def OrbitReal31 (f : Z31→ℤ) (T : List Nat) (e : Bool) (s : Z31) : Prop :=
  ∀ z, f z=1 ↔ ∃ x∈supportReflect31 e T, z=(x:Z31)+s

private theorem realRowFamily31 (f : Fin 3→Z31→ℤ) (hb : ∀ j z,f j z=0∨f j z=1)
    (hN : ∀ d : Z31,d≠0 → (∑ j,cycleAuto31 (f j) d)=nativeRequired31 d)
    {A B C : List Nat} (a : A∈proto2) (b : B∈proto3) (c : C∈proto5)
    {e₀ e₁ e₂ : Bool} {s₀ s₁ s₂ : Z31}
    (r₀ : OrbitReal31 (f 0) A e₀ s₀) (r₁ : OrbitReal31 (f 1) B e₁ s₁)
    (r₂ : OrbitReal31 (f 2) C e₂ s₂) : (A,B,C)∈allFamilies31 := by
  refine known_prototypes_join_31 a b c ?_
  let T : Fin 3→List Nat := ![A,B,C]
  let n : Fin 3→Nat := ![1,3,10]
  have hg : ∀ j,GoodProto31 (T j) (n j) := by
    intro j
    rcases fin3_cases j with rfl|rfl|rfl
    · exact good_proto2 A a
    · exact good_proto3 B b
    · exact good_proto5 C c
  have hp (j : Fin 3) (d : Nat) (hd : d∈unsignedGaps31 (T j)) : 1≤cycleAuto31 (f j) (d:Z31) := by
    rcases fin3_cases j with rfl|rfl|rfl
    · exact prototype_gap_pays_actual_auto _ (hb 0) A 1 (good_proto2 A a) e₀ s₀
        (fun z=> (r₀ z).mpr) d hd
    · exact prototype_gap_pays_actual_auto _ (hb 1) B 3 (good_proto3 B b) e₁ s₁
        (fun z=> (r₁ z).mpr) d hd
    · exact prototype_gap_pays_actual_auto _ (hb 2) C 10 (good_proto5 C c) e₂ s₂
        (fun z=> (r₂ z).mpr) d hd
  exact all_native_masks_join31 f T n hg (by decide) hb hN hp

private theorem physicalColumnDisjoint31 (X : FixedBanks31) (j : Fin 3)
    {A B : List Nat} {a b : Nat} (hA : GoodProto31 A a) (hB : GoodProto31 B b)
    {e f : Bool} {s t : Z31}
    (r₀ : OrbitReal31 (X.f j) A e s) (r₁ : OrbitReal31 (X.g j) B f t) :
    gapCode31 A &&& gapCode31 B=0 := by
  apply code_disjoint31
  intro d hdA hdB
  have h0 := (native_regular_shift31 d (hA.gaps_range d hdA)).1
  have h1 := X.commonColumn j (d:Z31) h0
  have h2 := prototype_gap_pays_actual_auto _ (X.binary_f j) A a hA e s
    (fun z=> (r₀ z).mpr) d hdA
  have h3 := prototype_gap_pays_actual_auto _ (X.binary_g j) B b hB f t
    (fun z=> (r₁ z).mpr) d hdB
  linarith only [h1,h2,h3]

theorem no_fixed_banks31_of_degree5_coverage
    (h5 : ∀ u : Fin 31, 0<u.val → coverage31At proto5 5 u.val=true)
    (X : FixedBanks31) : False := by
  have fN (j : Fin 3) (d : Z31) (hd : d≠0) : cycleAuto31 (X.f j) d≤1 :=
    (native_upper31 X.f X.binary_f X.native_f j d hd).trans (by unfold nativeRequired31; split <;> decide)
  have gN (j : Fin 3) (d : Z31) (hd : d≠0) : cycleAuto31 (X.g j) d≤1 :=
    (native_upper31 X.g X.binary_g X.native_g j d hd).trans (by unfold nativeRequired31; split <;> decide)
  have f0 := auto_one_zero31 X.f X.binary_f X.native_f
  have g0 := auto_one_zero31 X.g X.binary_g X.native_g
  have fH := X.exact_f
  have gH := X.exact_g
  obtain ⟨A,a,ea,sa,ra⟩ := actual_degree2_orbit31 (X.f 0) (X.binary_f 0) (fH 0) (fN 0) (f0 0)
  obtain ⟨B,b,eb,sb,rb⟩ := actual_degree3_orbit31 (X.f 1) (X.binary_f 1) (fH 1) (fN 1) (f0 1)
  obtain ⟨C,c,ec,sc,rc⟩ := actual_block_signed_orbit31 proto5 5 h5
    (X.f 2) (X.binary_f 2) (by decide) (fH 2) (fN 2) (f0 2)
  obtain ⟨D,d,ed,sd,rd⟩ := actual_degree2_orbit31 (X.g 2) (X.binary_g 2) (gH 2) (gN 2) (g0 2)
  obtain ⟨E,e,ee,se,re⟩ := actual_degree3_orbit31 (X.g 0) (X.binary_g 0) (gH 0) (gN 0) (g0 0)
  obtain ⟨F,f,ef,sf,rf⟩ := actual_block_signed_orbit31 proto5 5 h5
    (X.g 1) (X.binary_g 1) (by decide) (gH 1) (gN 1) (g0 1)
  have hf := realRowFamily31 X.f X.binary_f X.native_f a b c ra rb rc
  let G : Fin 3→Z31→ℤ := ![X.g 2,X.g 0,X.g 1]
  have hG j z : G j z=0 ∨ G j z=1 := by
    rcases fin3_cases j with rfl|rfl|rfl
    · exact X.binary_g 2 z
    · exact X.binary_g 0 z
    · exact X.binary_g 1 z
  have hGN (t : Z31) (ht : t≠0) : (∑ j,cycleAuto31 (G j) t)=nativeRequired31 t := by
    have hs := X.native_g t ht
    rw [Fin.sum_univ_three] at hs ⊢
    change cycleAuto31 (X.g 2) t+cycleAuto31 (X.g 0) t+cycleAuto31 (X.g 1) t=nativeRequired31 t
    linarith only [hs]
  have hg := realRowFamily31 G hG hGN d e f rd re rf
  have h0 := physicalColumnDisjoint31 X 0 (good_proto2 A a) (good_proto3 E e) ra re
  have h1 := physicalColumnDisjoint31 X 1 (good_proto3 B b) (good_proto5 F f) rb rf
  have h2 := physicalColumnDisjoint31 X 2 (good_proto5 C c) (good_proto2 D d) rc rd
  have hpair : pairCompatible31 (A,B,C) (D,E,F)=true := by
    simp [pairCompatible31,h0,h1,h2]
  have hm := fixed_families_give_roster31 hf hg hpair
  obtain ⟨P,hP,hE⟩ := List.mem_map.mp (show [A,E,B,F,C,D]∈projectedRoster31 from hm)
  have heq : P.a0=A ∧ P.b0=E ∧ P.a1=B ∧ P.b1=F ∧ P.a2=C ∧ P.b2=D := by
    simpa only [List.cons.injEq,and_true] using hE
  obtain ⟨ha,he,hb,hf',hc,hd⟩ := heq
  apply no_fixed_banks_with_literal_roster_supports X P hP ![ea,eb,ec] ![ee,ef,ed] ![sa,sb,sc] ![se,sf,sd]
  · intro j z hz
    rcases fin3_cases j with rfl|rfl|rfl
    · change ∃ x∈supportReflect31 ea P.a0,z=(x:Z31)+sa
      rw [ha]
      exact (ra z).mp hz
    · change ∃ x∈supportReflect31 eb P.a1,z=(x:Z31)+sb
      rw [hb]
      exact (rb z).mp hz
    · change ∃ x∈supportReflect31 ec P.a2,z=(x:Z31)+sc
      rw [hc]
      exact (rc z).mp hz
  · intro j z hz
    rcases fin3_cases j with rfl|rfl|rfl
    · change ∃ x∈supportReflect31 ee P.b0,z=(x:Z31)+se
      rw [he]
      exact (re z).mp hz
    · change ∃ x∈supportReflect31 ef P.b1,z=(x:Z31)+sf
      rw [hf']
      exact (rf z).mp hz
    · change ∃ x∈supportReflect31 ed P.b2,z=(x:Z31)+sd
      rw [hd]
      exact (rd z).mp hz

/-- This exact endgame interface has one discrete degree-five local test,
not assumptions about abstract profiles or physical support membership. -/
theorem phaseEndgame93_of_degree5_cells
    (h5 : ∀ u : Fin 31, 0<u.val →
      coveredBucket31 (chosenBucket31 witnessBuckets5 u.val) 5 u.val=true) : PhaseEndgame93 := by
  rintro ⟨X⟩
  obtain ⟨Y⟩ := normalize_physical_banks31 X
  exact no_fixed_banks31_of_degree5_coverage (local5_coverage_verified_of_cells h5) Y

end Symconf93

#print axioms Symconf93.no_fixed_banks31_of_degree5_coverage
#print axioms Symconf93.phaseEndgame93_of_degree5_cells
