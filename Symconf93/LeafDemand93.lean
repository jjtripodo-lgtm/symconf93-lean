module
public import Symconf93.CompactCoverage93

@[expose] public section

/-! Proper shifts can be checked on the positive column-length multiset.
Each selected column with gcd(a,b) dividing a proper shift costs at least
one in that shift. This avoids an exponentially repeated zero/positive
depth search among physically equal columns in some final profiles. -/
namespace Symconf93
open scoped List

def periodUses93 (a d : Nat) (D : List Nat) : Nat :=
  (D.filter (fun b=>decide (Nat.gcd a b∣d))).length

private theorem witness_positive_period93 {a : Nat} (ha : 0<a) {P : List Nat}
    {s q : Nat} {cap : Nat→Nat} (h : RowWitness a P s q cap)
    (hmax : ∀ d,cap d≤1) (hP : ∀ b∈P,3≤b ∧ b≤93 ∧ b≠4) :
    ∃ L : List PositiveOption93, (∀ o∈L,o∈rowOptions93 a) ∧
      (L.map PositiveOption93.u).sum=s ∧ (L.map PositiveOption93.cost).sum=q ∧
      L.map PositiveOption93.b <+ P ∧
      ∀ d,0<d → d<a → periodUses93 a d (L.map PositiveOption93.b)≤cap d := by
  induction h with
  | nil => exact ⟨[],by simp [periodUses93]⟩
  | cons b P u v s q cap hb hu hv hEq hPeriod _ ih =>
    obtain ⟨L,hL,hs,hq,hsub,hOcc⟩ := ih
      (fun d=>(Nat.sub_le _ _).trans (hmax d))
      (fun c hc=>hP c (List.mem_cons_of_mem _ hc))
    by_cases hu0 : u=0
    · refine ⟨L,hL,by simpa only [hu0,zero_add] using hs,
        by simpa only [hu0,zero_mul,zero_add] using hq,hsub.cons _,?_⟩
      exact fun d hd hda=>(hOcc d hd hda).trans (Nat.sub_le _ _)
    · let o : PositiveOption93 := ⟨b,u,v⟩
      have hv0 : 1≤v := by
        by_contra hn
        have hz : v=0 := by omega
        exact (Nat.ne_of_gt (Nat.mul_pos ha (Nat.pos_of_ne_zero hu0))) (by simpa [hz] using hEq)
      have hper : a∣b ∨ u≤1 := by
        by_cases hdiv : a∣b
        · exact Or.inl hdiv
        · have hG : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
          have hGa : Nat.gcd a b<a := by
            by_contra! hh
            have ht := Nat.le_antisymm (Nat.gcd_le_left b ha) hh
            exact hdiv (by simpa only [ht] using Nat.gcd_dvd_right a b)
          have hh := hPeriod _ hG hGa
          simp only [expenditure,dvd_refl,if_true] at hh
          exact Or.inr (hh.trans (hmax _))
      have hO : o∈rowOptions93 a := rowOptions93_iff.mpr
        ⟨(hP b (by simp)).1,(hP b (by simp)).2.1,(hP b (by simp)).2.2,
          Nat.pos_of_ne_zero hu0,hu,hv0,hv,hEq,hper⟩
      refine ⟨o::L,?_ ,?_ ,?_ ,hsub.cons_cons _,?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl|hm
        · exact hO
        · exact hL x hm
      · simp [o,hs]
      · simp [o,PositiveOption93.cost,hq]
      · intro d hd hda
        have hh := hOcc d hd hda
        have hX := hPeriod d hd hda
        by_cases hg : Nat.gcd a b∣d
        · have hG : decide (Nat.gcd a b∣d)=true := decide_eq_true_eq.mpr hg
          simp only [expenditure,hg,if_true] at hh hX
          simp only [periodUses93,List.map_cons,o,List.filter_cons,hG,if_true,List.length_cons]
          unfold periodUses93 at hh
          omega
        · have hG : decide (Nat.gcd a b∣d)=false := decide_eq_false_iff_not.mpr hg
          simp only [expenditure,if_neg hg,Nat.sub_zero] at hh
          simp only [periodUses93,List.map_cons,o,List.filter_cons,hG,Bool.false_eq_true,if_false]
          exact hh

def weakDemandFits93 (a : Nat) (D P : List Nat) : Bool :=
  demandFits93 D P 0 0 &&
    (List.range a).all (fun d=>d==0 || decide (periodUses93 a d D≤1))

theorem passing_weak_supported_demand93 {a : Nat} {P : List Nat}
    (ha : 0<a) (hS : rowSieve93 a P 10 (a+7) (fun _=>1)=true)
    (hP : ∀ b∈P,3≤b ∧ b≤93 ∧ b≠4) :
    ∃ D∈rowDemand93 a, weakDemandFits93 a D P=true := by
  obtain ⟨L,hL,hs,hq,hsub,hO⟩ :=
    witness_positive_period93 ha (rowSieve93_sound hS) (fun _=>le_rfl) hP
  have hp (o : PositiveOption93) (ho : o∈rowOptions93 a) : 1≤o.u ∧ 1≤o.v := by
    have hh := rowOptions93_iff.mp ho
    exact ⟨hh.2.2.2.1,hh.2.2.2.2.2.1⟩
  obtain ⟨D,hD,hP'⟩ := demandEnum93_complete (rowOptions93 a) L 10 (a+7)
    (rowOptions93_sorted a) hp hL hs hq
  refine ⟨D,hD,?_⟩
  have hIn : D <+~ (P++[]) := by simpa using hP'.subperm.trans hsub.subperm
  have hFit := demand_fits_actual_tail93 (hi:=0) hIn (show ([] : List Nat).sum=0 by rfl)
    (by simp)
  unfold weakDemandFits93
  rw [Bool.and_eq_true]
  refine ⟨hFit,List.all_eq_true.mpr ?_⟩
  intro d hd
  by_cases hz : d=0
  · simp [hz]
  · have hEq : periodUses93 a d D=periodUses93 a d (L.map PositiveOption93.b) :=
      (hP'.filter _).length_eq
    have hPay := hO d (Nat.pos_of_ne_zero hz) (List.mem_range.mp hd)
    simp [hEq,hPay]

theorem node_no_weak_demand93 {P : List Nat} {hi : Nat} (a : Nat) (D : List (List Nat))
    (hKnown : rowDemand93 a=D) (ha : a∈P) (hm : ∀ b∈P,3≤b ∧ b≤93 ∧ b≠4)
    (hBad : D.all (fun d=>!(weakDemandFits93 a d P))=true) :
    NodeCoverage93 P hi 0 := by
  apply node_bad_leaf93 a ha
  cases hS : rowSieve93 a P 10 (a+7) (fun _=>1)
  · rfl
  · have ha0 : 0<a := lt_of_lt_of_le (by decide : 0<3) (hm a ha).1
    obtain ⟨d,hd,hFit⟩ := passing_weak_supported_demand93 ha0 hS hm
    rw [hKnown] at hd
    have hNo := List.all_eq_true.mp hBad d hd
    rw [hFit] at hNo
    contradiction

end Symconf93

#print axioms Symconf93.passing_weak_supported_demand93
#print axioms Symconf93.node_no_weak_demand93
