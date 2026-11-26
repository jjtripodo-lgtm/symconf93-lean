module
public import Symconf93.DemandEnumerate93

@[expose] public section

/-! A proof-producing compact prefix cover. Prunes account for true
multiplicity and the exact total remaining size; a fork has an explicit
child proof for every legal next part, including all parity possibilities. -/
namespace Symconf93
open scoped List

def demandFits93 (D P : List Nat) (hi rem : Nat) : Bool :=
  let M := D.diff P
  decide (M.sum≤rem) && M.all (fun b=>decide (b≤hi))

/-- If the full match obtains, missing required columns are a submultiset
of the real tail, not reusable free options. -/
theorem demand_fits_actual_tail93 {D P T : List Nat} {hi rem : Nat}
    (hD : D <+~ (P++T)) (hs : T.sum=rem) (hT : ∀ b∈T,b≤hi) :
    demandFits93 D P hi rem=true := by
  have hM : D.diff P <+~ T := by
    apply List.subperm_iff_count.mpr
    intro b
    have h := (List.subperm_iff_count.mp hD) b
    rw [List.count_append] at h
    rw [List.count_diff]
    omega
  obtain ⟨W,hW,hsub⟩ := hM
  have hS := hW.sum_eq
  have hL := hsub.sum_le_sum (fun x _=>Nat.zero_le x)
  have hm : (D.diff P).sum≤rem := hS ▸ hs ▸ hL
  unfold demandFits93
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true_eq.mpr hm, List.all_eq_true.mpr (fun b hb=>
    decide_eq_true_eq.mpr (hT b (hsub.subset (hW.mem_iff.mpr hb))))⟩

def NodeCoverage93 (P : List Nat) (hi rem : Nat) : Prop :=
  ∀ T : List Nat, P.sum+rem=93 → T.sum=rem → T.Pairwise (·≥·) →
    (∀ b∈T,3≤b ∧ b≤hi) → profileSieve93 (P++T)=true → P++T∈profiles37

/-- The bank equality is checked independently against literal exhaustive
demand enumeration; a false/omitted hint cannot justify a prune. -/
theorem demand_node_prune93 {P : List Nat} {hi rem : Nat} (a : Nat)
    (D : List (List Nat)) (hKnown : rowDemand93 a=D)
    (ha : a∈P) (hMin : ∀ b∈P,3≤b) (hBad : D.all (fun d=>!(demandFits93 d P hi rem))=true) :
    NodeCoverage93 P hi rem := by
  intro T hSum hRem _ hB hPass
  have hAll : (P++T).sum=93 := by simpa only [List.sum_append,hRem] using hSum
  have h4 := passing_profile_no_four93 hPass
  have hBounds (b : Nat) (hb : b∈P++T) : b≤93 :=
    hAll ▸ Symconf59.member_le_sum hb
  have hLower (b : Nat) (hb : b∈P++T) : 3≤b := by
    rcases List.mem_append.mp hb with h|h
    · exact hMin b h
    · exact (hB b h).1
  have ha' : a∈P++T := List.mem_append_left T ha
  have ha0 : 0<a := lt_of_lt_of_le (by decide : 0<3) (hMin a ha)
  have hLoose := passing_profile_row_loose93 ha' ha0 hPass
  obtain ⟨d,hd,hpm⟩ := rowDemand93_complete ha0 hLoose
    (fun b hb=>⟨hLower b hb,hBounds b hb,fun he=>h4 (he ▸ hb)⟩)
  rw [hKnown] at hd
  have hNo := List.all_eq_true.mp hBad d hd
  rw [demand_fits_actual_tail93 hpm hRem (fun b hb=>(hB b hb).2)] at hNo
  contradiction

inductive ChildrenCoverage93 (P : List Nat) (rem : Nat) : List Nat → Prop where
  | nil : ChildrenCoverage93 P rem []
  | cons (b : Nat) (B : List Nat) :
    NodeCoverage93 (P++[b]) b (rem-b) → ChildrenCoverage93 P rem B →
      ChildrenCoverage93 P rem (b::B)

theorem childrenCoverage93_apply {P : List Nat} {rem : Nat} {B : List Nat}
    (h : ChildrenCoverage93 P rem B) {b : Nat} (hb : b∈B) :
    NodeCoverage93 (P++[b]) b (rem-b) := by
  induction h with
  | nil => simp at hb
  | cons x B h H ih =>
    rcases List.mem_cons.mp hb with rfl|hm
    · exact h
    · exact ih hm

def legalChildren93 (hi rem : Nat) : List Nat :=
  ((List.range (min hi rem+1)).filter (fun b=>decide (3≤b ∧ b≠4 ∧
    rem-b≠1 ∧ rem-b≠2))).reverse

theorem node_fork93 {P : List Nat} {hi rem : Nat} {B : List Nat}
    (hR : rem≠0) (hExact : legalChildren93 hi rem=B)
    (hC : ChildrenCoverage93 P rem B) : NodeCoverage93 P hi rem := by
  intro T hs hT hOrd hBound hValid
  cases T with
  | nil => simp at hT; exact (hR hT.symm).elim
  | cons b T =>
    have hb := hBound b (by simp)
    have hsT : b+T.sum=rem := hT
    have hs' : T.sum=rem-b := by omega
    have hb4 : b≠4 := by
      rintro rfl
      exact passing_profile_no_four93 hValid (List.mem_append_right P (by simp))
    have hn (n : Nat) (hn : n=1 ∨ n=2) : rem-b≠n := by
      intro he
      cases T with
      | nil => simp at hs'; omega
      | cons c V =>
        have hh := hBound c (by simp)
        simp only [List.sum_cons] at hs'
        omega
    have hm : b∈B := by
      rw [←hExact,legalChildren93,List.mem_reverse,List.mem_filter,List.mem_range,decide_eq_true_eq]
      refine ⟨?_ ,hb.1,hb4,hn 1 (Or.inl rfl),hn 2 (Or.inr rfl)⟩
      exact Nat.lt_succ_of_le (Nat.le_min.mpr ⟨hb.2,by omega⟩)
    have hc := childrenCoverage93_apply hC hm
    have hApp : (P++[b])++T=P++(b::T) := by simp
    rw [←hApp] at hValid ⊢
    apply hc T _ hs' (List.pairwise_cons.mp hOrd).2
      (fun c hc=>⟨(hBound c (List.mem_cons_of_mem _ hc)).1,(List.pairwise_cons.mp hOrd).1 c hc⟩) hValid
    simp only [List.sum_append,List.sum_cons,List.sum_nil]
    omega

theorem node_leaf93 {P : List Nat} {hi : Nat}
    (h : profileSieve93 P=true → P∈profiles37) : NodeCoverage93 P hi 0 := by
  intro T _ hT _ hb hv
  have hz : T=[] := by
    cases T with
    | nil => rfl
    | cons b T =>
      have hh := hb b (by simp)
      simp only [List.sum_cons] at hT
      omega
  subst T
  simpa using h (by simpa using hv)

theorem node_good_leaf93 {P : List Nat} {hi : Nat} (h : P∈profiles37) :
    NodeCoverage93 P hi 0 :=
  node_leaf93 (fun _=>h)

theorem node_bad_leaf93 {P : List Nat} {hi : Nat} (a : Nat)
    (ha : a∈P) (h : rowSieve93 a P 10 (a+7) (fun _=>1)=false) : NodeCoverage93 P hi 0 := by
  apply node_leaf93
  intro hSieve
  unfold profileSieve93 at hSieve
  simp only [Bool.and_eq_true] at hSieve
  have hh := List.all_eq_true.mp hSieve.2 a ha
  rw [h] at hh
  contradiction

theorem coverage93_of_root (h : NodeCoverage93 [] 93 93) : Coverage93 := by
  intro P hp hv
  have hP := partitionLists_sound93 hp
  exact h P (by decide) hP.1 hP.2.1 hP.2.2 hv

end Symconf93

#print axioms Symconf93.demand_fits_actual_tail93
#print axioms Symconf93.demand_node_prune93
#print axioms Symconf93.node_fork93
#print axioms Symconf93.coverage93_of_root
