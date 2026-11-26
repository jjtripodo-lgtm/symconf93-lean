module
public import Symconf93.ProfileSieve93
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Sound compact prefix elimination. A future tail may be replaced by a
multiset overcount, and all new columns take degree zero. -/
namespace Symconf93
open scoped BigOperators List

/-- Structural witness corresponding to an actual original row's block
sums after normalizing its first and second moments by its length. -/
inductive LooseRow93 (a : ℕ) : List ℕ → ℕ → ℕ → Prop where
  | nil : LooseRow93 a [] 0 0
  | cons (b : ℕ) (P : List ℕ) (u v s q : ℕ) :
      0<b → u≤10 → v≤10 → a*u=b*v →
      (a∣b ∨ u≤1) → LooseRow93 a P s q →
      LooseRow93 a (b::P) (u+s) (u*v+q)

def rowLoose93 (a : ℕ) (P : List ℕ) (s q : ℕ) : Bool :=
  match P with
  | [] => decide (s=0 ∧ q=0)
  | b::P => (List.range (min s 10+1)).any (fun u =>
      let v := a*u/b
      decide (0<b ∧ a*u=b*v ∧ v≤10 ∧ u*v≤q ∧ (a∣b ∨ u≤1)) &&
        rowLoose93 a P (s-u) (q-u*v))

/-- A genuine local row never gets rejected by the fast bounded checker. -/
theorem rowLoose93_complete {a : ℕ} {P : List ℕ} {s q : ℕ}
    (h : LooseRow93 a P s q) : rowLoose93 a P s q=true := by
  induction h with
  | nil => rfl
  | cons b P u v s q hb hu hv hdiv hlocal htail ih =>
    have hV : a*u/b=v := by rw [hdiv,Nat.mul_comm,Nat.mul_div_cancel _ hb]
    rw [rowLoose93,List.any_eq_true]
    refine ⟨u,?_ ,?_⟩
    · rw [List.mem_range,Nat.lt_succ_iff,Nat.le_min]
      exact ⟨Nat.le_add_right _ _,hu⟩
    · simp only [hV,Bool.and_eq_true,decide_eq_true_eq,Nat.add_sub_cancel_left]
      exact ⟨⟨hb,hdiv,hv,Nat.le_add_right _ _,hlocal⟩,ih⟩

def relevant (a b : ℕ) : Bool := decide ((a∣b ∧ b/a≤10) ∨ (b∣a ∧ a/b≤10))

private theorem relevant_of_positive {a b u v : ℕ} (ha : 0<a) (hb : 0<b)
    (hu0 : u≠0) (hu : u≤10) (hv : v≤10) (he : a*u=b*v)
    (hlocal : a∣b ∨ u≤1) : relevant a b=true := by
  apply decide_eq_true_eq.mpr
  rcases hlocal with ht|ht
  · left
    refine ⟨ht,?_⟩
    obtain ⟨c,hc⟩ := ht
    have hd : u=c*v := Nat.eq_of_mul_eq_mul_left ha (by rwa [hc,Nat.mul_assoc] at he)
    have hv1 : 1≤v := by
      by_contra hn
      have hz : v=0 := by omega
      rw [hz,mul_zero] at hd
      exact hu0 hd
    have hh := Nat.mul_le_mul_left c hv1
    rw [mul_one] at hh
    rw [hc,Nat.mul_div_cancel_left _ ha]
    omega
  · right
    have h1 : u=1 := by omega
    rw [h1,mul_one] at he
    exact ⟨⟨v,he⟩,by rw [he,Nat.mul_div_cancel_left _ hb]; exact hv⟩

/-- Dropping all impossible column lengths loses no true row witness. -/
theorem localRow_filter_relevant {a : ℕ} (ha : 0<a) {P : List ℕ} {s q : ℕ}
    (h : LooseRow93 a P s q) : LooseRow93 a (P.filter (relevant a)) s q := by
  induction h with
  | nil => exact LooseRow93.nil
  | cons b P u v s q hb hu hv he hloc htail ih =>
    by_cases hr : relevant a b=true
    · simp only [List.filter_cons,hr,if_true]
      exact LooseRow93.cons b _ u v s q hb hu hv he hloc ih
    · have hz : u=0 := by
        by_contra hn
        exact hr (relevant_of_positive ha hb hn hu hv he hloc)
      simp only [List.filter_cons,hr,hz,zero_mul,zero_add]
      exact ih

theorem physical_row_to_loose {a : ℕ} {P : List ℕ} {s t : ℕ} {cap : ℕ → ℕ}
    (ha : 0<a) (h : RowWitness a P s t cap) (hcap : ∀ d, cap d≤1) :
    LooseRow93 a P s t := by
  induction h with
  | nil => exact LooseRow93.nil
  | cons b P u v s t cap hb hu hv hab hperiod htail ih =>
    apply LooseRow93.cons b P u v s t hb hu hv hab
    · by_cases hd : a∣b
      · exact Or.inl hd
      · right
        have hg : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
        have hga : Nat.gcd a b<a := by
          have he := Nat.gcd_le_left b ha
          by_contra! hn
          have hc : Nat.gcd a b=a := Nat.le_antisymm he hn
          exact hd (by simpa only [hc] using Nat.gcd_dvd_right a b)
        have hh := hperiod (Nat.gcd a b) hg hga
        simp only [expenditure,dvd_refl,if_true] at hh
        exact hh.trans (hcap _)
    · exact ih (fun d => (Nat.sub_le _ _).trans (hcap d))

theorem loose_for_actual_profile {P : List ℕ} (F : OriginalProfileFacts P)
    (a : ℕ) (ha : a∈P) : LooseRow93 a P 10 (a+7) := by
  obtain ⟨i,hi⟩ := List.get_of_mem ha
  subst a
  have h1 : (∑ j,(F.row i).u j)=10 := by
    have h := (F.row i).momentOne
    simp_rw [←(F.row i).block,←Finset.mul_sum,Nat.mul_comm 10 (P.get i)] at h
    exact Nat.eq_of_mul_eq_mul_left
      (lt_of_lt_of_le (by decide : 0<3) (F.positive _ (List.get_mem P i))) h
  have h2 : (∑ j,(F.row i).u j*(F.row i).v j)=P.get i+7 := by
    have h := (F.row i).momentTwo
    simp_rw [←(F.row i).block,mul_assoc,←Finset.mul_sum] at h
    exact Nat.eq_of_mul_eq_mul_left
      (lt_of_lt_of_le (by decide : 0<3) (F.positive _ (List.get_mem P i))) h
  have hu (j : Fin P.length) : (F.row i).u j≤10 := by
    rw [←h1]
    exact Finset.single_le_sum (f:=(F.row i).u) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have hp := rowWitness_of_weighted_moments (P.get i) P (F.row i).u (F.row i).v
    (fun _=>1) (fun b hb => lt_of_lt_of_le (by decide : 0<3) (F.positive _ hb))
    hu (F.cap i) (F.row i).block (F.period i)
  rw [h1,h2] at hp
  exact physical_row_to_loose
    (lt_of_lt_of_le (by decide : 0<3) (F.positive _ (List.get_mem P i))) hp (fun _=>le_rfl)

theorem looseRow93_sublist {a : ℕ} {P U : List ℕ} (h : P <+ U)
    (hp : ∀ b∈U,0<b) {s t : ℕ} (hr : LooseRow93 a P s t) :
    LooseRow93 a U s t := by
  induction h generalizing s t with
  | slnil => exact hr
  | cons b h ih =>
    have ht := ih (fun c hc=>hp c (List.mem_cons_of_mem _ hc)) hr
    simpa only [zero_add,zero_mul] using
      LooseRow93.cons b _ 0 0 s t (hp b (by simp)) (by decide) (by decide)
        (by simp) (Or.inr (by decide)) ht
  | cons_cons b h ih =>
    cases hr with
    | cons _ _ u v s t hb hu hv hab hper ht =>
      exact LooseRow93.cons b _ u v s t hb hu hv hab hper
        (ih (fun c hc=>hp c (List.mem_cons_of_mem _ hc)) ht)

theorem looseRow93_perm {a : ℕ} {P U : List ℕ} (h : P.Perm U)
    {s t : ℕ} (hr : LooseRow93 a P s t) : LooseRow93 a U s t := by
  induction h generalizing s t with
  | nil => exact hr
  | cons b h ih =>
    cases hr with
    | cons _ _ u v s t hb hu hv hab hper ht =>
      exact LooseRow93.cons b _ u v s t hb hu hv hab hper (ih ht)
  | swap x y =>
    cases hr with
    | cons b _ u v s t hb hu hv hab hper ht =>
      cases ht with
      | cons c _ w z sx tx hc hw hz hac hperc htail =>
        have hNew := LooseRow93.cons x _ w z _ _ hc hw hz hac hperc
          (LooseRow93.cons y _ u v sx tx hb hu hv hab hper htail)
        simpa only [Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using hNew
  | trans _ _ ih ih' => exact ih' (ih hr)

theorem looseRow93_subperm {a : ℕ} {P U : List ℕ} (h : P <+~ U)
    (hp : ∀ b∈U,0<b) {s t : ℕ} (hr : LooseRow93 a P s t) :
    LooseRow93 a U s t := by
  obtain ⟨Q,hQ,hS⟩ := h
  exact looseRow93_sublist hS hp (looseRow93_perm hQ.symm hr)

theorem cycle_multiplicity_tail_bound (b : ℕ) (L : List ℕ) :
    b*L.count b≤L.sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases hx : b=x
    · subst x
      simp only [List.count_cons_self, Nat.mul_succ,List.sum_cons]
      omega
    · rw [List.count_cons_of_ne (Ne.symm hx),List.sum_cons]
      omega

/-- The precise sound validator for a marked dead prefix; the checked
multiset inclusion is needed, so an arbitrary hint cannot exclude a profile. -/
theorem dead_prefix_excludes_actual {P U : List ℕ} {a : ℕ}
    (F : OriginalProfileFacts P) (ha : a∈P)
    (hinflated : P.filter (relevant a) <+~ U) (hpos : ∀ b∈U,0<b)
    (hdead : rowLoose93 a U 10 (a+7)=false) : False := by
  have hA : 0<a := lt_of_lt_of_le (by decide : 0<3) (F.positive _ ha)
  have h := rowLoose93_complete (looseRow93_subperm hinflated hpos
    (localRow_filter_relevant hA (loose_for_actual_profile F a ha)))
  rw [hdead] at h
  contradiction

end Symconf93

#print axioms Symconf93.dead_prefix_excludes_actual
#print axioms Symconf93.cycle_multiplicity_tail_bound
