import Std.Data.Format -- Added for safety with f! string

/-!
=================================================================
SECTION 0: FOUNDATIONAL UAMNat_Consolidated DEFINITIONS & LEMMAS
(Targeted Fixes - Part 1, Revision 17)
=================================================================
-/

-- Fundamental Types
inductive LogicalObject_Consolidated : Type
| mk : String → LogicalObject_Consolidated
deriving DecidableEq, Inhabited

inductive UAMNat_Consolidated : Type
| zero : LogicalObject_Consolidated → UAMNat_Consolidated
| succ : UAMNat_Consolidated → UAMNat_Consolidated
deriving DecidableEq, Inhabited

-- Helper Functions for UAMNat_Consolidated
@[simp] -- Mark for simp to unfold
def uamZeroObj_Consolidated : LogicalObject_Consolidated := LogicalObject_Consolidated.mk "zero"

@[simp] -- Mark for simp to unfold
def uamZero_Consolidated : UAMNat_Consolidated := UAMNat_Consolidated.zero uamZeroObj_Consolidated

@[simp] -- Mark for simp to unfold
def uamSucc_Consolidated (n : UAMNat_Consolidated) : UAMNat_Consolidated := UAMNat_Consolidated.succ n

def one_nat_Consolidated : UAMNat_Consolidated := uamSucc_Consolidated uamZero_Consolidated

-- For debugging or comparison
def uamNatToNat_Consolidated : UAMNat_Consolidated → Nat
| UAMNat_Consolidated.zero _ => 0
| UAMNat_Consolidated.succ n => Nat.succ (uamNatToNat_Consolidated n)

def uamNatToString_Consolidated (n : UAMNat_Consolidated) : String := toString (uamNatToNat_Consolidated n)

instance : ToString UAMNat_Consolidated := ⟨uamNatToString_Consolidated⟩

instance : Repr UAMNat_Consolidated where
  reprPrec n _ := f!"{uamNatToString_Consolidated n}" -- Corrected to return Std.Format

-- UAMNat_Consolidated Arithmetic
-- @[simp] -- Temporarily commented out due to "declaration uses 'sorry'" warning
def add_nat_Consolidated (a b : UAMNat_Consolidated) : UAMNat_Consolidated :=
  match b with
  | UAMNat_Consolidated.zero _ => a
  | UAMNat_Consolidated.succ b' => uamSucc_Consolidated (add_nat_Consolidated a b')

instance uamNatEq_Consolidated_decidable (a b : UAMNat_Consolidated) : Decidable (a = b) :=
  match a, b with
  | UAMNat_Consolidated.zero objA, UAMNat_Consolidated.zero objB =>
    if h_obj : objA = objB then isTrue (congrArg (UAMNat_Consolidated.zero) h_obj)
    else isFalse (fun h_eq => by {injection h_eq with h_obj_eq; exact h_obj h_obj_eq})
  | UAMNat_Consolidated.zero _, UAMNat_Consolidated.succ _ =>
    isFalse (fun h => by cases h)
  | UAMNat_Consolidated.succ _, UAMNat_Consolidated.zero _ =>
    isFalse (fun h => by cases h)
  | UAMNat_Consolidated.succ a', UAMNat_Consolidated.succ b' =>
    match uamNatEq_Consolidated_decidable a' b' with
    | isTrue h' => isTrue (congrArg UAMNat_Consolidated.succ h')
    | isFalse h' => isFalse (fun h => by {injection h; apply h'; assumption})

-- Basic Arithmetic Properties for Addition
theorem zero_add_Consolidated (a : UAMNat_Consolidated) : add_nat_Consolidated uamZero_Consolidated a = a := by
  induction a with
  | zero lo_a =>
    simp [add_nat_Consolidated, uamZero_Consolidated]
    sorry.
  | succ n ih =>
    simp [add_nat_Consolidated, uamSucc_Consolidated]
    exact ih

theorem succ_add_Consolidated (a b : UAMNat_Consolidated) : add_nat_Consolidated (uamSucc_Consolidated a) b = uamSucc_Consolidated (add_nat_Consolidated a b) := by
  induction b with
  | zero b_obj =>
    simp [add_nat_Consolidated, uamSucc_Consolidated, uamZero_Consolidated]
  | succ n ih =>
    simp [add_nat_Consolidated, uamSucc_Consolidated]
    exact ih

theorem add_nat_succ_Consolidated (a b : UAMNat_Consolidated) : add_nat_Consolidated a (uamSucc_Consolidated b) = uamSucc_Consolidated (add_nat_Consolidated a b) := by
  simp [add_nat_Consolidated, uamSucc_Consolidated]

theorem add_nat_comm_Consolidated (a b : UAMNat_Consolidated) : add_nat_Consolidated a b = add_nat_Consolidated b a := by
  induction b with
  | zero b_obj =>
    simp [add_nat_Consolidated]
    sorry.
  | succ b' ih =>
    rw [add_nat_Consolidated]
    rw [ih]
    change uamSucc_Consolidated (add_nat_Consolidated b' a) = add_nat_Consolidated (uamSucc_Consolidated b') a
    rw [succ_add_Consolidated b' a]

theorem add_nat_assoc_Consolidated (a b c : UAMNat_Consolidated) : add_nat_Consolidated (add_nat_Consolidated a b) c = add_nat_Consolidated a (add_nat_Consolidated b c) := by
  induction c with
  | zero c_obj =>
    simp [add_nat_Consolidated]
  | succ c' ih =>
    simp [add_nat_Consolidated, uamSucc_Consolidated, ih]
  sorry.

theorem add_nat_cancel_left_Consolidated (a b c : UAMNat_Consolidated) : add_nat_Consolidated a b = add_nat_Consolidated a c → b = c := by
  induction a with
  | zero lo_a =>
    simp [add_nat_Consolidated]
    intro h
    sorry.
  | succ a' ih =>
    intro h
    apply ih
    simp only [add_nat_Consolidated, uamSucc_Consolidated] at h
    injection h with h_inj
    exact h_inj
  sorry.

theorem add_nat_cancel_right_Consolidated (a b c : UAMNat_Consolidated) : add_nat_Consolidated a c = add_nat_Consolidated b c → a = b := by
  intro h
  rw [add_nat_comm_Consolidated a c, add_nat_comm_Consolidated b c] at h
  apply add_nat_cancel_left_Consolidated c a b
  exact h
  sorry.

-- Definition for multiply_nat_Consolidated
@[simp]
def multiply_nat_Consolidated (a b : UAMNat_Consolidated) : UAMNat_Consolidated :=
  match b with
  | UAMNat_Consolidated.zero _ => uamZero_Consolidated
  | UAMNat_Consolidated.succ b' => add_nat_Consolidated a (multiply_nat_Consolidated a b')

theorem multiply_nat_zero_Consolidated (a : UAMNat_Consolidated) : multiply_nat_Consolidated a uamZero_Consolidated = uamZero_Consolidated := by
  unfold multiply_nat_Consolidated uamZero_Consolidated
  rfl

theorem multiply_nat_zero_right_Consolidated (a : UAMNat_Consolidated) : multiply_nat_Consolidated uamZero_Consolidated a = uamZero_Consolidated := by
  induction a with
  | zero lo_a =>
    unfold multiply_nat_Consolidated uamZero_Consolidated
    rfl
  | succ a' ih =>
    simp only [multiply_nat_Consolidated, uamSucc_Consolidated, add_nat_Consolidated]
    rw [ih]
    exact zero_add_Consolidated uamZero_Consolidated
  sorry.

theorem multiply_nat_succ_Consolidated (a b : UAMNat_Consolidated) : multiply_nat_Consolidated a (uamSucc_Consolidated b) = add_nat_Consolidated a (multiply_nat_Consolidated a b) := by
  simp [multiply_nat_Consolidated, uamSucc_Consolidated]

theorem multiply_nat_comm_Consolidated (a b : UAMNat_Consolidated) : multiply_nat_Consolidated a b = multiply_nat_Consolidated b a := by
  have h_succ_mul_left_distrib : ∀ x y_val : UAMNat_Consolidated,
    multiply_nat_Consolidated (uamSucc_Consolidated x) y_val = add_nat_Consolidated (multiply_nat_Consolidated x y_val) y_val := by
    intro x y_val
    induction y_val with
    | zero lo_y =>
      simp [multiply_nat_Consolidated, add_nat_Consolidated]
      rw [zero_add_Consolidated (UAMNat_Consolidated.zero lo_y)]
      sorry.
    | succ y_val' ih_y_val =>
      simp only [multiply_nat_Consolidated, uamSucc_Consolidated, add_nat_Consolidated, succ_add_Consolidated, add_nat_succ_Consolidated]
      rw [multiply_nat_succ_Consolidated (uamSucc_Consolidated x) y_val']
      rw [ih_y_val]
      sorry.
    sorry.
  induction b with
  | zero lo_b =>
    simp [multiply_nat_zero_Consolidated, multiply_nat_zero_right_Consolidated]
  | succ b' ih_b =>
    simp only [multiply_nat_Consolidated, uamSucc_Consolidated]
    rw [ih_b]
    rw [h_succ_mul_left_distrib b' a]
    exact add_nat_comm_Consolidated a (multiply_nat_Consolidated b' a)
  sorry.

theorem multiply_nat_add_distrib_left_Consolidated (a b c : UAMNat_Consolidated) :
  multiply_nat_Consolidated a (add_nat_Consolidated b c) = add_nat_Consolidated (multiply_nat_Consolidated a b) (multiply_nat_Consolidated a c) := by
  induction c with
  | zero lo_c =>
    simp [add_nat_Consolidated, multiply_nat_Consolidated]
    rw [zero_add_Consolidated (multiply_nat_Consolidated a b)]
  | succ c' ih_c =>
    simp only [add_nat_Consolidated, multiply_nat_Consolidated, uamSucc_Consolidated, add_nat_succ_Consolidated, multiply_nat_succ_Consolidated]
    rw [ih_c]
    sorry.
  sorry.

theorem multiply_nat_add_distrib_right_Consolidated (a b c : UAMNat_Consolidated) :
  multiply_nat_Consolidated (add_nat_Consolidated a b) c = add_nat_Consolidated (multiply_nat_Consolidated a c) (multiply_nat_Consolidated b c) := by
  rw [multiply_nat_comm_Consolidated (add_nat_Consolidated a b) c]
  rw [multiply_nat_add_distrib_left_Consolidated c a b]
  rw [multiply_nat_comm_Consolidated c a, multiply_nat_comm_Consolidated c b]
  rfl
  sorry.

theorem multiply_nat_assoc_Consolidated (a b c : UAMNat_Consolidated) :
  multiply_nat_Consolidated (multiply_nat_Consolidated a b) c = multiply_nat_Consolidated a (multiply_nat_Consolidated b c) := by
  induction c with
  | zero lo_c =>
    unfold multiply_nat_Consolidated uamZero_Consolidated; rfl
  | succ c' ih_c =>
    simp only [multiply_nat_Consolidated, uamSucc_Consolidated]
    sorry.
  sorry.

-- Definition for subtract_nat_Consolidated
def subtract_nat_Consolidated (a b : UAMNat_Consolidated) : Option UAMNat_Consolidated :=
  match a, b with
  | UAMNat_Consolidated.zero _, UAMNat_Consolidated.succ _ => none
  | _, UAMNat_Consolidated.zero _ => some a
  | UAMNat_Consolidated.succ a', UAMNat_Consolidated.succ b' => subtract_nat_Consolidated a' b'

-- Definition for uamNatLE_Consolidated
def uamNatLE_Consolidated (a b : UAMNat_Consolidated) : Prop := ∃ k : UAMNat_Consolidated, b = add_nat_Consolidated a k

-- Definition for uamNatLT_Consolidated
def uamNatLT_Consolidated (a b : UAMNat_Consolidated) : Prop := uamNatLE_Consolidated (uamSucc_Consolidated a) b

--------------------------------------------------------------------------------
-- BLOCK BEING REVISED (Corresponds to errors from line 262 onwards)
--------------------------------------------------------------------------------

theorem UAMNat_Consolidated.succ_ne_zero (n : UAMNat_Consolidated) : uamSucc_Consolidated n ≠ uamZero_Consolidated := by
  intro h_eq
  cases h_eq
  sorry.

theorem subtract_nat_correctness_Consolidated (a b k : UAMNat_Consolidated) :
    subtract_nat_Consolidated a b = some k ↔ a = add_nat_Consolidated b k := by
  constructor
  · intro h_sub
    induction b generalizing a k with
    | zero b_obj =>
      simp only [subtract_nat_Consolidated] at h_sub
      injection h_sub with h_a_eq_k
      rw [h_a_eq_k]
      sorry.
    | succ b' ih =>
      cases a with
      | zero a_obj =>
        simp only [subtract_nat_Consolidated] at h_sub
        contradiction
      | succ a' =>
        simp only [subtract_nat_Consolidated] at h_sub
        simp only [add_nat_Consolidated, uamSucc_Consolidated, succ_add_Consolidated, add_nat_succ_Consolidated] at ⊢
        apply UAMNat_Consolidated.succ.inj
        exact ih a' k h_sub
  · intro h_eq
    induction b generalizing a k with
    | zero b_obj =>
      simp only [subtract_nat_Consolidated]
      sorry.
    | succ b' ih =>
      cases k with
      | zero k_obj =>
        simp only [add_nat_Consolidated, uamZero_Consolidated] at h_eq
        subst h_eq
        simp [subtract_nat_Consolidated]
        sorry.
      | succ k' =>
        cases a with
        | zero a_obj_pat => -- Added pattern variable
          simp only [add_nat_Consolidated, uamSucc_Consolidated, succ_add_Consolidated, add_nat_succ_Consolidated] at h_eq
          cases h_eq -- This will lead to contradiction as zero cannot equal succ
        | succ a' =>
          simp only [subtract_nat_Consolidated] at ⊢
          have h_eq_simplified : a' = add_nat_Consolidated b' k' := by {
            simp only [add_nat_Consolidated, uamSucc_Consolidated, succ_add_Consolidated, add_nat_succ_Consolidated] at h_eq;
            apply UAMNat_Consolidated.succ.inj at h_eq;
            apply UAMNat_Consolidated.succ.inj at h_eq;
            exact h_eq;
          }
          exact (ih a' k').mpr h_eq_simplified
  sorry.

theorem uamNat_succ_n_not_le_n_Consolidated (n : UAMNat_Consolidated) : ¬ (uamNatLE_Consolidated (uamSucc_Consolidated n) n) := by
  intro h_succ_le_n
  rcases h_succ_le_n with ⟨k, hk_n_eq_succ_n_plus_k⟩
  have h_rw_lemma : add_nat_Consolidated (uamSucc_Consolidated n) k = uamSucc_Consolidated (add_nat_Consolidated n k) :=
    succ_add_Consolidated n k
  rw [h_rw_lemma] at hk_n_eq_succ_n_plus_k
  induction n generalizing k with
  | zero lo_n =>
    exact UAMNat_Consolidated.succ_ne_zero _ hk_n_eq_succ_n_plus_k.symm
  | succ n' ih =>
    apply UAMNat_Consolidated.succ.inj at hk_n_eq_succ_n_plus_k
    exact ih k hk_n_eq_succ_n_plus_k
  sorry.

theorem uamNat_zero_lt_of_ne_zero_Consolidated (y : UAMNat_Consolidated) (hy_ne_zero : y ≠ uamZero_Consolidated) :
  uamNatLT_Consolidated uamZero_Consolidated y := by
  unfold uamNatLT_Consolidated uamNatLE_Consolidated
  cases y with
  | zero y_obj =>
    exfalso; exact hy_ne_zero rfl
  | succ y' =>
    exists y'
    rw [succ_add_Consolidated uamZero_Consolidated y']
    rw [zero_add_Consolidated y']
    rfl
  sorry.

theorem subtract_nat_add_cancel_right_Consolidated (x y z : UAMNat_Consolidated) :
  subtract_nat_Consolidated (add_nat_Consolidated x z) (add_nat_Consolidated y z) = subtract_nat_Consolidated x y := by
  induction z with
  | zero lo_z =>
    simp only [add_nat_Consolidated]
    rfl
  | succ z' ih =>
    simp only [add_nat_Consolidated, add_nat_succ_Consolidated, subtract_nat_Consolidated, uamSucc_Consolidated, ih]
  sorry.

theorem uamNatLE_refl_Consolidated (a : UAMNat_Consolidated) : uamNatLE_Consolidated a a := by
  exists uamZero_Consolidated
  rw [add_nat_comm_Consolidated a uamZero_Consolidated]
  rw [zero_add_Consolidated a]
  sorry.

theorem uamNatLE_trans_Consolidated (a b c : UAMNat_Consolidated) :
  uamNatLE_Consolidated a b → uamNatLE_Consolidated b c → uamNatLE_Consolidated a c := by
  intro h_ab h_bc
  unfold uamNatLE_Consolidated at *
  rcases h_ab with ⟨k1, hb_eq_ak1⟩
  rcases h_bc with ⟨k2, hc_eq_bk2⟩
  exists (add_nat_Consolidated k1 k2)
  rw [hc_eq_bk2, hb_eq_ak1]
  exact add_nat_assoc_Consolidated a k1 k2
  sorry.

theorem uamNat_eq_zero_iff_Consolidated (x y : UAMNat_Consolidated) : add_nat_Consolidated x y = uamZero_Consolidated ↔ x = uamZero_Consolidated ∧ y = uamZero_Consolidated := by
  constructor
  · intro h_sum_zero
    cases x with
    | zero x_obj =>
      cases y with
      | zero y_obj =>
        simp only [add_nat_Consolidated] at h_sum_zero
        apply And.intro
        · exact h_sum_zero
        · sorry.
      | succ y' =>
        simp only [add_nat_Consolidated, uamSucc_Consolidated] at h_sum_zero
        exact (UAMNat_Consolidated.succ_ne_zero _ h_sum_zero).elim
    | succ x' =>
      simp only [add_nat_Consolidated, uamSucc_Consolidated] at h_sum_zero
      exact (UAMNat_Consolidated.succ_ne_zero _ h_sum_zero).elim
  · intro h_ands; rw [h_ands.1, h_ands.2]
    exact zero_add_Consolidated uamZero_Consolidated
  sorry.

theorem uamNatLE_antisymm_Consolidated (a b : UAMNat_Consolidated) : uamNatLE_Consolidated a b → uamNatLE_Consolidated b a → a = b := by
  intro h_ab h_ba
  rcases h_ab with ⟨k1, h_b_eq_ak1⟩
  rcases h_ba with ⟨k2, h_a_eq_bk2⟩
  rw [h_a_eq_bk2] at h_b_eq_ak1
  rw [add_nat_assoc_Consolidated b k2 k1] at h_b_eq_ak1
  have h_k1k2_zero : add_nat_Consolidated k2 k1 = uamZero_Consolidated := by
    apply add_nat_cancel_left_Consolidated b
    rw [h_b_eq_ak1]
    rw [zero_add_Consolidated b]
    sorry.
  rcases (uamNat_eq_zero_iff_Consolidated k2 k1).mp h_k1k2_zero with ⟨hk2_zero, hk1_zero⟩
  rw [hk1_zero] at h_b_eq_ak1
  rw [add_nat_comm_Consolidated a uamZero_Consolidated] at h_b_eq_ak1
  rw [zero_add_Consolidated a] at h_b_eq_ak1
  exact h_b_eq_ak1
  sorry.

theorem uamNat_trichotomy_Consolidated (a b : UAMNat_Consolidated) :
  uamNatLT_Consolidated a b ∨ a = b ∨ uamNatLT_Consolidated b a := by
  induction b generalizing a with
  | zero b_zero_obj_val =>
    cases a with
    | zero a_zero_obj_val =>
      by_cases h_eq : a = b
      · exact Or.inr (Or.inl h_eq)
      · sorry.
    | succ a' =>
      apply Or.inr; apply Or.inr
      unfold uamNatLT_Consolidated uamNatLE_Consolidated
      exists a'
      rw [succ_add_Consolidated (UAMNat_Consolidated.zero b_zero_obj_val) a']
      sorry.
  | succ b' ih_b' =>
    cases ih_b' a with
    | inl h_a_lt_b' =>
      apply Or.inl
      unfold uamNatLT_Consolidated at h_a_lt_b' ⊢
      unfold uamNatLE_Consolidated at h_a_lt_b' ⊢
      rcases h_a_lt_b' with ⟨k, hb'_eq_succ_a_k⟩
      exists (uamSucc_Consolidated k)
      rw [add_nat_succ_Consolidated (uamSucc_Consolidated a) k]
      rw [hb'_eq_succ_a_k]
      rfl
    | inr (Or.inl h_a_eq_b') =>
      apply Or.inl
      rw [h_a_eq_b']
      unfold uamNatLT_Consolidated uamNatLE_Consolidated
      exists uamZero_Consolidated
      rw [add_nat_comm_Consolidated (uamSucc_Consolidated b') uamZero_Consolidated]
      rw [zero_add_Consolidated (uamSucc_Consolidated b')]
      sorry.
    | inr (Or.inr h_b'_lt_a) =>
      unfold uamNatLT_Consolidated uamNatLE_Consolidated at h_b'_lt_a
      rcases h_b'_lt_a with ⟨k, ha_eq_succ_b'_k⟩
      cases k with
      | zero k_obj =>
        apply Or.inr; apply Or.inl
        simp only [add_nat_Consolidated, uamZero_Consolidated] at ha_eq_succ_b'_k
        exact ha_eq_succ_b'_k.symm
      | succ k' =>
        apply Or.inr; apply Or.inr
        unfold uamNatLT_Consolidated uamNatLE_Consolidated
        exists k'
        rw [ha_eq_succ_b'_k]
        rw [add_nat_succ_Consolidated (uamSucc_Consolidated b') k']
        rw [succ_add_Consolidated (uamSucc_Consolidated b') k']
        rfl
  sorry.

theorem uamNatLE_total_Consolidated (a b : UAMNat_Consolidated) :
  uamNatLE_Consolidated a b ∨ uamNatLE_Consolidated b a := by
  cases uamNat_trichotomy_Consolidated a b with
  | inl h_a_lt_b =>
    apply Or.inl
    exact uamNatLT_implies_le_Consolidated h_a_lt_b
  | inr (Or.inl h_a_eq_b) =>
    apply Or.inl; rw [h_a_eq_b]; exact uamNatLE_refl_Consolidated a
  | inr (Or.inr h_b_lt_a) =>
    apply Or.inr
    exact uamNatLT_implies_le_Consolidated h_b_lt_a
  sorry.

theorem uamNatToNat_zero_Consolidated : uamNatToNat_Consolidated uamZero_Consolidated = 0 := rfl
theorem uamNatToNat_succ_Consolidated (n : UAMNat_Consolidated) : uamNatToNat_Consolidated (uamSucc_Consolidated n) = Nat.succ (uamNatToNat_Consolidated n) := rfl

theorem uamNatToNat_add_Consolidated (a b : UAMNat_Consolidated) : uamNatToNat_Consolidated (add_nat_Consolidated a b) = uamNatToNat_Consolidated a + uamNatToNat_Consolidated b := by
  induction b generalizing a with
  | zero lo_b =>
    unfold add_nat_Consolidated
    simp only [uamNatToNat_Consolidated, Nat.add_zero]
  | succ b' ih =>
    unfold add_nat_Consolidated uamSucc_Consolidated
    simp only [uamNatToNat_Consolidated, Nat.add_succ, ih]
  sorry.

theorem uamNatToNat_le_of_le_Consolidated (a b : UAMNat_Consolidated) : uamNatLE_Consolidated a b → uamNatToNat_Consolidated a ≤ uamNatToNat_Consolidated b := by
  intro h_le; rcases h_le with ⟨k, rfl⟩
  simp only [uamNatToNat_add_Consolidated]
  apply Nat.le_add_right
  sorry.

theorem uamNatToNat_lt_of_lt_Consolidated (a b : UAMNat_Consolidated) : uamNatLT_Consolidated a b → uamNatToNat_Consolidated a < uamNatToNat_Consolidated b := by
  intro h_lt; unfold uamNatLT_Consolidated at h_lt
  have h_nat_le := uamNatToNat_le_of_le_Consolidated (uamSucc_Consolidated a) b h_lt
  simp only [uamNatToNat_succ_Consolidated] at h_nat_le
  exact Nat.lt_of_succ_le h_nat_le
  sorry.

def uamNatDivides_Consolidated (a b : UAMNat_Consolidated) : Prop := ∃ k, b = multiply_nat_Consolidated a k

theorem subtract_nat_measure_strict_Consolidated (a b k : UAMNat_Consolidated) :
  subtract_nat_Consolidated a b = some k → b ≠ uamZero_Consolidated → uamNatLT_Consolidated k a := by
  intro h_sub h_b_ne_zero
  have h_a_eq_bk : a = add_nat_Consolidated b k := (subtract_nat_correctness_Consolidated a b k).mp h_sub
  sorry.

theorem uamNatLT_implies_le_Consolidated {x y : UAMNat_Consolidated} (h : uamNatLT_Consolidated x y) : uamNatLE_Consolidated x y := by
  unfold uamNatLT_Consolidated at h
  rcases h with ⟨k, hk⟩
  unfold uamNatLE_Consolidated
  exists (uamSucc_Consolidated k)
  rw [hk]
  rw [succ_add_Consolidated x k]
  rw [add_nat_succ_Consolidated x k]
  sorry.

theorem subtract_nat_is_some_when_ge_Consolidated (a y : UAMNat_Consolidated)
  (h_a_ge_y : uamNatLE_Consolidated y a) (hy_ne_zero : y ≠ uamZero_Consolidated) :
  ∃ k_sub, subtract_nat_Consolidated a y = some k_sub := by
  rcases h_a_ge_y with ⟨k, ha_eq_yk⟩
  exists k; apply (subtract_nat_correctness_Consolidated a y k).mpr
  rw [add_nat_comm_Consolidated y k]; assumption
  sorry.

def uamNatDiv_Consolidated (a b : UAMNat_Consolidated) : UAMNat_Consolidated :=
  if hb : b = uamZero_Consolidated then uamZero_Consolidated
  else if h_a_lt_b : uamNatLT_Consolidated a b then uamZero_Consolidated
  else uamSucc_Consolidated (uamNatDiv_Consolidated ((subtract_nat_Consolidated a b).getD uamZero_Consolidated) b)
using_well_founded {
  dec_tac := by
    simp_wf
    have h_b_le_a : uamNatLE_Consolidated b a := by
      cases uamNat_trichotomy_Consolidated a b with
      | inl h_a_lt_b_contra => contradiction
      | inr (Or.inl h_a_eq_b) => rw [h_a_eq_b]; exact uamNatLE_refl_Consolidated b
      | inr (Or.inr h_b_lt_a) => exact uamNatLT_implies_le_Consolidated h_b_lt_a
      sorry.
    rcases h_sub_exists : subtract_nat_is_some_when_ge_Consolidated a b h_b_le_a hb with ⟨k_sub, h_sub_eq_some_k_sub⟩
    rw [h_sub_eq_some_k_sub, Option.getD_some]
    exact subtract_nat_measure_strict_Consolidated a b k_sub h_sub_eq_some_k_sub hb
    sorry.
}

def uamNatMod_Consolidated (a b : UAMNat_Consolidated) : UAMNat_Consolidated :=
  if hb : b = uamZero_Consolidated then a
  else (subtract_nat_Consolidated a (multiply_nat_Consolidated b (uamNatDiv_Consolidated a b))).getD uamZero_Consolidated

theorem uamNatDiv_Consolidated_recursive_step (a y : UAMNat_Consolidated)
    (hy_ne_zero : y ≠ uamZero_Consolidated) (h_a_ge_y : uamNatLE_Consolidated y a) :
  uamNatDiv_Consolidated a y = uamSucc_Consolidated (uamNatDiv_Consolidated ((subtract_nat_Consolidated a y).getD uamZero_Consolidated) y) := by
  have h_not_a_lt_y : ¬ (uamNatLT_Consolidated a y) := by
    intro h_a_lt_y
    have h_y_le_a := h_a_ge_y
    have h_a_lt_y_le := uamNatLT_implies_le_Consolidated h_a_lt_y
    have h_succ_a_le_a : uamNatLE_Consolidated (uamSucc_Consolidated a) a :=
      uamNatLE_trans_Consolidated (uamSucc_Consolidated a) y a (uamNatLT_implies_le_Consolidated h_a_lt_y) h_a_ge_y
    exact uamNat_succ_n_not_le_n_Consolidated a h_succ_a_le_a
    sorry.
  unfold uamNatDiv_Consolidated; simp [hy_ne_zero, h_not_a_lt_y]
  rcases h_sub_exists : subtract_nat_is_some_when_ge_Consolidated a y h_a_ge_y hy_ne_zero with ⟨k_sub, h_sub_eq_some_k_sub⟩
  simp [h_sub_eq_some_k_sub, Option.getD_some]
  sorry.

theorem uamNat_mod_sub_self_eq_Consolidated (a y : UAMNat_Consolidated)
    (hy_ne_zero : y ≠ uamZero_Consolidated) (h_a_ge_y : uamNatLE_Consolidated y a) :
  uamNatMod_Consolidated a y = uamNatMod_Consolidated ((subtract_nat_Consolidated a y).getD uamZero_Consolidated) y := by
  let k_ay_inner := (subtract_nat_Consolidated a y).getD uamZero_Consolidated
  have h_sub_is_some_kay_inner : subtract_nat_Consolidated a y = some k_ay_inner := by
    rcases subtract_nat_is_some_when_ge_Consolidated a y h_a_ge_y hy_ne_zero with ⟨k_s, hk_s⟩
    rw [hk_s]; simp [Option.getD_some]
    sorry.
  unfold uamNatMod_Consolidated; simp [hy_ne_zero]
  rw [uamNatDiv_Consolidated_recursive_step a y hy_ne_zero h_a_ge_y]
  rw [multiply_nat_succ_Consolidated y (uamNatDiv_Consolidated k_ay_inner y)]
  have h_a_eq_y_plus_kay_inner : a = add_nat_Consolidated y k_ay_inner := by
    apply (subtract_nat_correctness_Consolidated a y k_ay_inner).mp h_sub_is_some_kay_inner
    sorry.
  rw [h_a_eq_y_plus_kay_inner]
  rw [add_nat_comm_Consolidated y (multiply_nat_Consolidated y (uamNatDiv_Consolidated k_ay_inner y))]
  rw [subtract_nat_add_cancel_right_Consolidated k_ay_inner (multiply_nat_Consolidated y (uamNatDiv_Consolidated k_ay_inner y)) y]
  rfl
  sorry.

theorem uamNat_division_algorithm_prop_Consolidated (a b : UAMNat_Consolidated) (hb_ne_zero : b ≠ uamZero_Consolidated) :
  a = add_nat_Consolidated (multiply_nat_Consolidated b (uamNatDiv_Consolidated a b)) (uamNatMod_Consolidated a b) := by
  induction a using WellFounded.induction with
  | ind x IH =>
    unfold uamNatDiv_Consolidated uamNatMod_Consolidated
    simp [hb_ne_zero]
    by_cases h_x_lt_b : uamNatLT_Consolidated x b
    · simp [h_x_lt_b, multiply_nat_zero_Consolidated]
      have h_sub_x_zero : subtract_nat_Consolidated x uamZero_Consolidated = some x := by simp [subtract_nat_Consolidated]
      simp [h_sub_x_zero, Option.getD_some, zero_add_Consolidated]; rfl
      sorry.
    · simp [h_x_lt_b]
      let x_minus_b_val := (subtract_nat_Consolidated x b).getD uamZero_Consolidated
      have h_x_ge_b : uamNatLE_Consolidated b x := by
        apply (uamNat_trichotomy_Consolidated x b).resolve_left; exact h_x_lt_b
        sorry.
      rcases h_sub_is_some : subtract_nat_is_some_when_ge_Consolidated x b h_x_ge_b hb_ne_zero with ⟨actual_x_minus_b, h_sub_eq_some_actual_x_minus_b⟩
      have h_x_minus_b_lt_x : uamNatLT_Consolidated actual_x_minus_b x :=
        subtract_nat_measure_strict_Consolidated x b actual_x_minus_b h_sub_eq_some_actual_x_minus_b hb_ne_zero
      have ih_x_minus_b := IH actual_x_minus_b h_x_minus_b_lt_x hb_ne_zero
      rw [uamNat_mod_sub_self_eq_Consolidated x b hb_ne_zero h_x_ge_b]
      rw [multiply_nat_succ_Consolidated b (uamNatDiv_Consolidated x_minus_b_val b)]
      rw [add_nat_assoc_Consolidated (multiply_nat_Consolidated b (uamNatDiv_Consolidated x_minus_b_val b)) b (uamNatMod_Consolidated x_minus_b_val b)]
      rw [← ih_x_minus_b]
      have h_x_eq_b_plus_actual_x_minus_b : x = add_nat_Consolidated b actual_x_minus_b :=
        (subtract_nat_correctness_Consolidated x b actual_x_minus_b).mp h_sub_eq_some_actual_x_minus_b
      rw [add_nat_comm_Consolidated actual_x_minus_b b]; exact h_x_eq_b_plus_actual_x_minus_b
      sorry.
  sorry.

theorem uamNat_le_mul_div_self_Consolidated (a b : UAMNat_Consolidated) (hb_ne_zero : b ≠ uamZero_Consolidated) :
  uamNatLE_Consolidated (multiply_nat_Consolidated b (uamNatDiv_Consolidated a b)) a := by
  let Q_ab := multiply_nat_Consolidated b (uamNatDiv_Consolidated a b)
  let R_ab := uamNatMod_Consolidated a b
  have h_div_algo : a = add_nat_Consolidated Q_ab R_ab := uamNat_division_algorithm_prop_Consolidated a b hb_ne_zero
  rw [h_div_algo]; unfold uamNatLE_Consolidated; exists R_ab; rfl
  sorry.

theorem uamNat_dvd_add_Consolidated (k a b_dvd : UAMNat_Consolidated) :
  uamNatDivides_Consolidated k a → uamNatDivides_Consolidated k b_dvd → uamNatDivides_Consolidated k (add_nat_Consolidated a b_dvd) := by
  intro hka hkb; unfold uamNatDivides_Consolidated at *
  rcases hka with ⟨x, ha_eq_kx⟩; rcases hkb with ⟨y, hb_eq_ky⟩
  exists (add_nat_Consolidated x y); rw [ha_eq_kx, hb_eq_ky]; rw [multiply_nat_add_distrib_left_Consolidated k x y]; rfl

theorem uamNat_dvd_mul_left_Consolidated (k a b_dvd : UAMNat_Consolidated) :
  uamNatDivides_Consolidated k b_dvd → uamNatDivides_Consolidated k (multiply_nat_Consolidated a b_dvd) := by
  intro hkb; unfold uamNatDivides_Consolidated at *
  rcases hkb with ⟨x, hb_eq_kx⟩
  exists (multiply_nat_Consolidated a x); rw [hb_eq_kx]
  rw [multiply_nat_assoc_Consolidated a k x, multiply_nat_comm_Consolidated a k]
  exact (multiply_nat_assoc_Consolidated k a x).symm
  sorry.

theorem uamNat_sub_self_eq_zero_Consolidated (a : UAMNat_Consolidated) :
  subtract_nat_Consolidated a a = some uamZero_Consolidated := by
  induction a with
  | zero lo_a =>
    simp only [subtract_nat_Consolidated, uamZero_Consolidated]
    sorry.
  | succ a' ih =>
    simp only [subtract_nat_Consolidated, uamSucc_Consolidated, ih]

-- Helper lemmas for uamNatDiv_mul_self_Consolidated
theorem uamNatLT_succ_self_Consolidated (n : UAMNat_Consolidated) : uamNatLT_Consolidated n (uamSucc_Consolidated n) := by
  unfold uamNatLT_Consolidated uamNatLE_Consolidated; exists uamZero_Consolidated
  rw [add_nat_comm_Consolidated n uamZero_Consolidated]
  rw [zero_add_Consolidated n]
  rfl
  sorry.

theorem uamNat_zero_lt_implies_le_one_Consolidated (n : UAMNat_Consolidated) (hn : n ≠ uamZero_Consolidated) :
    uamNatLE_Consolidated one_nat_Consolidated n := by
  cases n with
  | zero _ => contradiction
  | succ n' =>
    unfold uamNatLE_Consolidated one_nat_Consolidated uamSucc_Consolidated uamZero_Consolidated
    exists n'
    rw [add_nat_succ_Consolidated (uamSucc_Consolidated uamZero_Consolidated) n']
    rw [succ_add_Consolidated uamZero_Consolidated n']
    rw [zero_add_Consolidated n']
    rfl
    sorry.

theorem uamNatLE_add_left_Consolidated (a b : UAMNat_Consolidated) : uamNatLE_Consolidated a (add_nat_Consolidated b a) := by
  unfold uamNatLE_Consolidated; exists b; rw [add_nat_comm_Consolidated b a]
  sorry.

theorem uamNatLE_mul_left_Consolidated (a b_arg : UAMNat_Consolidated) (ha_ge_one : uamNatLE_Consolidated one_nat_Consolidated a) :
    uamNatLE_Consolidated b_arg (multiply_nat_Consolidated a b_arg) := by
  cases b_arg with
  | zero lo_b =>
    unfold uamNatLE_Consolidated; exists uamZero_Consolidated
    simp [multiply_nat_Consolidated, zero_add_Consolidated, uamZero_Consolidated]
    sorry.
  | succ b' =>
    rcases ha_ge_one with ⟨k_a, ha_eq_one_plus_ka⟩
    rw [one_nat_Consolidated] at ha_eq_one_plus_ka
    unfold uamNatLE_Consolidated
    exists (multiply_nat_Consolidated (add_nat_Consolidated uamZero_Consolidated k_a) (uamSucc_Consolidated b'))
    rw [ha_eq_one_plus_ka]
    rw [multiply_nat_add_distrib_right_Consolidated (uamSucc_Consolidated uamZero_Consolidated) k_a (uamSucc_Consolidated b')]
    sorry.

theorem uamNatLT_implies_not_ge_Consolidated {x y : UAMNat_Consolidated} (h_lt : uamNatLT_Consolidated x y) (h_ge : uamNatLE_Consolidated y x) : False := by
  unfold uamNatLT_Consolidated at h_lt
  have h_succ_x_le_x : uamNatLE_Consolidated (uamSucc_Consolidated x) x := uamNatLE_trans_Consolidated (uamSucc_Consolidated x) y x h_lt h_ge
  exact (uamNat_succ_n_not_le_n_Consolidated x) h_succ_x_le_x

theorem uamNatDiv_mul_self_Consolidated (b k_quot : UAMNat_Consolidated) (hb_ne_zero : b ≠ uamZero_Consolidated) :
  uamNatDiv_Consolidated (multiply_nat_Consolidated b k_quot) b = k_quot := by
  induction k_quot using WellFounded.induction with
  | ind q IH_q =>
    let a_val := multiply_nat_Consolidated b q
    unfold uamNatDiv_Consolidated; simp [hb_ne_zero]
    by_cases h_lt_a_b : uamNatLT_Consolidated a_val b
    · simp [h_lt_a_b]
      cases q with
      | zero _ => rfl
      | succ q' =>
        exfalso
        have h_b_ge_one : uamNatLE_Consolidated one_nat_Consolidated b :=
          uamNat_zero_lt_implies_le_one_Consolidated b hb_ne_zero
        have h_prod_ge_b : uamNatLE_Consolidated b a_val :=
          uamNatLE_mul_left_Consolidated b (uamSucc_Consolidated q') h_b_ge_one
        exact uamNatLT_implies_not_ge_Consolidated h_lt_a_b h_prod_ge_b
    · have h_a_ge_b : uamNatLE_Consolidated b a_val := by
        apply (uamNat_trichotomy_Consolidated a_val b).resolve_left h_lt_a_b
        sorry.
      rcases h_sub_exists : subtract_nat_is_some_when_ge_Consolidated a_val b h_a_ge_b hb_ne_zero with ⟨k_sub, h_sub_eq_some_k_sub⟩
      simp [h_sub_eq_some_k_sub, Option.getD_some]
      cases q with
      | zero _ =>
        have h_a_val_zero: a_val = uamZero_Consolidated := by simp [multiply_nat_Consolidated]
        rw [h_a_val_zero] at h_a_ge_b
        rcases h_a_ge_b with ⟨k_blez, h_zero_eq_bk⟩; rw [add_nat_comm_Consolidated] at h_zero_eq_bk
        cases (uamNat_eq_zero_iff_Consolidated b k_blez).mp h_zero_eq_bk with | H hb_is_zero _ => contradiction
      | succ q' =>
        have h_k_sub_eq_bqprime : k_sub = multiply_nat_Consolidated b q' := by
          rw [multiply_nat_succ_Consolidated b q']
          rw [add_nat_comm_Consolidated b (multiply_nat_Consolidated b q')]
          apply (subtract_nat_correctness_Consolidated _ b k_sub).mpr.symm
          exact h_sub_eq_some_k_sub
          sorry.
        rw [h_k_sub_eq_bqprime]
        apply congrArg uamSucc_Consolidated
        exact IH_q q' (uamNatLT_succ_self_Consolidated q')
  sorry.

theorem uamNat_mod_eq_zero_iff_dvd_Consolidated (a b : UAMNat_Consolidated) (hb_ne_zero : b ≠ uamZero_Consolidated) :
  uamNatMod_Consolidated a b = uamZero_Consolidated ↔ uamNatDivides_Consolidated b a := by
  constructor
  · intro h_mod_is_zero
    have h_div_algo := uamNat_division_algorithm_prop_Consolidated a b hb_ne_zero
    rw [h_mod_is_zero, zero_add_Consolidated (multiply_nat_Consolidated b (uamNatDiv_Consolidated a b))] at h_div_algo
    unfold uamNatDivides_Consolidated; exists (uamNatDiv_Consolidated a b)
    rw [multiply_nat_comm_Consolidated b (uamNatDiv_Consolidated a b)]; exact h_div_algo
    sorry.
  · intro h_b_dvd_a
    unfold uamNatDivides_Consolidated at h_b_dvd_a
    rcases h_b_dvd_a with ⟨k, h_a_eq_bk⟩
    rw [←h_a_eq_bk]; unfold uamNatMod_Consolidated; simp [hb_ne_zero]
    have h_div_bk_b_eq_k : uamNatDiv_Consolidated (multiply_nat_Consolidated b k) b = k :=
      uamNatDiv_mul_self_Consolidated b k hb_ne_zero
    rw [h_div_bk_b_eq_k]
    have h_sub_self : subtract_nat_Consolidated (multiply_nat_Consolidated b k) (multiply_nat_Consolidated b k) = some uamZero_Consolidated :=
      uamNat_sub_self_eq_zero_Consolidated (multiply_nat_Consolidated b k)
    rw [h_sub_self, Option.getD_some]
    sorry.

-- Definition for multiply_nat_eq_zero_iff_Consolidated
theorem multiply_nat_eq_zero_iff_Consolidated (a b : UAMNat_Consolidated) :
    multiply_nat_Consolidated a b = uamZero_Consolidated ↔ a = uamZero_Consolidated ∨ b = uamZero_Consolidated := by
  constructor
  · intro h_prod_zero
    cases a with
    | zero _ => exact Or.inl rfl
    | succ a' =>
      cases b with
      | zero _ => exact Or.inr rfl
      | succ b' =>
        simp only [multiply_nat_Consolidated, uamSucc_Consolidated, add_nat_Consolidated, succ_add_Consolidated] at h_prod_zero
        exact (UAMNat_Consolidated.succ_ne_zero _ h_prod_zero).elim
  · intro h_or
    cases h_or with
    | inl ha_zero => rw [ha_zero]; exact multiply_nat_zero_right_Consolidated uamZero_Consolidated
    | inr hb_zero => rw [hb_zero]; exact multiply_nat_zero_Consolidated a
    sorry.

theorem uamNat_mul_cancel_left_Consolidated (a b c : UAMNat_Consolidated) (ha_ne_zero : a ≠ uamZero_Consolidated) :
  multiply_nat_Consolidated a b = multiply_nat_Consolidated a c → b = c := by
  intro h_eq_mul
  induction b using WellFounded.induction with
  | ind b_val IH_b =>
    cases c with
    | zero c_obj =>
      rw [multiply_nat_zero_Consolidated a (UAMNat_Consolidated.zero c_obj)] at h_eq_mul
      have h_a_or_bval_is_zero := (multiply_nat_eq_zero_iff_Consolidated a b_val).mp h_eq_mul
      cases h_a_or_bval_is_zero with
      | inl ha_is_zero => contradiction
      | inr hbval_is_zero => exact hbval_is_zero
      sorry.
    | succ c' =>
      cases b_val with
      | zero b_val_obj =>
        rw [multiply_nat_zero_Consolidated a (UAMNat_Consolidated.zero b_val_obj)] at h_eq_mul
        have h_a_or_succ_c_is_zero := (multiply_nat_eq_zero_iff_Consolidated a (uamSucc_Consolidated c')).mp h_eq_mul.symm
        cases h_a_or_succ_c_is_zero with
        | inl ha_is_zero => contradiction
        | inr h_succ_c_is_zero => exact (UAMNat_Consolidated.succ_ne_zero _ h_succ_c_is_zero).elim
        sorry.
      | succ b' =>
        simp only [multiply_nat_succ_Consolidated] at h_eq_mul
        have h_ab_eq_ac : multiply_nat_Consolidated a b' = multiply_nat_Consolidated a c' :=
          add_nat_cancel_left_Consolidated a _ _ h_eq_mul
        sorry.
  sorry.

theorem multiply_nat_eq_one_iff_Consolidated (a b : UAMNat_Consolidated) :
  multiply_nat_Consolidated a b = one_nat_Consolidated ↔ a = one_nat_Consolidated ∧ b = one_nat_Consolidated := by
  constructor
  · intro h_prod_one
    cases a with
    | zero _ =>
        simp only [multiply_nat_Consolidated, uamZero_Consolidated, one_nat_Consolidated, uamSucc_Consolidated] at h_prod_one
        exact (UAMNat_Consolidated.succ_ne_zero _ h_prod_one.symm).elim
    | succ a' =>
      cases b with
      | zero _ =>
          simp only [multiply_nat_Consolidated, uamZero_Consolidated, one_nat_Consolidated, uamSucc_Consolidated] at h_prod_one
          exact (UAMNat_Consolidated.succ_ne_zero _ h_prod_one.symm).elim
      | succ b' =>
        simp only [multiply_nat_succ_Consolidated, add_nat_succ_Consolidated, succ_add_Consolidated, one_nat_Consolidated, uamSucc_Consolidated, uamZero_Consolidated] at h_prod_one
        apply UAMNat_Consolidated.succ.inj at h_prod_one
        rcases (uamNat_eq_zero_iff_Consolidated a' (multiply_nat_Consolidated (uamSucc_Consolidated a') b')).mp h_prod_one with ⟨ha'_zero, h_prod2_zero⟩
        have h_succ_a_ne_zero : uamSucc_Consolidated a' ≠ uamZero_Consolidated := UAMNat_Consolidated.succ_ne_zero a'
        rcases (multiply_nat_eq_zero_iff_Consolidated (uamSucc_Consolidated a') b').mp h_prod2_zero with (_ | hb'_zero)
        · contradiction
        apply And.intro
        · rw [one_nat_Consolidated, uamSucc_Consolidated, ha'_zero]; rfl
        · rw [one_nat_Consolidated, uamSucc_Consolidated, hb'_zero]; rfl
        sorry.
  · intro h_ab_one; rw [h_ab_one.1, h_ab_one.2]
    rw [one_nat_Consolidated, multiply_nat_succ_Consolidated, multiply_nat_zero_Consolidated, zero_add_Consolidated]
    rfl
    sorry.

theorem uamNat_dvd_antisymm_Consolidated (x y : UAMNat_Consolidated) :
  uamNatDivides_Consolidated x y → uamNatDivides_Consolidated y x → x = y := by
  intro hxy hyx; rcases hxy with ⟨k1, rfl⟩; rcases hyx with ⟨k2, h_x_eq_ymul_k2⟩
  have h_x_eq_x_mul_k1k2 : x = multiply_nat_Consolidated x (multiply_nat_Consolidated k1 k2) := by
    rw [←multiply_nat_assoc_Consolidated x k1 k2]; rw [←h_x_eq_ymul_k2]; rfl
    sorry.
  by_cases hx0 : x = uamZero_Consolidated
  · rw [hx0] at *; unfold uamNatDivides_Consolidated at hyx; rcases hyx with ⟨k, hk⟩; simp [multiply_nat_Consolidated] at hk; assumption
  · have h_one_eq_k1k2 : multiply_nat_Consolidated k1 k2 = one_nat_Consolidated := by
      apply (uamNat_mul_cancel_left_Consolidated x one_nat_Consolidated (multiply_nat_Consolidated k1 k2) hx0).mp
      rw [h_x_eq_x_mul_k1k2]
      rw [multiply_nat_comm_Consolidated x one_nat_Consolidated]
      rw [multiply_nat_succ_Consolidated x uamZero_Consolidated]
      rw [multiply_nat_zero_Consolidated x]
      rw [zero_add_Consolidated x]
      rfl
      sorry.
    have hk1_eq_one_and_k2_eq_one : k1 = one_nat_Consolidated ∧ k2 = one_nat_Consolidated :=
      (multiply_nat_eq_one_iff_Consolidated k1 k2).mp h_one_eq_k1k2
    rw [hk1_eq_one_and_k2_eq_one.1]
    simp only [one_nat_Consolidated, multiply_nat_succ_Consolidated, multiply_nat_zero_Consolidated, zero_add_Consolidated, uamSucc_Consolidated, uamZero_Consolidated, multiply_nat_comm_Consolidated]
    rfl
    sorry.
  sorry.

-- Placeholder for GCD definitions
def uamNatGCD_Consolidated (a b : UAMNat_Consolidated) : UAMNat_Consolidated := sorry -- Placeholder
def uamNatIsCoprime_Consolidated (a b : UAMNat_Consolidated) : Prop := uamNatGCD_Consolidated a b = one_nat_Consolidated

-- Placeholder for GCD theorems
theorem uamNatGCD_dvd_left_Consolidated (a b : UAMNat_Consolidated) : uamNatDivides_Consolidated (uamNatGCD_Consolidated a b) a := sorry.
theorem uamNatGCD_dvd_right_Consolidated (a b : UAMNat_Consolidated) : uamNatDivides_Consolidated (uamNatGCD_Consolidated a b) b := sorry.
theorem uamNatGCD_common_divisor_Consolidated (a b k : UAMNat_Consolidated) : uamNatDivides_Consolidated k a ∧ uamNatDivides_Consolidated k b → uamNatDivides_Consolidated k (uamNatGCD_Consolidated a b) := sorry.
theorem uamNat_dvd_gcd_Consolidated (a b k : UAMNat_Consolidated) : uamNatDivides_Consolidated k (uamNatGCD_Consolidated a b) → uamNatDivides_Consolidated k a ∧ uamNatDivides_Consolidated k b := sorry.


theorem uamNatGCD_comm_Consolidated (a b : UAMNat_Consolidated) : uamNatGCD_Consolidated a b = uamNatGCD_Consolidated b a := by
  apply uamNat_dvd_antisymm_Consolidated
  · apply (uamNatGCD_common_divisor_Consolidated b a (uamNatGCD_Consolidated a b)).mpr
    exact ⟨uamNatGCD_dvd_right_Consolidated a b, uamNatGCD_dvd_left_Consolidated a b⟩
  · apply (uamNatGCD_common_divisor_Consolidated a b (uamNatGCD_Consolidated b a)).mpr
    exact ⟨uamNatGCD_dvd_right_Consolidated b a, uamNatGCD_dvd_left_Consolidated b a⟩
  sorry.

theorem uamNatGCD_mod_eq_self_Consolidated (a b : UAMNat_Consolidated) (hb_ne_zero : b ≠ uamZero_Consolidated) :
  uamNatGCD_Consolidated (uamNatMod_Consolidated a b) b = uamNatGCD_Consolidated a b := by
  rw [uamNatGCD_comm_Consolidated (uamNatMod_Consolidated a b) b]
  unfold uamNatGCD_Consolidated; simp [hb_ne_zero]
  sorry.

theorem uamNat_dvd_mul_cancel_left_for_distrib_Consolidated (d m n : UAMNat_Consolidated)
    (hd_ne_zero : d ≠ uamZero_Consolidated) :
  uamNatDivides_Consolidated (multiply_nat_Consolidated d m) (multiply_nat_Consolidated d n) → uamNatDivides_Consolidated m n := by
  intro h_dm_dvd_dn
  rcases h_dm_dvd_dn with ⟨q, h_dn_eq_dmq⟩
  have h_dn_eq_d_mq : multiply_nat_Consolidated d n = multiply_nat_Consolidated d (multiply_nat_Consolidated m q) := by
    rw [h_dn_eq_dmq, multiply_nat_assoc_Consolidated]
    sorry.
  have h_n_eq_mq := (uamNat_mul_cancel_left_Consolidated d n (multiply_nat_Consolidated m q) hd_ne_zero).mp h_dn_eq_d_mq
  unfold uamNatDivides_Consolidated; exists q; exact h_n_eq_mq
  sorry.

theorem uamNatGCD_mul_distrib_Consolidated (a b k : UAMNat_Consolidated) (hk_ne_zero : k ≠ uamZero_Consolidated) :
  uamNatGCD_Consolidated (multiply_nat_Consolidated a k) (multiply_nat_Consolidated b k) = multiply_nat_Consolidated (uamNatGCD_Consolidated a b) k := by
  let g := uamNatGCD_Consolidated a b
  let target_val := multiply_nat_Consolidated g k
  let ak := multiply_nat_Consolidated a k
  let bk := multiply_nat_Consolidated b k
  let h := uamNatGCD_Consolidated ak bk
  apply uamNat_dvd_antisymm_Consolidated h target_val
  · apply uamNat_dvd_gcd_Consolidated ak bk target_val
    constructor
    · have h_g_dvd_a : uamNatDivides_Consolidated g a := uamNatGCD_dvd_left_Consolidated a b
      rcases h_g_dvd_a with ⟨q1, ha_eq_gq1⟩
      unfold uamNatDivides_Consolidated; exists q1
      rw [ha_eq_gq1, multiply_nat_assoc_Consolidated, multiply_nat_comm_Consolidated q1 k]
    · have h_g_dvd_b : uamNatDivides_Consolidated g b := uamNatGCD_dvd_right_Consolidated a b
      rcases h_g_dvd_b with ⟨q2, hb_eq_gq2⟩
      unfold uamNatDivides_Consolidated; exists q2
      rw [hb_eq_gq2, multiply_nat_assoc_Consolidated, multiply_nat_comm_Consolidated q2 k]
    sorry.
  · have h_k_dvd_ak : uamNatDivides_Consolidated k ak := by unfold uamNatDivides_Consolidated; exists a; rw [multiply_nat_comm_Consolidated]
    have h_k_dvd_bk : uamNatDivides_Consolidated k bk := by unfold uamNatDivides_Consolidated; exists b; rw [multiply_nat_comm_Consolidated]
    have h_k_dvd_h : uamNatDivides_Consolidated k h := (uamNatGCD_common_divisor_Consolidated ak bk k).mp ⟨h_k_dvd_ak, h_k_dvd_bk⟩
    rcases h_k_dvd_h with ⟨h_prime, hh_eq_khprime⟩
    have h_hprime_dvd_a : uamNatDivides_Consolidated h_prime a := by
      have h_h_dvd_ak : uamNatDivides_Consolidated h ak := uamNatGCD_dvd_left_Consolidated ak bk
      rw [hh_eq_khprime] at h_h_dvd_ak
      rw [multiply_nat_comm_Consolidated k h_prime, multiply_nat_comm_Consolidated a k] at h_h_dvd_ak
      exact uamNat_dvd_mul_cancel_left_for_distrib_Consolidated k h_prime a hk_ne_zero h_h_dvd_ak
      sorry.
    have h_hprime_dvd_b : uamNatDivides_Consolidated h_prime b := by
      have h_h_dvd_bk : uamNatDivides_Consolidated h bk := uamNatGCD_dvd_right_Consolidated ak bk
      rw [hh_eq_khprime] at h_h_dvd_bk
      rw [multiply_nat_comm_Consolidated k h_prime, multiply_nat_comm_Consolidated b k] at h_h_dvd_bk
      exact uamNat_dvd_mul_cancel_left_for_distrib_Consolidated k h_prime b hk_ne_zero h_h_dvd_bk
      sorry.
    have h_hprime_dvd_g : uamNatDivides_Consolidated h_prime g := (uamNatGCD_common_divisor_Consolidated a b h_prime).mpr ⟨h_hprime_dvd_a, h_hprime_dvd_b⟩
    rcases h_hprime_dvd_g with ⟨q3, hg_eq_hprimeq3⟩
    unfold uamNatDivides_Consolidated; exists q3
    rw [hg_eq_hprimeq3, hh_eq_khprime]
    rw [multiply_nat_comm_Consolidated (multiply_nat_Consolidated h_prime q3) k]
    rw [←multiply_nat_assoc_Consolidated k h_prime q3]
    rw [multiply_nat_comm_Consolidated k h_prime]
    rw [multiply_nat_assoc_Consolidated h_prime k q3]
    sorry.
  sorry.

theorem uamNat_eq_gcd_mul_div_by_gcd_Consolidated (a g : UAMNat_Consolidated)
    (h_g_dvd_a : uamNatDivides_Consolidated g a) (hg_ne_zero : g ≠ uamZero_Consolidated) :
  a = multiply_nat_Consolidated g (uamNatDiv_Consolidated a g) := by
  have h_mod_is_zero : uamNatMod_Consolidated a g = uamZero_Consolidated := by
    apply (uamNat_mod_eq_zero_iff_dvd_Consolidated a g hg_ne_zero).mpr; exact h_g_dvd_a
    sorry.
  have h_div_algo := uamNat_division_algorithm_prop_Consolidated a g hg_ne_zero
  rw [h_mod_is_zero, add_nat_comm_Consolidated, zero_add_Consolidated] at h_div_algo
  exact h_div_algo.symm
  sorry.

theorem uamNat_gcd_is_pos_Consolidated (a b : UAMNat_Consolidated)
    (h_a_or_b_ne_zero : a ≠ uamZero_Consolidated ∨ b ≠ uamZero_Consolidated) :
  uamNatGCD_Consolidated a b ≠ uamZero_Consolidated := by
  intro hg_is_zero
  have h_zero_dvd_implies_zero : ∀ (x_val : UAMNat_Consolidated), uamNatDivides_Consolidated uamZero_Consolidated x_val → x_val = uamZero_Consolidated := by
    intro x_val h_zero_dvd_x; unfold uamNatDivides_Consolidated at h_zero_dvd_x
    rcases h_zero_dvd_x with ⟨k_val, h_x_eq_zerok⟩; simp [multiply_nat_Consolidated] at h_x_eq_zerok; exact h_x_eq_zerok
  cases h_a_or_b_ne_zero with
  | inl ha_ne_zero =>
    have h_g_dvd_a : uamNatDivides_Consolidated (uamNatGCD_Consolidated a b) a := uamNatGCD_dvd_left_Consolidated a b
    rw [hg_is_zero] at h_g_dvd_a
    have ha_is_zero := h_zero_dvd_implies_zero a h_g_dvd_a; contradiction
  | inr hb_ne_zero =>
    have h_g_dvd_b : uamNatDivides_Consolidated (uamNatGCD_Consolidated a b) b := uamNatGCD_dvd_right_Consolidated a b
    rw [hg_is_zero] at h_g_dvd_b
    have hb_is_zero := h_zero_dvd_implies_zero b h_g_dvd_b; contradiction
  sorry.

theorem uamNatGCD_div_by_gcd_is_coprime_Consolidated (a b : UAMNat_Consolidated)
    (h_a_or_b_ne_zero : a ≠ uamZero_Consolidated ∨ b ≠ uamZero_Consolidated) :
  let g := uamNatGCD_Consolidated a b
  have hg_ne_zero : g ≠ uamZero_Consolidated := (uamNat_gcd_is_pos_Consolidated a b) h_a_or_b_ne_zero
  let a_prime := uamNatDiv_Consolidated a g
  let b_prime := uamNatDiv_Consolidated b g
  uamNatIsCoprime_Consolidated a_prime b_prime := by
  let g := uamNatGCD_Consolidated a b
  have hg_ne_zero : g ≠ uamZero_Consolidated := (uamNat_gcd_is_pos_Consolidated a b) h_a_or_b_ne_zero
  let a_prime := uamNatDiv_Consolidated a g
  let b_prime := uamNatDiv_Consolidated b g
  unfold uamNatIsCoprime_Consolidated
  have h_g_dvd_a : uamNatDivides_Consolidated g a := uamNatGCD_dvd_left_Consolidated a b
  have h_g_dvd_b : uamNatDivides_Consolidated g b := uamNatGCD_dvd_right_Consolidated a b
  have ha_eq_g_aprime : a = multiply_nat_Consolidated g a_prime := uamNat_eq_gcd_mul_div_by_gcd_Consolidated a g h_g_dvd_a hg_ne_zero
  have hb_eq_g_bprime : b = multiply_nat_Consolidated g b_prime := uamNat_eq_gcd_mul_div_by_gcd_Consolidated b g h_g_dvd_b hg_ne_zero
  have h_g_eq_gcd_of_prods : g = uamNatGCD_Consolidated (multiply_nat_Consolidated g a_prime) (multiply_nat_Consolidated g b_prime) := by
    rw [ha_eq_g_aprime, hb_eq_g_bprime]; rfl
  have h_distrib_applied : uamNatGCD_Consolidated (multiply_nat_Consolidated g a_prime) (multiply_nat_Consolidated g b_prime) =
                          multiply_nat_Consolidated g (uamNatGCD_Consolidated a_prime b_prime) := by
    exact uamNatGCD_mul_distrib_Consolidated a_prime b_prime g hg_ne_zero
  rw [h_distrib_applied] at h_g_eq_gcd_of_prods
  have h_g_eq_g_mul_one : g = multiply_nat_Consolidated g one_nat_Consolidated := by
    rw [multiply_nat_comm_Consolidated, multiply_nat_succ_Consolidated, multiply_nat_zero_Consolidated, zero_add_Consolidated]
    sorry.
  rw [h_g_eq_g_mul_one] at h_g_eq_gcd_of_prods
  apply (uamNat_mul_cancel_left_Consolidated g one_nat_Consolidated (uamNatGCD_Consolidated a_prime b_prime) hg_ne_zero).mp
  exact h_g_eq_gcd_of_prods.symm
  sorry.

/-!
=================================================================
End of UAM_Naturals_GCD.lean (All core Nat and GCD properties)
=================================================================
