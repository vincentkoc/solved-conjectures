import OMAReductions.R_Erdos78_erdos_78_R1

-- Step Erdos78.erdos_78.R1.H3: hypothesis H3 of reduction Erdos78.erdos_78.R1
-- Credit: @vincentkoc
-- H3: (xs, u, v) ↦ (List.replicate (2 ^ Nat.size xs.length) true, u, v) is polynomial time.
-- A hand-built five-stack TM2 machine. The step-budget bookkeeping (`RIn`) follows the
-- style of @adammcarter's padding machine for the strongly explicit variant.

open ComplexityTheory
open Turing Computability

namespace Erdos78R1Pad

-- Reachability within a step budget.

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

-- The machine. Stack `M` holds input and output; `A`, `B` halve the element count,
-- `C`, `D` double a unary counter.

inductive Stk | M | A | B | C | D
  deriving DecidableEq

instance : Fintype Stk :=
  ⟨{.M, .A, .B, .C, .D}, by intro x; cases x <;> simp⟩

inductive Lab | p0 | p1 | p2 | chk | h | pB | dbl | pD | o0 | o
  deriving DecidableEq

instance : Fintype Lab :=
  ⟨{.p0, .p1, .p2, .chk, .h, .pB, .dbl, .pD, .o0, .o}, by intro x; cases x <;> simp⟩

abbrev G : Stk → Type := fun _ => Bool

abbrev St := TM2.Stmt G Lab (Option Bool)

def popS (k : Stk) (q : St) : St := .pop k (fun _ o => o) q
def pushS (k : Stk) (b : Bool) (q : St) : St := .push k (fun _ => b) q
def ifS (q₁ q₂ : St) : St := .branch (fun v => v.isSome) q₁ q₂

def prog : Lab → St
  | .p0 => popS .M <| .branch (fun v => v == some true)
      (popS .M <| pushS .A true <| .goto fun _ => .p1)
      (pushS .C true <| .goto fun _ => .chk)
  | .p1 => popS .M <| popS .M <| .goto fun _ => .p2
  | .p2 => popS .M <| popS .M <| .goto fun _ => .p0
  | .chk => .peek .A (fun _ o => o) <| ifS (.goto fun _ => .h) (.goto fun _ => .o0)
  | .h => popS .A <| ifS
      (popS .A <| ifS (pushS .B true <| .goto fun _ => .h) (.goto fun _ => .pB))
      (.goto fun _ => .pB)
  | .pB => popS .B <| ifS (pushS .A true <| .goto fun _ => .pB) (.goto fun _ => .dbl)
  | .dbl => popS .C <| ifS (pushS .D true <| pushS .D true <| .goto fun _ => .dbl)
      (.goto fun _ => .pD)
  | .pD => popS .D <| ifS (pushS .C true <| .goto fun _ => .pD) (.goto fun _ => .chk)
  | .o0 => pushS .M false <| .goto fun _ => .o
  | .o => popS .C <| ifS
      (pushS .M false <| pushS .M true <| pushS .M true <| pushS .M true <| pushS .M true <|
        pushS .M true <| .goto fun _ => .o)
      (.load (fun _ => none) .halt)

def N : FinTM2 :=
  { K := Stk
    k₀ := .M
    k₁ := .M
    Γ := G
    Λ := Lab
    main := .p0
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

def mk (m a b c d : List Bool) : ∀ k : Stk, List (G k)
  | .M => m
  | .A => a
  | .B => b
  | .C => c
  | .D => d

@[simp] lemma upd_M (m a b c d x : List Bool) :
    Function.update (mk m a b c d) Stk.M x = mk x a b c d := by
  funext k; cases k <;> simp [Function.update, mk]
@[simp] lemma upd_A (m a b c d x : List Bool) :
    Function.update (mk m a b c d) Stk.A x = mk m x b c d := by
  funext k; cases k <;> simp [Function.update, mk]
@[simp] lemma upd_B (m a b c d x : List Bool) :
    Function.update (mk m a b c d) Stk.B x = mk m a x c d := by
  funext k; cases k <;> simp [Function.update, mk]
@[simp] lemma upd_C (m a b c d x : List Bool) :
    Function.update (mk m a b c d) Stk.C x = mk m a b x d := by
  funext k; cases k <;> simp [Function.update, mk]
@[simp] lemma upd_D (m a b c d x : List Bool) :
    Function.update (mk m a b c d) Stk.D x = mk m a b c x := by
  funext k; cases k <;> simp [Function.update, mk]

@[simp] lemma mk_M (m a b c d : List Bool) : mk m a b c d Stk.M = m := rfl
@[simp] lemma mk_A (m a b c d : List Bool) : mk m a b c d Stk.A = a := rfl
@[simp] lemma mk_B (m a b c d : List Bool) : mk m a b c d Stk.B = b := rfl
@[simp] lemma mk_C (m a b c d : List Bool) : mk m a b c d Stk.C = c := rfl
@[simp] lemma mk_D (m a b c d : List Bool) : mk m a b c d Stk.D = d := rfl

def cfg (l : Option Lab) (v : Option Bool) (m a b c d : List Bool) : N.Cfg :=
  ⟨l, v, mk m a b c d⟩

lemma step_eq (l : Lab) (v : Option Bool) (m a b c d : List Bool) :
    N.step (cfg (some l) v m a b c d) = some (TM2.stepAux (prog l) v (mk m a b c d)) := rfl


-- Single steps.

lemma s_p0_t (v : Option Bool) (x : Bool) (m a : List Bool) :
    N.step (cfg (some .p0) v (true :: x :: m) a [] [] []) =
      some (cfg (some .p1) (some x) m (true :: a) [] [] []) := by
  rw [step_eq]; simp [prog, popS, pushS, TM2.stepAux, cfg]
  rfl

lemma s_p0_f (v : Option Bool) (m a : List Bool) :
    N.step (cfg (some .p0) v (false :: m) a [] [] []) =
      some (cfg (some .chk) (some false) m a [] [true] []) := by
  rw [step_eq]; simp [prog, popS, pushS, TM2.stepAux, cfg]
  rfl

lemma s_p1 (v : Option Bool) (x y : Bool) (m a : List Bool) :
    N.step (cfg (some .p1) v (x :: y :: m) a [] [] []) =
      some (cfg (some .p2) (some y) m a [] [] []) := by
  rw [step_eq]; simp [prog, popS, TM2.stepAux, cfg]
  rfl

lemma s_p2 (v : Option Bool) (x y : Bool) (m a : List Bool) :
    N.step (cfg (some .p2) v (x :: y :: m) a [] [] []) =
      some (cfg (some .p0) (some y) m a [] [] []) := by
  rw [step_eq]; simp [prog, popS, TM2.stepAux, cfg]
  rfl

lemma s_chk_cons (v : Option Bool) (m a c : List Bool) :
    N.step (cfg (some .chk) v m (true :: a) [] c []) =
      some (cfg (some .h) (some true) m (true :: a) [] c []) := by
  rw [step_eq]; simp [prog, ifS, TM2.stepAux, cfg]
  rfl

lemma s_chk_nil (v : Option Bool) (m c : List Bool) :
    N.step (cfg (some .chk) v m [] [] c []) =
      some (cfg (some .o0) none m [] [] c []) := by
  rw [step_eq]; simp [prog, ifS, TM2.stepAux, cfg]
  rfl

lemma s_h_nil (v : Option Bool) (m b c : List Bool) :
    N.step (cfg (some .h) v m [] b c []) = some (cfg (some .pB) none m [] b c []) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_h_one (v : Option Bool) (m b c : List Bool) :
    N.step (cfg (some .h) v m [true] b c []) = some (cfg (some .pB) none m [] b c []) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_h_two (v : Option Bool) (m a b c : List Bool) :
    N.step (cfg (some .h) v m (true :: true :: a) b c []) =
      some (cfg (some .h) (some true) m a (true :: b) c []) := by
  rw [step_eq]; simp [prog, popS, pushS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_pB_cons (v : Option Bool) (m a b c : List Bool) :
    N.step (cfg (some .pB) v m a (true :: b) c []) =
      some (cfg (some .pB) (some true) m (true :: a) b c []) := by
  rw [step_eq]; simp [prog, popS, pushS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_pB_nil (v : Option Bool) (m a c : List Bool) :
    N.step (cfg (some .pB) v m a [] c []) = some (cfg (some .dbl) none m a [] c []) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_dbl_cons (v : Option Bool) (m a c d : List Bool) :
    N.step (cfg (some .dbl) v m a [] (true :: c) d) =
      some (cfg (some .dbl) (some true) m a [] c (true :: true :: d)) := by
  rw [step_eq]; simp [prog, popS, pushS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_dbl_nil (v : Option Bool) (m a d : List Bool) :
    N.step (cfg (some .dbl) v m a [] [] d) = some (cfg (some .pD) none m a [] [] d) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_pD_cons (v : Option Bool) (m a c d : List Bool) :
    N.step (cfg (some .pD) v m a [] c (true :: d)) =
      some (cfg (some .pD) (some true) m a [] (true :: c) d) := by
  rw [step_eq]; simp [prog, popS, pushS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_pD_nil (v : Option Bool) (m a c : List Bool) :
    N.step (cfg (some .pD) v m a [] c []) = some (cfg (some .chk) none m a [] c []) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_o0 (v : Option Bool) (m c : List Bool) :
    N.step (cfg (some .o0) v m [] [] c []) = some (cfg (some .o) v (false :: m) [] [] c []) := by
  rw [step_eq]; simp [prog, pushS, TM2.stepAux, cfg]
  rfl

lemma s_o_cons (v : Option Bool) (m c : List Bool) :
    N.step (cfg (some .o) v m [] [] (true :: c) []) =
      some (cfg (some .o) (some true) (true :: true :: true :: true :: true :: false :: m)
        [] [] c []) := by
  rw [step_eq]; simp [prog, popS, pushS, ifS, TM2.stepAux, cfg]
  rfl

lemma s_o_nil (v : Option Bool) (m : List Bool) :
    N.step (cfg (some .o) v m [] [] [] []) = some (cfg none none m [] [] [] []) := by
  rw [step_eq]; simp [prog, popS, ifS, TM2.stepAux, cfg]
  rfl


-- The phases.

def blk : List Bool → List Bool
  | [] => [false]
  | b :: xs => true :: true :: true :: b :: true :: false :: blk xs

def chunk : List Bool := [true, true, true, true, true, false]

def outs (n : ℕ) : List Bool := (List.replicate n chunk).flatten

lemma replicate_true_cons_comm (n : ℕ) (l : List Bool) : ((List.replicate n true)) ++ true :: l = true :: (((List.replicate n true)) ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

lemma parse_run (xs t a : List Bool) (v : Option Bool) :
    RIn N.step (cfg (some .p0) v (blk xs ++ t) a [] [] [])
      (some (cfg (some .chk) (some false) t (((List.replicate xs.length true)) ++ a) [] [true] []))
      (3 * xs.length + 1) := by
  induction xs generalizing a v with
  | nil => simpa [blk] using RIn.single (s_p0_f v t a)
  | cons b xs ih =>
    have h1 := RIn.single (s_p0_t v true (true :: b :: true :: false :: (blk xs ++ t)) a)
    have h2 := RIn.single (s_p1 (some true) true b (true :: false :: (blk xs ++ t)) (true :: a))
    have h3 := RIn.single (s_p2 (some b) true false (blk xs ++ t) (true :: a))
    have h4 := ih (true :: a) (some false)
    have := RIn.trans (RIn.trans (RIn.trans h1 h2) h3) h4
    simp only [blk, List.cons_append, List.length_cons, List.replicate_succ, replicate_true_cons_comm] at this ⊢
    exact this.mono (by omega)

lemma halve_run (m b c : List Bool) (n : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .h) v m ((List.replicate n true)) b c [])
      (some (cfg (some .pB) none m [] (((List.replicate (n / 2) true)) ++ b) c [])) (n / 2 + 1) := by
  induction n using Nat.strong_induction_on generalizing b v with
  | _ n ih =>
    match n with
    | 0 => simpa using RIn.single (s_h_nil v m b c)
    | 1 => simpa using RIn.single (s_h_one v m b c)
    | k + 2 =>
      have h1 := RIn.single (s_h_two v m ((List.replicate k true)) b c)
      have h2 := ih k (by omega) (true :: b) (some true)
      have := RIn.trans h1 h2
      have e : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [e]
      simp only [List.replicate_succ, replicate_true_cons_comm, List.cons_append] at this ⊢
      exact this.mono (by omega)

lemma pourB_run (m a c : List Bool) (n : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .pB) v m a ((List.replicate n true)) c [])
      (some (cfg (some .dbl) none m (((List.replicate n true)) ++ a) [] c [])) (n + 1) := by
  induction n generalizing a v with
  | zero => simpa using RIn.single (s_pB_nil v m a c)
  | succ n ih =>
    have := RIn.trans (RIn.single (s_pB_cons v m a ((List.replicate n true)) c)) (ih (true :: a) (some true))
    simp only [List.replicate_succ, replicate_true_cons_comm, List.cons_append] at this ⊢
    exact this.mono (by omega)

lemma dbl_run (m a d : List Bool) (n : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .dbl) v m a [] ((List.replicate n true)) d)
      (some (cfg (some .pD) none m a [] [] (((List.replicate (2 * n) true)) ++ d))) (n + 1) := by
  induction n generalizing d v with
  | zero => simpa using RIn.single (s_dbl_nil v m a d)
  | succ n ih =>
    have := RIn.trans (RIn.single (s_dbl_cons v m a ((List.replicate n true)) d)) (ih (true :: true :: d) (some true))
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e]
    simp only [List.replicate_succ, replicate_true_cons_comm, List.cons_append] at this ⊢
    exact this.mono (by omega)

lemma pD_run (m a c : List Bool) (n : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .pD) v m a [] c ((List.replicate n true)))
      (some (cfg (some .chk) none m a [] (((List.replicate n true)) ++ c) [])) (n + 1) := by
  induction n generalizing c v with
  | zero => simpa using RIn.single (s_pD_nil v m a c)
  | succ n ih =>
    have := RIn.trans (RIn.single (s_pD_cons v m a c ((List.replicate n true)))) (ih (true :: c) (some true))
    simp only [List.replicate_succ, replicate_true_cons_comm, List.cons_append] at this ⊢
    exact this.mono (by omega)

lemma outs_succ (n : ℕ) : outs (n + 1) = outs n ++ chunk := by
  simp [outs, List.replicate_succ']

lemma out_run (m : List Bool) (n : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .o) v m [] [] ((List.replicate n true)) [])
      (some (cfg none none (outs n ++ m) [] [] [] [])) (n + 1) := by
  induction n generalizing m v with
  | zero => simpa [outs] using RIn.single (s_o_nil v m)
  | succ n ih =>
    have := RIn.trans (RIn.single (s_o_cons v m ((List.replicate n true)))) (ih _ (some true))
    rw [outs_succ, List.replicate_succ, List.append_assoc]
    exact this.mono (by omega)

lemma blk_rep (n : ℕ) : blk ((List.replicate n true)) = outs n ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, blk, ih, outs, chunk]

lemma size_half {a : ℕ} (ha : 0 < a) : Nat.size a = Nat.size (a / 2) + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (a / 2)
    omega
  · rw [Nat.succ_le, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (Nat.size (a / 2)) with h0 | hpos
    · rw [h0]; simp; omega
    · have h := Nat.lt_size.mp (show Nat.size (a / 2) - 1 < Nat.size (a / 2) by omega)
      have e : 2 ^ Nat.size (a / 2) = 2 * 2 ^ (Nat.size (a / 2) - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega

lemma round_run (t : List Bool) (a c : ℕ) (v : Option Bool) (ha : 0 < a) :
    RIn N.step (cfg (some .chk) v t ((List.replicate a true)) [] ((List.replicate c true)) [])
      (some (cfg (some .chk) none t ((List.replicate (a / 2) true)) [] ((List.replicate (2 * c) true)) [])) (a + 3 * c + 5) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have h0 := RIn.single (s_chk_cons v t ((List.replicate a' true)) ((List.replicate c true)))
  have h1 := halve_run t [] ((List.replicate c true)) (a' + 1) (some true)
  have h2 := pourB_run t [] ((List.replicate c true)) ((a' + 1) / 2) none
  have h3 := dbl_run t (((List.replicate ((a' + 1) / 2) true)) ++ []) [] c none
  have h4 := pD_run t (((List.replicate ((a' + 1) / 2) true)) ++ []) [] (2 * c) none
  simp only [List.append_nil] at h1 h2 h3 h4
  have := RIn.trans (RIn.trans (RIn.trans (RIn.trans h0 (by simpa [List.replicate_succ] using h1))
    h2) h3) h4
  exact this.mono (by omega)

lemma loop_run (t : List Bool) (a c : ℕ) (v : Option Bool) :
    RIn N.step (cfg (some .chk) v t ((List.replicate a true)) [] ((List.replicate c true)) [])
      (some (cfg (some .o0) none t [] [] ((List.replicate (c * 2 ^ Nat.size a) true)) []))
      ((Nat.size a + 1) * (a + 3 * (c * 2 ^ Nat.size a) + 6)) := by
  induction a using Nat.strong_induction_on generalizing c v with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [List.replicate_zero, Nat.size_zero, pow_zero, mul_one]
      exact (RIn.single (s_chk_nil v t ((List.replicate c true)))).mono (by omega)
    · have h1 := round_run t a c v ha
      have h2 := ih (a / 2) (by omega) (2 * c) none
      have hs := size_half ha
      set s := Nat.size (a / 2) with hsdef
      have e : 2 * c * 2 ^ s = c * 2 ^ Nat.size a := by rw [hs, pow_succ]; ring
      rw [e] at h2
      refine (RIn.trans h1 h2).mono ?_
      rw [hs]
      set X := c * 2 ^ (s + 1) with hX
      have hcX : c ≤ X := by
        rw [hX]; exact Nat.le_mul_of_pos_right c (by positivity)
      have hK : a / 2 + 3 * X + 6 ≤ a + 3 * X + 6 := by omega
      have hm := Nat.mul_le_mul_left (s + 1) hK
      have e2 : (s + 1 + 1) * (a + 3 * X + 6) = (s + 1) * (a + 3 * X + 6) + (a + 3 * X + 6) := by
        ring
      rw [e2]
      omega

lemma initList_N (l : List Bool) : initList N l = cfg (some .p0) none l [] [] [] [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_N (l : List Bool) : haltList N l = cfg none none l [] [] [] [] := by
  simp only [haltList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma full_run (xs t : List Bool) :
    RIn N.step (initList N (blk xs ++ t))
      (some (haltList N (blk ((List.replicate (2 ^ Nat.size xs.length) true)) ++ t)))
      (3 * xs.length + 1 + (Nat.size xs.length + 1) *
        (xs.length + 3 * (2 ^ Nat.size xs.length) + 6) + 1 + (2 ^ Nat.size xs.length + 1)) := by
  rw [initList_N, haltList_N]
  have h1 := parse_run xs t [] none
  have h2 := loop_run t xs.length 1 (some false)
  have h3 := RIn.single (s_o0 none t ((List.replicate (1 * 2 ^ Nat.size xs.length) true)))
  have h4 := out_run (false :: t) (1 * 2 ^ Nat.size xs.length) none
  simp only [List.append_nil] at h1
  have := RIn.trans (RIn.trans (RIn.trans h1 (by simpa using h2)) h3) h4
  simp only [one_mul] at this
  rw [blk_rep]
  simpa [List.append_assoc] using this

lemma blk_eq (xs : List Bool) :
    BitstringEncoding.delimit
      (((xs.map fun b => [b]).map BitstringEncoding.delimit).flatten) = blk xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    show BitstringEncoding.delimit (BitstringEncoding.delimit [b] ++
      ((xs.map fun b => [b]).map BitstringEncoding.delimit).flatten) = _
    simp only [BitstringEncoding.delimit, List.cons_append, List.nil_append, blk, ih]

end Erdos78R1Pad

namespace Erdos78R1Pad

lemma length_blk (xs : List Bool) : (blk xs).length = 6 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [blk, ih]; ring

lemma two_pow_size_le (L : ℕ) : 2 ^ Nat.size L ≤ 2 * L + 1 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · have hpos : 0 < Nat.size L := Nat.size_pos.mpr hL
    have h := Nat.lt_size.mp (show Nat.size L - 1 < Nat.size L by omega)
    have e : 2 ^ Nat.size L = 2 * 2 ^ (Nat.size L - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

lemma size_le_self (L : ℕ) : Nat.size L ≤ L := Nat.size_le.mpr (Nat.lt_two_pow_self)

end Erdos78R1Pad

open Erdos78R1Pad in
/-- Unary padding of the first slot to the next power of two is polynomial time. -/
theorem erdos78_unaryPad_polyTime :
    IsPolyTime (fun x : List Bool × ℕ × ℕ =>
      (List.replicate (2 ^ Nat.size x.1.length) true, x.2)) := by
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 7 * (Polynomial.X + 2) ^ 2
            outputsFun := fun x => ?_ }⟩
  obtain ⟨xs, r⟩ := x
  set t := BitstringEncoding.bitEncode r with ht
  have henc : (BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (xs, r) =
      blk xs ++ t := by
    rw [← blk_eq]; rfl
  have hout : (BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode
      (List.replicate (2 ^ Nat.size xs.length) true, r) =
      blk (List.replicate (2 ^ Nat.size xs.length) true) ++ t := by
    rw [← blk_eq]; rfl
  have hn : ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (xs, r)).length =
      6 * xs.length + 1 + t.length := by
    rw [henc, List.length_append, length_blk]
  set L := xs.length with hLdef
  have hb : 3 * L + 1 + (Nat.size L + 1) * (L + 3 * 2 ^ Nat.size L + 6) + 1 +
      (2 ^ Nat.size L + 1) ≤ (7 * (Polynomial.X + 2) ^ 2 : Polynomial ℕ).eval
        ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (xs, r)).length := by
    rw [hn]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    have hs := size_le_self L
    have hP := two_pow_size_le L
    have hm : (Nat.size L + 1) * (L + 3 * 2 ^ Nat.size L + 6) ≤ (L + 1) * (7 * L + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    set n := 6 * L + 1 + t.length
    have hLn : L ≤ n := by omega
    nlinarith
  have key : ∀ l l' : List Bool, l = blk xs ++ t →
      l' = blk (List.replicate (2 ^ Nat.size L) true) ++ t →
      TM2OutputsInTime N l (some l')
        ((7 * (Polynomial.X + 2) ^ 2 : Polynomial ℕ).eval
          ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (xs, r)).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := (full_run xs t).mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ (by rw [henc]; exact List.map_id _) (by rw [hout]; exact List.map_id _)

theorem OMA.solution : OMA.R_Erdos78_erdos_78_R1.H3 :=
  erdos78_unaryPad_polyTime
