import research.arxiv.«1104.1579».CunninghamJonesLargeDegree
import research.arxiv.«1104.1579».CunninghamJonesSixCertificate
import research.arxiv.«1104.1579».CunninghamJonesPrimePowerDegrees

/-!
# Jones's polynomial question for k = 1

A reducible polynomial gives a coefficient list whose autocorrelations are prescribed by
the trinomial. Its two outer coefficients determine a state in the finite certificate.
Removing endpoints either advances the state or reaches a terminal.
-/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private noncomputable def sixT (N : ℕ) : ℤ[X] :=
  monomial N 1+monomial 1 5+monomial 0 (-6)

private lemma sixT_eq (N : ℕ) : sixT N = X^N+5*X-6 := by
  simp [sixT,← C_mul_X_pow_eq_monomial]
  ring

private def sixSlice (n : ℕ) (v : ℕ → ℤ) := (List.range n).map v
private abbrev sixDot := JonesSix.dot
private def sixEnergy (xs : List ℤ) : ℕ := (xs.map (fun z => z.natAbs^2)).sum

private lemma sixSlice_sum (n : ℕ) (v : ℕ → ℤ) :
    (sixSlice n v).sum = ∑ i ∈ Finset.range n, v i := by
  induction n with
  | zero => simp [sixSlice]
  | succ n ih => simp [sixSlice,List.range_succ,Finset.sum_range_succ] at ih ⊢; exact ih

private lemma sixSlice_ext (n : ℕ) (v u : ℕ → ℤ) (h : ∀ i < n, v i = u i) :
    sixSlice n v = sixSlice n u := by
  apply List.ext_getElem
  · simp [sixSlice]
  · intro i hi _
    simpa [sixSlice] using h i (by simpa [sixSlice] using hi)

private lemma sixSlice_reverse (n : ℕ) (v : ℕ → ℤ) :
    (sixSlice n v).reverse = sixSlice n (fun i => v (n-1-i)) := by
  apply List.ext_getElem
  · simp [sixSlice]
  · intro i h₁ h₂
    simp [sixSlice,List.getElem_reverse]

private lemma sixSlice_drop (k n : ℕ) (v : ℕ → ℤ) :
    (sixSlice n v).drop k = sixSlice (n-k) (fun i => v (k+i)) := by
  apply List.ext_getElem
  · simp [sixSlice]
  · intro i h₁ h₂
    simp [sixSlice]

private lemma sixSlice_add (k n : ℕ) (v : ℕ → ℤ) :
    sixSlice (k+n) v = sixSlice k v ++ sixSlice n (fun i => v (k+i)) := by
  simp only [sixSlice,List.range_add,List.map_append,List.map_map,Function.comp_def]

private lemma sixDot_slices (n m : ℕ) (v u : ℕ → ℤ) :
    sixDot (sixSlice n v) (sixSlice m u) = ∑ i ∈ Finset.range (min n m), v i*u i := by
  rw [← sixSlice_sum]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp [sixSlice]
  · intro i h₁ h₂
    simp [sixSlice]

/-- The low coefficient of the product with its reflection reads from opposite ends. -/
private lemma sixCorr (g : ℤ[X]) (N n : ℕ) (hn : n ≤ N) :
    (g * reflect N g).coeff n =
      ∑ i ∈ Finset.range (n+1), g.coeff (n-i) * g.coeff (N-i) := by
  rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => (reflect N g).coeff i*g.coeff k)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflect,revAt_le ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn),mul_comm]

private lemma sixTrinomialCoeffs (N k : ℕ) (hN : 5 ≤ N) (hk : k ≤ N) :
    (sixT N * reflect N (sixT N)).coeff k =
      if k=0 then -6 else if k=1 then 5 else if k=N-1 then -30 else if k=N then 62 else 0 := by
  have hrev : reflect N (sixT N) =
      monomial 0 1+monomial (N-1) 5+monomial N (-6) := by
    simp only [sixT,← C_mul_X_pow_eq_monomial,reflect_add,reflect_C_mul_X_pow]
    simp [revAt_le (by omega : 1 ≤ N),revAt_le le_rfl]
  rw [hrev]
  simp only [sixT,add_mul,mul_add,monomial_mul_monomial,coeff_add,coeff_monomial]
  simp only [Nat.zero_add,Nat.add_zero,show N+N ≠ k by omega,
    show N+(N-1) ≠ k by omega,show 1+N ≠ k by omega,
    show 1+(N-1) = N by omega,if_false]
  simp only [@eq_comm ℕ 0 k,@eq_comm ℕ 1 k,@eq_comm ℕ (N-1) k,@eq_comm ℕ N k]
  split_ifs <;> omega

private lemma sixSlice_succ (n : ℕ) (v : ℕ → ℤ) :
    sixSlice (n+1) v = sixSlice n v ++ [v n] := by simp [sixSlice,List.range_succ]
private lemma sixSlice_cons (n : ℕ) (v : ℕ → ℤ) :
    sixSlice (n+1) v = v 0 :: sixSlice n (fun i => v (1+i)) := by
  rw [Nat.add_comm n 1,sixSlice_add]
  rfl

-- The two stored prefixes have their innermost coefficients first.
private def sixLow (v : ℕ → ℤ) (n : ℕ) := (sixSlice n v).reverse
private def sixHigh (N : ℕ) (v : ℕ → ℤ) (n : ℕ) := (sixSlice n (fun i => v (N-i))).reverse
private def sixMiddle (N : ℕ) (v : ℕ → ℤ) (n : ℕ) :=
  sixSlice (N+1-n-n) (fun i => v (n+i))

private lemma sixSplit (N n : ℕ) (hn : n+n ≤ N+1) (v : ℕ → ℤ) :
    sixSlice (N+1) v = (sixLow v n).reverse ++ sixMiddle N v n ++ sixHigh N v n := by
  let m := N+1-n-n
  have he : n+m+n=N+1 := by dsimp [m]; omega
  calc
    sixSlice (N+1) v = sixSlice (n+m) v ++ sixSlice n (fun i => v ((n+m)+i)) := he ▸ sixSlice_add _ _ _
    _ = _ := by
      rw [sixSlice_add]
      simp only [sixLow,List.reverse_reverse,sixMiddle,sixHigh]
      rw [sixSlice_reverse]
      apply congrArg (fun z => (sixSlice n v ++ sixSlice m (fun i => v (n+i))) ++ z)
      apply sixSlice_ext
      intro i hi
      congr 1
      dsimp [m]
      omega

private lemma sixMiddle_step (N n : ℕ) (v : ℕ → ℤ) (hn : n+n+2 ≤ N+1) :
    sixMiddle N v n = v n :: (sixMiddle N v (n+1) ++ [v (N-n)]) := by
  let m := N+1-(n+1)-(n+1)
  have he : N+1-n-n=m+1+1 := by dsimp [m]; omega
  unfold sixMiddle
  rw [he,sixSlice_succ,sixSlice_cons]
  simp only [Nat.add_zero,List.cons_append,List.cons.injEq,true_and]
  congr 1
  · apply sixSlice_ext
    intro i hi
    congr 1
    omega
  · dsimp [m]
    congr 2
    omega

private lemma sixPrefix_relation (N n : ℕ) (v : ℕ → ℤ) (hn : 0 < n) (hN : n ≤ N)
    (h₀ : v 0 = 2) (h₁ : v N = -3) :
    ∑ i ∈ Finset.range (n+1), v (n-i)*v (N-i) =
      2*v (N-n)-3*v n+sixDot (sixLow v n) (sixHigh N v n).reverse.tail := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [Nat.sub_self,Nat.sub_zero,h₀,h₁,sixHigh,List.reverse_reverse]
  rw [sixSlice_cons k (fun i => v (N-i)),List.tail_cons]
  simp only [sixLow,sixSlice_reverse,sixDot_slices,Nat.min_eq_right (by omega : k ≤ k+1)]
  have hx : ∑ i ∈ Finset.range k, v (k+1-(i+1))*v (N-(i+1)) =
      ∑ i ∈ Finset.range k, v (k+1-1-i)*v (N-(1+i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm 1 i,show k+1-(i+1)=k+1-1-i by omega]
  linear_combination hx

private lemma sixEnergy_cons (v : ℤ) (a : List ℤ) :
    sixEnergy (v::a) = v.natAbs^2 + sixEnergy a := by simp [sixEnergy]

private lemma sixEnergy_append (a b : List ℤ) :
    sixEnergy (a++b) = sixEnergy a + sixEnergy b := by simp [sixEnergy]

private lemma sixEnergy_cast (a : List ℤ) : (sixEnergy a : ℤ) = sixDot a a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    rw [sixEnergy_cons,Nat.cast_add,Nat.cast_pow,Int.natCast_natAbs,sq_abs,ih]
    simp [sixDot,JonesSix.dot,pow_two]

private lemma sixFull_lag (N h : ℕ) (hh : h ≤ N) (g : ℤ[X]) :
    sixDot (sixSlice (N+1) g.coeff) ((sixSlice (N+1) g.coeff).drop h) =
      (g*reflect N g).coeff (N-h) := by
  rw [sixSlice_drop,sixDot_slices,Nat.min_eq_right (Nat.sub_le ..)]
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => g.coeff i*(reflect N g).coeff k)]
  rw [show N+1-h=N-h+1 by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [coeff_reflect,revAt_le (by omega),show N-(N-h-i)=h+i by omega]

/-- The middle autocorrelation fixes the energy; the three adjacent ones test a terminal. -/
private lemma sixWitness_stats (N : ℕ) (hN : 5 ≤ N) (g : ℤ[X]) (hd : g.natDegree ≤ N)
    (he : g.eval 1 = 0) (hg : g*reflect N g = sixT N*reflect N (sixT N)) :
    let xs := sixSlice (N+1) g.coeff
    xs.sum=0 ∧ sixEnergy xs=62 ∧ sixDot xs (xs.drop 1) = -30 ∧
      sixDot xs (xs.drop 2) = 0 ∧ sixDot xs (xs.drop 3) = 0 := by
  dsimp only
  have hl (k : ℕ) (hk : k ≤ N) :
      sixDot (sixSlice (N+1) g.coeff) ((sixSlice (N+1) g.coeff).drop k) =
      if N-k=0 then -6 else if N-k=1 then 5 else if N-k=N-1 then -30 else if N-k=N then 62 else 0 := by
    rw [sixFull_lag N k hk,hg,sixTrinomialCoeffs N _ hN (Nat.sub_le ..)]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [sixSlice_sum,← he,Polynomial.eval_eq_sum_range' (by omega : g.natDegree < N+1)]
    simp
  · have h := hl 0 (Nat.zero_le _)
    simp only [tsub_zero,List.drop_zero,← sixEnergy_cast] at h
    split_ifs at h <;> omega
  · have h := hl 1 (by omega)
    split_ifs at h <;> omega
  · have h := hl 2 (by omega)
    split_ifs at h <;> omega
  · have h := hl 3 (by omega)
    split_ifs at h <;> omega

private lemma six_terminal_of_short (a b m : List ℤ) (hshort : m.length ≤ 1)
    (hlen : 6 ≤ (a.reverse++m++b).length) (hs : (a.reverse++m++b).sum = 0)
    (h₁ : sixDot (a.reverse++m++b) ((a.reverse++m++b).drop 1) = -30)
    (h₂ : sixDot (a.reverse++m++b) ((a.reverse++m++b).drop 2) = 0)
    (h₃ : sixDot (a.reverse++m++b) ((a.reverse++m++b).drop 3) = 0) :
    JonesSix.terminal (a,b,sixEnergy m) = true := by
  cases m with
  | nil =>
    have hz : -(a.sum+b.sum) = 0 := by simp at hs; omega
    simp only [List.append_nil] at hlen h₁ h₂ h₃
    simp only [JonesSix.terminal,Bool.or_eq_true]
    left
    simp only [sixEnergy,List.map_nil,List.sum_nil,hz,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    tauto
  | cons c rest =>
    have hrest : rest = [] := by simpa using hshort
    subst rest
    have hc : -(a.sum+b.sum) = c := by simp at hs; omega
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hlen h₁ h₂ h₃
    simp only [JonesSix.terminal,Bool.or_eq_true]
    right
    simp only [sixEnergy,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hc,
      Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    tauto

private lemma six_child_mem (a b : List ℤ) (budget : ℕ) (x y : ℤ)
    (hb : budget ≤ 62) (hw : x.natAbs^2+y.natAbs^2 ≤ budget)
    (he : 2*y-3*x = (if a.length=1 then 5 else 0)-sixDot a b.reverse.tail) :
    (x::a,y::b,budget-(x.natAbs^2+y.natAbs^2)) ∈ JonesSix.children (a,b,budget) := by
  have hx : x.natAbs ≤ 7 := by
    by_contra! hn
    have := Nat.pow_le_pow_left (by omega : 8 ≤ x.natAbs) 2
    omega
  have hreg : -7 ≤ x ∧ x ≤ 7 := by omega
  have hcode : (((x+7).toNat : ℕ) : ℤ)-7 = x := by omega
  have hy : (((if a.length=1 then 5 else 0)-sixDot a b.reverse.tail)+3*x)/2 = y := by omega
  unfold JonesSix.children
  apply List.mem_filterMap.mpr
  refine ⟨(x+7).toNat,List.mem_range.mpr (by omega),?_⟩
  simp only [hcode,hy,he,hw,and_self,if_true]

private lemma six_no_polynomial (N : ℕ) (hN : 5 ≤ N) (g : ℤ[X]) (hgdeg : g.natDegree ≤ N)
    (h₀ : g.coeff 0 = 2) (h₁ : g.coeff N = -3) (heval : g.eval 1 = 0)
    (hg : g*reflect N g = sixT N*reflect N (sixT N)) : False := by
  let v := g.coeff
  let xs := sixSlice (N+1) v
  let st (n : ℕ) : JonesSix.State :=
    (sixLow v n,sixHigh N v n,sixEnergy (sixMiddle N v n))
  let Live (s : JonesSix.State) := ∃ n > 0, n+n ≤ N+1 ∧ s=st n
  obtain ⟨hsum,hE,hL₁,hL₂,hL₃⟩ := sixWitness_stats N hN g hgdeg heval hg
  have hlen : 6 ≤ xs.length := by simp [xs,sixSlice]; omega
  have advance (s : JonesSix.State) (hlive : Live s) :
      JonesSix.terminal s = true ∨ ∃ c ∈ JonesSix.children s, Live c := by
    obtain ⟨n,hn,hnN,rfl⟩ := hlive
    let m := sixMiddle N v n
    let a := sixLow v n
    let b := sixHigh N v n
    have hsp : xs = a.reverse++m++b := sixSplit N n hnN v
    have hml : m.length=N+1-n-n := by simp [m,sixMiddle,sixSlice]
    by_cases hshort : m.length ≤ 1
    · left
      apply six_terminal_of_short a b m hshort
      all_goals rw [← hsp]
      all_goals assumption
    · have hlong : n+n+2 ≤ N+1 := by omega
      let x := v n
      let y := v (N-n)
      have hmiddle : m = x :: (sixMiddle N v (n+1) ++ [y]) := sixMiddle_step N n v hlong
      have hmE := congrArg sixEnergy hmiddle
      simp only [sixEnergy_cons,sixEnergy_append,show sixEnergy []=0 from rfl,add_zero] at hmE
      have hbudget : sixEnergy m ≤ 62 := by
        change sixEnergy xs = 62 at hE
        rw [hsp,sixEnergy_append,sixEnergy_append] at hE
        omega
      have hn' : n ≤ N := by omega
      have hcoeff : (g*reflect N g).coeff n = if n=1 then 5 else 0 := by
        rw [hg,sixTrinomialCoeffs N n hN hn']
        simp [show n≠0 by omega,show n≠N-1 by omega,show n≠N by omega]
      rw [sixCorr g N n hn'] at hcoeff
      have hc := sixPrefix_relation N n v hn hn' h₀ h₁
      have hall : 2*y-3*x = (if a.length=1 then 5 else 0)-sixDot a b.reverse.tail := by
        have hal : a.length=n := by simp [a,sixLow,sixSlice]
        rw [hal]
        dsimp only [a,b,x,y,v] at hc ⊢
        linear_combination hc.symm.trans hcoeff
      have mem := six_child_mem a b (sixEnergy m) x y hbudget (by omega) hall
      have hdiff : sixEnergy m - (x.natAbs^2+y.natAbs^2) = sixEnergy (sixMiddle N v (n+1)) := by omega
      have hl : sixLow v (n+1) = x::a := by simp [sixLow,sixSlice_succ,x,a]
      have hh : sixHigh N v (n+1) = y::b := by simp [sixHigh,sixSlice_succ,y,b]
      right
      refine ⟨_,mem,n+1,by omega,by omega,?_⟩
      simp only [st,hl,hh,hdiff]
  have sound (s : JonesSix.State) (h : JonesSix.Excluded s) : ¬Live s := by
    induction h with
    | step nt children ih =>
      intro hL
      rcases advance _ hL with term|⟨child,hm,hchild⟩
      · simp [nt] at term
      · exact ih child hm hchild
  apply sound _ JonesSix.six_certificate
  refine ⟨1,by decide,by omega,?_⟩
  have hl : sixLow v 1 = [2] := by simp [sixLow,sixSlice,List.range_succ,v,h₀]
  have hh : sixHigh N v 1 = [-3] := by simp [sixHigh,sixSlice,List.range_succ,v,h₁]
  have hsp := sixSplit N 1 (by omega) v
  rw [hl,hh] at hsp
  change sixEnergy (sixSlice (N+1) v)=62 at hE
  rw [hsp,sixEnergy_append,sixEnergy_append] at hE
  norm_num [sixEnergy_cons,sixEnergy] at hE
  have h49 : sixEnergy (sixMiddle N v 1)=49 := by dsimp only [sixEnergy]; omega
  simp [st,hl,hh,h49]

/-- Jones's Conjecture 4.1 for its first parameter, k = 1, t = 3 and m = 6. -/
theorem jones_first_parameter_irreducible_iff (j : ℕ) (hj : 2 ≤ j) :
    Irreducible ((jonesSumPolynomial 6 j).map (Int.castRingHom ℚ)) ↔ j ≠ 3 := by
  constructor
  · intro hi h
    subst j
    have hh := (jones_rational_root_iff 3 3 (by decide) (by decide) (by decide)
      (by decide) (-2)).mpr ⟨rfl,rfl⟩
    rw [show jonesConstant 3=6 by decide] at hh
    have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hh)
    rw [natDegree_map_eq_of_injective Int.cast_injective,(jonesSumPolynomial_shape ..).1] at hd
    exact (by decide : (3 : ℕ) ≠ 1) hd
  · intro h3
    by_cases h2 : j=2
    · subst j
      simpa using dyadic_degree_irreducible (m:=6) (by decide) 1
    · by_contra hred
      obtain ⟨g,hd,h₀,h₁,he,hg⟩ := jones_six_factor_witness j (by omega) hred
      exact six_no_polynomial (j+1) (by omega) g hd h₀ h₁ he (by simpa only [sixT_eq] using hg)

#print axioms jones_first_parameter_irreducible_iff

end CunninghamChain
