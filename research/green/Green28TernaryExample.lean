import Green28PrimeOrbitIndex
import Green28BalancedOrbits

/-! Ternary certificates for two uniform integer laws of width sixteen. -/

namespace Green28TernaryExample

open Finset Polynomial Green28 Green28PrimitiveSupport Green28PrimeOrbitIndex

private abbrev Word := List (ZMod 3)

/-- Evaluate a most-significant-first word at a field element. -/
private def value {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) : Word → K
  | [] => 0
  | a::v => algebraMap (ZMod 3) K a*x^v.length+value x v

private def add (a b : Word) := List.zipWith (·+·) a b
private def scale (a : ZMod 3) (b : Word) := b.map (a*·)

private theorem add_len (a b : Word) (len : a.length = b.length) :
    (add a b).length = a.length := by simp [add,len]

private theorem value_add {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (a b : Word)
    (len : a.length = b.length) : value x (add a b) = value x a+value x b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [value,add]
  | cons u a ih =>
    cases b with
    | nil => simp at len
    | cons v b =>
      have h : a.length = b.length := by simpa using len
      simp only [add,List.zipWith_cons_cons,value,List.length_zipWith,h,inf_idem,map_add]
      rw [show value x (List.zipWith (·+·) a b) = value x a+value x b from ih b h];ring

private theorem value_scale {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (a : ZMod 3) (v : Word) :
    value x (scale a v) = algebraMap (ZMod 3) K a*value x v := by
  induction v with
  | nil => simp [scale,value]
  | cons b v ih =>
    change algebraMap _ _ (a*b)*x^(scale a v).length+value x (scale a v) = _
    rw [ih,map_mul];simp only [scale,List.length_map,value];ring

private theorem value_snoc {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (a : Word) :
    value x (a++[0]) = x*value x a := by
  induction a with
  | nil => simp [value]
  | cons v a ih =>
    simp only [List.cons_append,value,List.length_append,List.length_cons,List.length_nil,zero_add,pow_succ,ih]
    ring

/-- Multiplication by the indeterminate using its monic relation. -/
private def shift (h : Word) : Word → Word
  | [] => []
  | a::v => add (v++[0]) (scale a h)

private theorem shift_len (h v : Word) (len : v.length = h.length) :
    (shift h v).length = h.length := by
  cases v with
  | nil => simpa only [shift] using len
  | cons a v => simp [shift,add,scale] at len ⊢;omega

private theorem value_shift {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (h v : Word)
    (root : x^h.length = value x h) (len : v.length = h.length) :
    value x (shift h v) = x*value x v := by
  cases v with
  | nil => simp [shift,value]
  | cons a v =>
    have l : (v++[0]).length = (scale a h).length := by simpa [scale] using len
    rw [shift,value_add _ _ _ l,value_scale,value_snoc,←root,←len]
    simp only [value,List.length_cons,pow_succ];ring

private def accumulate (h b : Word) : Word → Word → Word
  | [], acc => acc
  | a::v, acc => accumulate h b v (add (shift h acc) (scale a b))

private def zeroWord (n : ℕ) : Word := List.replicate n 0
private def product (h a b : Word) := accumulate h b a (zeroWord h.length)

private theorem value_zero {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (n : ℕ) :
    value x (zeroWord n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeroWord,List.replicate_succ,value,map_zero,zero_mul,zero_add];exact ih

private theorem value_accumulate {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (h b a acc : Word)
    (root : x^h.length = value x h) (bl : b.length = h.length) (al : acc.length = h.length) :
    value x (accumulate h b a acc) = value x acc*x^a.length+value x a*value x b := by
  induction a generalizing acc with
  | nil => simp [accumulate,value]
  | cons u v ih =>
    have sl := shift_len h acc al
    have l : (shift h acc).length = (scale u b).length := by simpa [scale] using sl.trans bl.symm
    rw [accumulate,ih _ ((add_len _ _ l).trans sl),value_add _ _ _ l,value_shift _ _ _ root al,value_scale]
    simp only [value,List.length_cons,pow_succ];ring

private theorem value_product {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) (h a b : Word)
    (root : x^h.length = value x h) (bl : b.length = h.length) :
    value x (product h a b) = value x a*value x b := by
  rw [product,value_accumulate _ _ _ _ _ root bl (by simp [zeroWord]),value_zero,zero_mul,zero_add]

private theorem accumulate_len (h b a acc : Word) (bl : b.length = h.length) (al : acc.length = h.length) :
    (accumulate h b a acc).length = h.length := by
  induction a generalizing acc with
  | nil => exact al
  | cons u v ih =>
    have sl := shift_len h acc al
    exact ih _ ((add_len _ _ (by simpa [scale] using sl.trans bl.symm)).trans sl)

private theorem product_len (h a b : Word) (bl : b.length = h.length) :
    (product h a b).length = h.length :=
  accumulate_len h b a _ bl (by simp [zeroWord])

private def unpack : ℕ → ℕ → Word
  | 0, _ => []
  | k+1, n => unpack k (n/3)++[((n%3:ℕ):ZMod 3)]

private theorem unpack_len (k n : ℕ) : (unpack k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [unpack,ih]

private def word := unpack 16
private def relation : Word := [1,2,1,0,0,0,0,0,0,2,1,2,0,2,1,2]

private theorem width (w : ℕ) : (word w).length = relation.length := unpack_len 16 w

private theorem value_one {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) : value x (word 1) = 1 := by
  change value x ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1] : Word) = 1
  simp [value]

private theorem value_x {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K) : value x (word 3) = x := by
  change value x ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0] : Word) = x
  simp [value]

/-- Read the certificate backwards. Each listed residue is for the preceding
binary prefix of the exponent. The final prefix is one. -/
private def checkPower (n w : ℕ) : List ℕ → Bool
  | [] => n==1 && w==3
  | a::tail =>
    let sq := product relation (word a) (word a)
    let next := if n%2 = 0 then sq else shift relation sq
    decide (word w = next) && checkPower (n/2) a tail

private theorem checked_power {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) (n w : ℕ) (steps : List ℕ)
    (ok : checkPower n w steps = true) : value x (word w) = x^n := by
  induction steps generalizing n w with
  | nil =>
    simp only [checkPower,Bool.and_eq_true,beq_iff_eq] at ok
    obtain ⟨rfl,rfl⟩ := ok
    simpa using value_x x
  | cons a tail ih =>
    simp only [checkPower,Bool.and_eq_true,decide_eq_true_eq] at ok
    have prev := ih (n/2) a ok.2
    have sq := value_product x relation (word a) (word a) root (width a)
    rw [prev] at sq
    by_cases even : n%2 = 0
    · rw [ok.1,if_pos even,sq,←pow_add,show n/2+n/2 = n by omega]
    · rw [ok.1,if_neg even,value_shift _ _ _ root (product_len _ _ _ (width a)),sq,←pow_add,
        ←pow_succ',show n/2+n/2+1 = n by omega]

private def checkInverse (w v : ℕ) : Bool :=
  decide (product relation (word w) (word v) = add (word v) (word 1))

private theorem checked_ne_one {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) {w v : ℕ} (ok : checkInverse w v = true) :
    value x (word w) ≠ 1 := by
  intro one
  have words := of_decide_eq_true ok
  have eq := congrArg (value x) words
  rw [value_product _ _ _ _ root (width v),one,one_mul,value_add _ _ _ ((width v).trans (width 1).symm),
    value_one] at eq
  apply one_ne_zero (α:=K)
  linear_combination -eq

set_option maxHeartbeats 3000000 in
/-- Every listed number encodes a degree-below-sixteen residue in base three.
The lists certify powers by squaring. The inverse witnesses certify that the
proper prime-quotient powers differ from one. -/
private theorem signed_order {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) : IsPrimitiveRoot x 10761680 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · have h := checked_power x root 10761680 1
      [2,1570656,1570658,9512394,8027579,42429337,8793639,
        25445565,16993226,12507391,39893377,26954496,10074641,5566559,
        41732483,15233664,42354864,11934775,25632851,59049,243,
        9,3] (by decide +kernel)
    rw [←h,value_one]
  · intro q prime dvd
    have mem := Nat.mem_primeFactors.mpr ⟨prime,dvd,(by decide : (10761680:ℕ) ≠ 0)⟩
    have factors : (10761680:ℕ).primeFactors = {2,5,17,41,193} := by decide +kernel
    simp only [factors,Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · have h := checked_power x root 5380840 2
        [1570656,1570658,9512394,8027579,42429337,8793639,25445565,
        16993226,12507391,39893377,26954496,10074641,5566559,41732483,
        15233664,42354864,11934775,25632851,59049,243,9,
        3] (by decide +kernel)
      exact h ▸ checked_ne_one x root (w:=2) (v:=1) (by decide +kernel)
    · have h := checked_power x root 2152336 10182232
        [12743299,3565392,5746108,4987500,38578298,34347738,36611307,
        8583299,24836195,27578789,41904575,28896815,37524737,32324250,
        1033810,16760660,25511054,6561,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one x root (w:=10182232) (v:=11932231) (by decide +kernel)
    · have h := checked_power x root 633040 31553167
        [27069735,13070866,39047394,31977788,20081263,39391195,9466420,
        12846648,40795260,42044239,21376671,31024656,2949542,22290507,
        14390235,19683,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one x root (w:=31553167) (v:=42040371) (by decide +kernel)
    · have h := checked_power x root 262480 31120573
        [42693866,30865128,37288765,24570984,38117099,24358866,1512324,
        10052181,4798687,5127337,22632108,37545288,16760660,25511054,
        6561,81,9,3] (by decide +kernel)
      exact h ▸ checked_ne_one x root (w:=31120573) (v:=20719370) (by decide +kernel)
    · have h := checked_power x root 55760 11889439
        [29512482,40096167,37582840,32941121,22874305,22248161,19053527,
        18719964,29021134,496999,23997106,1594323,729,27,
        3] (by decide +kernel)
      exact h ▸ checked_ne_one x root (w:=11889439) (v:=4660903) (by decide +kernel)

/-- A ten-site sumset of width sixteen. -/
def sites : Finset ℤ := {0,1,2,4,5,6,13,14,15,16}

private theorem present : (0:ℤ) ∈ sites := by decide

private noncomputable def mask : ℤ[X] := X^16+X^15+X^14+X^13+X^6+X^5+X^4+X^2+X+1

private theorem mask_eq : outputMask sites ⟨0,present⟩=mask := by
  have least : sites.min' ⟨0,present⟩=0 := by
    apply le_antisymm (Finset.min'_le _ _ present)
    apply Finset.le_min'
    intro j hj
    simp only [sites,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  unfold outputMask
  rw [least]
  have img : sites.image (fun z => (z-0).toNat) = ({0,1,2,4,5,6,13,14,15,16}:Finset ℕ) := by decide +kernel
  rw [img]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton,←C_mul_X_pow_eq_monomial,map_one,one_mul,pow_zero,pow_one]
  unfold mask;ring

private theorem mon : mask.Monic := by
  have deg : mask.natDegree = 16 := by unfold mask;compute_degree!
  rw [Monic,leadingCoeff,deg]
  norm_num [mask,coeff_X_pow,coeff_X,coeff_one]

/-- The set itself has a decomposition with both summands nontrivial. -/
theorem support_sumset : sites = ({0,4,13,14}:Finset ℤ).biUnion
    (fun a => ({0,1,2}:Finset ℤ).image (a+·)) := by decide +kernel

private theorem base_root : ∃ x : AlgebraicClosure (ZMod 3), mask.eval₂ (Int.castRingHom _) (-x) = 0 ∧
    x^relation.length = value x relation := by
  classical
  let K := AlgebraicClosure (ZMod 3)
  let M := mask.map (Int.castRingHom K)
  have degree : mask.natDegree = 16 := by unfold mask;compute_degree!
  have degM : M.natDegree = 16 := (mon.natDegree_map _).trans degree
  obtain ⟨a,zero⟩ := IsAlgClosed.exists_root M (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  let x := -a
  have r : mask.eval₂ (Int.castRingHom K) (-x) = 0 := by
    have xa : -x = a := neg_neg a
    rw [xa,←eval_map];exact zero
  have power : x^relation.length = value x relation := by
    have e := r
    simp only [mask,eval₂_add,eval₂_pow,eval₂_X,eval₂_one] at e
    have three : (3:K) = 0 := CharP.cast_eq_zero K 3
    have two : algebraMap (ZMod 3) K (2:ZMod 3) = (2:K) := map_ofNat _ 2
    simp [relation,value,two]
    linear_combination e-(x^14+x^6+x^4+x^2+1)*three
  exact ⟨x,r,power⟩

private theorem site_orbit : PrimeOrbit mask 3 16 10761680 := by
  obtain ⟨x,r,power⟩ := base_root
  have degree : mask.natDegree = 16 := by unfold mask;compute_degree!
  apply primeOrbit_of_root mon degree (by decide) r (signed_order x power)
  decide +kernel

/-- The uniform law on these ten outputs forces a constant input, even
though the output support itself is a sum of two nonconstant supports. -/
theorem pure_of_ten_sites {P Q : PMF ℤ} (sum : indepSum P Q = PMF.uniformOfFinset sites ⟨0,present⟩) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  apply pure_of_prime_index ⟨0,present⟩ sum (p:=3) (d:=16) (n:=10761680) (c:=2)
  · rw [mask_eq];exact site_orbit
  · decide +kernel
  · decide

private theorem binary_exclusion (H : ℤ[X]) (hm : H.Monic) (deg : H.natDegree = 16) (d n : ℕ)
    (root : (H.map (Int.castRingHom (GaloisField 2 d))).eval 1 = 0)
    (one : (H.map (Int.castRingHom (GaloisField 2 d))).coeff 1 = 1) :
    ¬Green28BalancedOrbits.BinaryOrbit H d n := by
  classical
  rintro ⟨α,_,fac⟩
  let K := GaloisField 2 d
  have dd := congrArg natDegree fac
  rw [hm.natDegree_map,deg,natDegree_finsetProd_X_sub_C_eq_card,card_range] at dd
  rw [fac,eval_prod] at root
  obtain ⟨i,_,h⟩ := Finset.prod_eq_zero_iff.mp root
  have ao : α^(2^i) = 1 := (sub_eq_zero.mp (by simpa using h)).symm
  have alpha : α = 1 := (iterateFrobenius K 2 i).injective (by simpa only [iterateFrobenius_def,one_pow] using ao)
  have poly : H.map (Int.castRingHom K) = (X+1 : K[X])^16 := by
    simpa only [alpha,one_pow,map_one,Finset.prod_const,card_range,←dd,CharTwo.sub_eq_add] using fac
  have sq := add_pow_char_pow (X:K[X]) 1 2 4
  norm_num only [one_pow] at sq
  rw [sq] at poly
  have coeff := congrArg (fun F : K[X] => F.coeff 1) poly
  rw [one] at coeff
  norm_num [coeff_X_pow,coeff_one] at coeff

/-- The ten-site mask is outside every binary single-orbit certificate. -/
theorem no_binary_orbit (d n : ℕ) : ¬Green28BalancedOrbits.BinaryOrbit (outputMask sites ⟨0,present⟩) d n := by
  rw [mask_eq]
  apply binary_exclusion mask mon (by unfold mask;compute_degree!) d n
  · simp [mask,CharTwo.add_self_eq_zero]
  · norm_num [mask,Polynomial.map_add,coeff_X_pow,coeff_X,coeff_one]

private def checkEvaluation (z acc : ℕ) : List (ZMod 3 × ℕ) → Bool
  | [] => acc==0
  | (c,w)::tail =>
    decide (add (product relation (word acc) (word z)) (scale c (word 1)) = word w) &&
      checkEvaluation z w tail

private theorem checked_evaluation {K : Type*} [Field K] [Algebra (ZMod 3) K] (x : K)
    (root : x^relation.length = value x relation) (z acc : ℕ) (rows : List (ZMod 3 × ℕ))
    (ok : checkEvaluation z acc rows = true) :
    value x (word acc)*(value x (word z))^rows.length+value (value x (word z)) (rows.map Prod.fst) = 0 := by
  induction rows generalizing acc with
  | nil =>
    simp only [checkEvaluation,beq_iff_eq] at ok
    subst acc
    simp only [List.length_nil,List.map_nil,pow_zero,mul_one,value,add_zero]
    exact value_zero x 16
  | cons row tail ih =>
    obtain ⟨c,w⟩ := row
    simp only [checkEvaluation,Bool.and_eq_true,decide_eq_true_eq] at ok
    have e := congrArg (value x) ok.1
    have len : (product relation (word acc) (word z)).length = (scale c (word 1)).length := by
      rw [product_len _ _ _ (width z)];simpa only [scale,List.length_map] using (width 1).symm
    rw [value_add _ _ _ len,value_product _ _ _ _ root (width z),value_scale,value_one,mul_one] at e
    have h := ih w ok.2
    rw [←e] at h
    simp only [List.map_cons,List.length_cons,value,List.length_map,pow_succ]
    linear_combination h

/-- A fourteen-site sumset of width sixteen. -/
def fourteenSites : Finset ℤ := {0,1,2,4,5,8,9,10,11,12,13,14,15,16}

private theorem fourteenPresent : (0:ℤ) ∈ fourteenSites := by decide

private noncomputable def fourteenMask : ℤ[X] := X^16+X^15+X^14+X^13+X^12+X^11+X^10+X^9+X^8+X^5+X^4+X^2+X+1

private theorem fourteen_mask_eq : outputMask fourteenSites ⟨0,fourteenPresent⟩=fourteenMask := by
  have least : fourteenSites.min' ⟨0,fourteenPresent⟩=0 := by
    apply le_antisymm (Finset.min'_le _ _ fourteenPresent)
    apply Finset.le_min'
    intro j hj
    simp only [fourteenSites,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  unfold outputMask
  rw [least]
  have img : fourteenSites.image (fun z => (z-0).toNat) = ({0,1,2,4,5,8,9,10,11,12,13,14,15,16}:Finset ℕ) := by decide +kernel
  rw [img]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton,←C_mul_X_pow_eq_monomial,map_one,one_mul,pow_zero,pow_one]
  unfold fourteenMask;ring

private theorem fourteenMon : fourteenMask.Monic := by
  have deg : fourteenMask.natDegree = 16 := by unfold fourteenMask;compute_degree!
  rw [Monic,leadingCoeff,deg]
  norm_num [fourteenMask,coeff_X_pow,coeff_X,coeff_one]

/-- The set itself has a decomposition with both summands nontrivial. -/
theorem fourteen_support_sumset : fourteenSites = ({0,1,2,4,5}:Finset ℤ).biUnion
    (fun a => ({0,8,9,10,11}:Finset ℤ).image (a+·)) := by decide +kernel

private theorem fourteen_orbit : PrimeOrbit fourteenMask 3 16 5380840 := by
  let K := AlgebraicClosure (ZMod 3)
  obtain ⟨x,_,root⟩ := base_root
  let y := x^381386
  have ord : IsPrimitiveRoot y 5380840 := IsPrimitiveRoot.iff_orderOf.mpr (by
    dsimp only [y];rw [orderOf_pow' _ (by decide : (381386:ℕ) ≠ 0),
      IsPrimitiveRoot.iff_orderOf.mp (signed_order x root)];decide)
  have yw : value x (word 35304686) = y := checked_power x root 381386 35304686
    [17650149,28629096,27296724,7468866,31777393,34806371,9301538,
      42396323,13353325,41149118,19256558,40502305,14436928,17676567,
      177147,243,9,3] (by decide +kernel)
  let rows : List (ZMod 3 × ℕ) := [(1,1),(2,35304685),(1,1031711),(2,31250282),(1,13121687),(2,1265655),(1,7349370),
      (2,37093448),(1,39062841),(0,3994859),(0,25349123),(2,2499370),(1,25645011),(0,40798118),
      (1,32189957),(2,36657942),(1,0)]
  have ev := checked_evaluation x root 35304686 0 rows (by decide +kernel)
  have zer : value x (word 0) = 0 := value_zero x 16
  have two : algebraMap (ZMod 3) (AlgebraicClosure (ZMod 3)) (2:ZMod 3) = (2:AlgebraicClosure (ZMod 3)) := map_ofNat _ 2
  rw [zer,zero_mul,zero_add,yw] at ev
  simp [rows,value,two] at ev
  have rr : fourteenMask.eval₂ (Int.castRingHom K) (-y) = 0 := by
    simp only [fourteenMask,eval₂_add,eval₂_pow,eval₂_X,eval₂_one]
    have three : (3:K) = 0 := CharP.cast_eq_zero K 3
    linear_combination ev-(y^15+y^13+y^11+y^9+y^5+y)*three
  apply primeOrbit_of_root fourteenMon (by unfold fourteenMask;compute_degree!) (by decide) rr ord
  decide +kernel

/-- The uniform fourteen-site law has a point-mass factor in every independent
decomposition. Its support has a sum representation using two five-site sets. -/
theorem pure_of_fourteen_sites {P Q : PMF ℤ}
    (sum : indepSum P Q = PMF.uniformOfFinset fourteenSites ⟨0,fourteenPresent⟩) :
    (∃ x, P = PMF.pure x) ∨ (∃ y, Q = PMF.pure y) := by
  apply pure_of_prime_index ⟨0,fourteenPresent⟩ sum (p:=3) (d:=16) (n:=5380840) (c:=4)
  · rw [fourteen_mask_eq];exact fourteen_orbit
  · decide +kernel
  · decide

/-- The fourteen-site example also escapes the binary single-orbit test. -/
theorem no_binary_orbit_fourteen (d n : ℕ) :
    ¬Green28BalancedOrbits.BinaryOrbit (outputMask fourteenSites ⟨0,fourteenPresent⟩) d n := by
  rw [fourteen_mask_eq]
  apply binary_exclusion fourteenMask fourteenMon (by unfold fourteenMask;compute_degree!) d n
  · simp [fourteenMask,CharTwo.add_self_eq_zero]
  · norm_num [fourteenMask,Polynomial.map_add,coeff_X_pow,coeff_X,coeff_one]

#print axioms signed_order
#print axioms support_sumset
#print axioms site_orbit
#print axioms pure_of_ten_sites
#print axioms no_binary_orbit
#print axioms fourteen_support_sumset
#print axioms fourteen_orbit
#print axioms pure_of_fourteen_sites
#print axioms no_binary_orbit_fourteen
end Green28TernaryExample
