import Green51GeelenEquality

/-! # Extending partial additive maps in binary spaces -/

namespace Green51SliceStability
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical Pointwise

variable {V : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]

/-- A locally additive binary functional on more than five eighths of the space extends linearly. -/
theorem scalar_extension (H : Finset V) (f : V → F) (zero : 0 ∈ H)
    (dense : 5 * Fintype.card V < 8 * H.card)
    (add : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H → f (x + y) = f x + f y) :
    ∃ l : V →ₗ[F] F, ∀ x ∈ H, l x = f x := by
  classical
  let graph (x : V) : V × F := (x, 1 + f x)
  let D := H.image graph
  have zero_val := add 0 zero 0 zero (by simpa using zero)
  rw [zero_add, ZModModule.add_self] at zero_val
  have nz : (0 : V × F) ∉ D := by
    intro mem
    obtain ⟨x, _, eq⟩ := mem_image.mp mem
    have value : x = 0 := congrArg Prod.fst eq
    have v : 1 + f x = 0 := congrArg Prod.snd eq
    simp [value, zero_val] at v
  have free : ∀ x ∈ D, ∀ y ∈ D, x + y ∉ D := by
    rintro _ hx _ hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    obtain ⟨c, hc, eq⟩ := mem_image.mp hxy
    have first : c = a + b := congrArg Prod.fst eq
    subst c
    have coord : 1 + f (a + b) = (1 + f a) + (1 + f b) := congrArg Prod.snd eq
    rw [add a ha b hb hc, add_add_add_comm (1:F) (f a) 1 (f b), ZModModule.add_self, zero_add] at coord
    simp at coord
  have short (R : Finset (V × F)) (sub : R ⊆ D) (odd : Odd R.card) (sum : (∑ x ∈ R, x) = 0) : 5 ≤ R.card := by
    by_contra! lt
    rw [Nat.odd_iff] at odd
    rcases (show R.card = 1 ∨ R.card = 3 by omega) with one | three
    · obtain ⟨x, rfl⟩ := card_eq_one.mp one
      rw [sum_singleton] at sum
      exact nz (sum ▸ sub (mem_singleton_self x))
    · obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := card_eq_three.mp three
      have hx := sub (mem_insert_self x {y,z})
      have hy := sub (mem_insert_of_mem (mem_insert_self y {z}))
      have hz := sub (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self z)))
      simp only [sum_insert (show x ∉ ({y,z} : Finset (V × F)) by simp [xy,xz]), sum_insert (show y ∉ ({z} : Finset (V × F)) by simpa using yz), sum_singleton] at sum
      apply free x hx y hy
      have val : x + y = z := by
        calc
          x + y = (x + (y + z)) + z := by rw [add_assoc x, add_assoc y, ZModModule.add_self, add_zero]
          _ = z := by rw [sum, zero_add]
      exact val.symm ▸ hz
  have aff : ∃ p : (V × F) →ₗ[F] F, ∀ x ∈ D, p x = 1 := by
    by_contra no
    obtain ⟨C, m⟩ := (choose_circuit D).resolve_left no
    have five := short _ m.1 m.2.1 m.2.2.1
    have rank := circuit_rank m
    have upperRank := Submodule.finrank_le (Submodule.span F (C : Set (V × F)))
    have dim : Module.finrank F (V × F) = Module.finrank F V + 1 := by rw [Module.finrank_prod, Module.finrank_self]
    have upper := geelen_bound D 5 (by decide) short no
    have eq : D.card = H.card := card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
    rw [eq] at upper
    have cardV : Fintype.card V = 2 ^ Module.finrank F V := by rw [Module.card_eq_pow_finrank (K := F)]; simp [F]
    have shifted : Module.finrank F V = (Module.finrank F (V × F) + 1 - 5) + 3 := by omega
    have scale : Fintype.card V = 2 ^ (Module.finrank F (V × F) + 1 - 5) * 8 := by
      conv_lhs => rw [cardV, shifted, pow_add]
      rfl
    omega
  obtain ⟨p, pD⟩ := aff
  have val1 : p (0, (1:F)) = 1 := by simpa [graph, zero_val] using pD _ (mem_image.mpr ⟨_, zero, rfl⟩)
  have coord (a : F) : p (0, a) = a := by
    rcases (show ∀ t : F, t = 0 ∨ t = 1 from by decide) a with rfl | rfl
    · exact p.map_zero
    · exact val1
  refine ⟨p.comp (LinearMap.inl F V F), fun x hx => ?_⟩
  have one := pD _ (mem_image.mpr ⟨x, hx, rfl⟩)
  have split : graph x = (x,0) + (0,1+f x) := by simp [graph]
  rw [split, map_add, coord, add_comm 1, ←add_assoc] at one
  have cancel : p (x,0) + f x = 0 := add_right_cancel (show (p (x,0) + f x) + 1 = 0 + 1 by simpa using one)
  change p (x,0) = f x
  calc
    p (x,0) = (p (x,0) + f x) + f x := by rw [add_assoc, ZModModule.add_self, add_zero]
    _ = f x := by rw [cancel, zero_add]

end Green51SliceStability
#print axioms Green51SliceStability.scalar_extension

namespace Green51SliceStability
open Finset Green53ParityThreshold
open scoped Classical
variable {V E : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module F E] [Module.Finite F E]

/-- Extend a locally additive vector-valued function by extending every scalar coordinate. -/
theorem vector_extension (H : Finset V) (f : V → E) (zero : 0 ∈ H)
    (dense : 5 * Fintype.card V < 8 * H.card)
    (add : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H → f (x + y) = f x + f y) :
    ∃ L : V →ₗ[F] E, ∀ x ∈ H, L x = f x := by
  classical
  let b := Module.Free.chooseBasis F E
  have at_coord (i : Module.Free.ChooseBasisIndex F E) :=
    scalar_extension H (fun x => b.coord i (f x)) zero dense
      (fun x hx y hy hs => by rw [add x hx y hy hs, map_add])
  choose p matchP using at_coord
  refine ⟨b.equivFun.symm.toLinearMap.comp (LinearMap.pi p), fun x hx => ?_⟩
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm _) = b.equivFun (f x)
  rw [b.equivFun.apply_symm_apply]
  exact funext (fun i => matchP i x hx)

end Green51SliceStability
#print axioms Green51SliceStability.vector_extension

namespace Green51SliceStability
open Finset Green53ParityThreshold
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]

/-- Above density one half, every prescribed pair of shifts occurs with its common starting point. -/
theorem three_shifts (H : Finset V) (dense : Fintype.card V < 2 * H.card) (a b : V) :
    ∃ x ∈ H, x + a ∈ H ∧ x + b ∈ H := by
  classical
  by_contra absent
  let bit (x : V) : ℕ := if x ∈ H then 1 else 0
  have cap (x : V) : bit x + bit (x+a) + bit (x+b) + bit (x+a+b) ≤ 2 := by
    have twice (u v : V) : u+v+v = u := by rw [add_assoc, ZModModule.add_self, add_zero]
    have cross : x+b+a = x+a+b := by abel
    have fold : x+a+b+a = x+b := by rw [add_right_comm (x+a) b a, twice]
    have bad (t : V) : ¬ (t ∈ H ∧ t+a ∈ H ∧ t+b ∈ H) := fun h => absent ⟨t,h.1,h.2⟩
    have h0 := bad x
    have h1 := bad (x+a)
    have h2 := bad (x+b)
    have h3 := bad (x+a+b)
    rw [twice] at h1
    rw [cross, twice] at h2
    rw [fold, twice] at h3
    dsimp only [bit]
    split_ifs <;> first | omega | tauto
  have count : ∑ x, bit x = H.card := by simp [bit]
  have translated (v : V) : (∑ x : V, bit (x+v)) = H.card :=
    (Equiv.sum_comp (Equiv.addRight v) bit).trans count
  have bound := sum_le_sum (fun x (_ : x ∈ (univ : Finset V)) => cap x)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at bound
  rw [count, translated a, translated b, show (∑ x : V, bit (x+a+b)) = H.card by
    simpa only [add_assoc] using translated (a+b)] at bound
  norm_cast at bound
  omega

end Green51SliceStability
#print axioms Green51SliceStability.three_shifts

namespace Green51SliceStability
open Finset Green53ParityThreshold
open scoped Classical
variable {V E : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module F E]

/-- A map preserving all four-point additive relations above density one half has linear pair sums. -/
theorem extend_pair_sums (H : Finset V) (f : V → E) (dense : Fintype.card V < 2 * H.card)
    (rect : ∀ a b c d, a ∈ H → b ∈ H → c ∈ H → d ∈ H → a + b = c + d → f a + f b = f c + f d) :
    ∃ L : V →ₗ[F] E, ∀ a b : V, a ∈ H → b ∈ H → L (a+b) = f a + f b := by
  classical
  have pair (u : V) : ∃ x, x ∈ H ∧ x + u ∈ H := by
    obtain ⟨x, hx, hu, _⟩ := three_shifts H dense u u
    exact ⟨x,hx,hu⟩
  choose pt good next using pair
  let calcF (u : V) := f (pt u) + f (pt u + u)
  have rep (a b : V) (ha : a ∈ H) (hb : b ∈ H) : calcF (a + b) = f a + f b := by
    apply rect _ _ _ _ (good _) (next _) ha hb
    rw [←add_assoc, ZModModule.add_self, zero_add]
  let hom : V →+ E := {
    toFun := calcF
    map_zero' := by simp [calcF, ZModModule.add_self]
    map_add' := by
      intro a b
      obtain ⟨x, h0, h1, h2⟩ := three_shifts H dense a (a+b)
      have h3 := rep x (x + a) h0 h1
      have h4 := rep (x + a) (x + (a + b)) h1 h2
      have h5 := rep x (x + (a + b)) h0 h2
      rw [←add_assoc x x, ZModModule.add_self, zero_add] at h3 h5
      have ident : (x + a) + (x + (a + b)) = b := by
        rw [add_add_add_comm, ZModModule.add_self, zero_add, ←add_assoc, ZModModule.add_self, zero_add]
      rw [ident] at h4
      rw [h3, h4, h5, add_assoc, ←add_assoc (f (x + a)), ZModModule.add_self, zero_add] }
  exact ⟨hom.toZModLinearMap 2, fun a b ha hb => rep a b ha hb⟩


end Green51SliceStability
#print axioms Green51SliceStability.extend_pair_sums
