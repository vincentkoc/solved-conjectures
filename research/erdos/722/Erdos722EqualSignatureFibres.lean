import Erdos722AffineSignatureDual
import Erdos722QuadrupleProduct

/-! # Equal multiplicities of all point signatures in a Steiner quadruple system -/

namespace Erdos722.QuadSwitch
open Finset Function
open scoped Multiset
noncomputable section
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

private def quad (a b c d : V) : Multiset V := a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0
private def allowed (H : Finset (Finset V)) (m : Multiset V) := m.toFinset∈H ∨ ∀ x, Even (m.count x)

def partner (hH : H.IsBlockDesign 3 4) (a b x : V) := (QuadrupleProduct.unique_fourth hH a b x).exists.choose

private theorem allowed_partner (hH : H.IsBlockDesign 3 4) (a b x : V) :
    allowed H (quad a b x (partner hH a b x)) := (QuadrupleProduct.unique_fourth hH a b x).exists.choose_spec

theorem partner_involutive (hH : H.IsBlockDesign 3 4) (a b : V) : Involutive (partner hH a b) := by
  intro x
  let y := partner hH a b x
  have eq : quad a b y x=quad a b x y := by simp only [quad,← Multiset.singleton_add]; ac_rfl
  exact (QuadrupleProduct.unique_fourth hH a b y).unique (allowed_partner hH a b y) (show allowed H (quad a b y x) by rw [eq]; exact allowed_partner hH a b x)

private theorem double_zero {I : Type*} (f : I → ZMod 2) : f+f=0 := funext fun i => CharTwo.add_self_eq_zero (f i)

/-- The permutation pairing completions at two points translates every point
signature by the sum of the signatures at those points. -/
theorem partner_signature (hH : H.IsBlockDesign 3 4) (a b x : V) :
    signature H (partner hH a b x)=signature H a+signature H b+signature H x := by
  classical
  let y := partner hH a b x
  let m := quad a b x y
  have zero : (m.map (signature H)).sum=0 := by
    rcases allowed_partner hH a b x with hb|even
    · have card : m.toFinset.card=m.card := (hH.1 _ hb).trans (by simp [m,quad])
      have eq : m.toFinset.val=m := by rw [Multiset.toFinset_val,(Multiset.toFinset_card_eq_card_iff_nodup.mp card).dedup]
      have h := signature_sum hb
      change (m.toFinset.val.map (signature H)).sum=0 at h
      rwa [eq] at h
    · rw [Finset.sum_multiset_map_count]
      apply sum_eq_zero
      intro v _
      obtain ⟨n,hn⟩ := even v
      change m.count v=n+n at hn
      rw [hn,add_nsmul,double_zero]
  have z : signature H a+signature H b+signature H x+signature H y=0 := by
    simpa [m,quad,add_assoc] using zero
  exact add_right_cancel ((double_zero (signature H y)).trans z.symm)

private theorem swap_label (hH : H.IsBlockDesign 3 4) (o p q x : V) (h : label hH o x=label hH o p) :
    label hH o (partner hH p q x)=label hH o q := by
  have eq : signature H x=signature H p := add_right_cancel (congrArg Subtype.val h)
  apply Subtype.ext
  change signature H (partner hH p q x)+_=signature H q+_
  rw [partner_signature,eq,add_right_comm (signature H p),double_zero,zero_add]

abbrev LabelFibre (hH : H.IsBlockDesign 3 4) (o : V) (u : labelSpace hH o) := {x : V // label hH o x=u}

/-- The intrinsic quotient map is equifibred even when checks do not separate points. -/
def labelFibreEquiv (hH : H.IsBlockDesign 3 4) (o : V) (u v : labelSpace hH o) :
    LabelFibre hH o u ≃ LabelFibre hH o v := by
  let p := (label_surjective hH o u).choose
  let q := (label_surjective hH o v).choose
  have hp : label hH o p=u := (label_surjective hH o u).choose_spec
  have hq : label hH o q=v := (label_surjective hH o v).choose_spec
  rw [← hp,← hq]
  refine { toFun := fun x => ⟨partner hH p q x.val,swap_label hH o p q x.val x.prop⟩,
           invFun := fun y => ⟨partner hH p q y.val,?_⟩,
           left_inv := fun x => Subtype.ext (partner_involutive hH p q x.val),
           right_inv := fun y => Subtype.ext (partner_involutive hH p q y.val) }
  have eq : signature H y.val=signature H q := add_right_cancel (congrArg Subtype.val y.prop)
  apply Subtype.ext
  change signature H (partner hH p q y.val)+_=signature H p+_
  rw [partner_signature,eq,add_assoc (signature H p) (signature H q) (signature H q),double_zero,add_zero]

def labelProduct (hH : H.IsBlockDesign 3 4) (o : V) : V ≃ labelSpace hH o × LabelFibre hH o 0 :=
  (Equiv.sigmaFiberEquiv (label hH o)).symm.trans ((Equiv.sigmaCongrRight (fun u => labelFibreEquiv hH o u 0)).trans
    (Equiv.sigmaEquivProd _ _))

theorem labelProduct_fst (hH : H.IsBlockDesign 3 4) (o x : V) : (labelProduct hH o x).1=label hH o x := rfl

#print axioms partner
#print axioms partner_involutive
#print axioms partner_signature
#print axioms LabelFibre
#print axioms labelFibreEquiv
#print axioms labelProduct
#print axioms labelProduct_fst
end
end Erdos722.QuadSwitch
