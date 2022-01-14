import topology.basic
import data.real.basic
import topology.continuous_function.basic
import tactic
import topology.instances.real
import Homotopy

open topological_space

namespace Alg_Top

noncomputable theory

variables {X Y: Type} [topological_space X][topological_space Y]
variables a b c d : X

def Path_Composition {a b c: X} (f: Path a b) (g:Path b c) : Path a c:=
begin
  split,
  let Func : ℝ → X := λ s, if s ≤ 2⁻¹ then (f.Func (2*s)) else (g.Func (2*s-1)),
  have Continuity: continuous Func,
  {
    apply continuous.if, continuity,
    have h1 : a_1 ∈ {x : ℝ | x = 2⁻¹},
    {
      apply frontier_le_subset_eq,continuity,
    },
    have h2: a_1 = 2⁻¹ := h1,
    rw h2,
    norm_num, 
    rw f.EndPT,rw g.InitPT,
    exact f.Continuity, exact g.Continuity,
  },
  exact Continuity,simp, 
  exact f.InitPT,simp,split_ifs,
  apply false.elim, norm_num at h,
  norm_num, exact g.EndPT,
end

notation f ∘ g := Path_Composition f g

/-theorem FixPT_Path_is_Group : group Path:=

begin

end-/



theorem Path_Comp_Preserve_Path_Hom {a b c:X} (f f': Path a b)  (g g': Path b c) : 
Path_Homotopic f f' → Path_Homotopic g g' → Path_Homotopic (f ∘ g) (f' ∘ g'):=
begin
  intros fRf' gRg', 
  have Hff' := Path_Homotopy_if_Homotopic fRf',
  have Hgg' := Path_Homotopy_if_Homotopic gRg',
  let Func : ℝ × ℝ → X := λx, if x.snd ≤ 2⁻¹ then (Hff'.Hom.Func (x.fst,2*x.snd)) else (Hgg'.Hom.Func (x.fst,2*x.snd-1)),
  have Continuity: continuous Func,
  {
    apply continuous.if,continuity,
    have h1 : a_1 ∈ {x : ℝ × ℝ | x.snd = 2⁻¹},
    {
      apply frontier_le_subset_eq,continuity,
    },
    have h2: a_1.snd = 2⁻¹,
    {
      exact h1,
    }, rw h2, simp,
    rw Hff'.FixEndPT, rw Hgg'.FixInitPT,
    exact Hff'.Hom.Continuity,
    exact Hgg'.Hom.Continuity,
  }, 
  have InitPT: ∀(x:ℝ), Func (x,0) = a,
  {
    intro x, simp_rw Func, simp only [zero_le_one, inv_nonneg, if_true, zero_le_bit0, mul_zero],
    rw Hff'.FixInitPT,
  },
  have EndPT: ∀(x:ℝ), Func (x,1) = c,
  {
    intro x, simp_rw Func, simp, split_ifs, apply false.elim,
    norm_num at h, norm_num,
    rw Hgg'.FixEndPT,
  },
  split,split,
  rotate,rotate,
  split,exact Continuity, 
  {
    intro x, simp_rw Func, 
    split_ifs, rw Hff'.Hom.InitPT, unfold Path_Composition, 
    simp only,split_ifs,refl,refl, unfold Path_Composition, 
    simp only,split_ifs,simp at h, apply false.elim, norm_num at *,
    nlinarith, rw Hgg'.Hom.InitPT,
  },
  {
    intro x, simp_rw Func, split_ifs, unfold Path_Composition,
    simp only,split_ifs, rw Hff'.Hom.EndPT, rw Hff'.Hom.EndPT,
    unfold Path_Composition, simp only, split_ifs, simp at h, apply false.elim, norm_num at *, linarith,
    rw Hgg'.Hom.EndPT,
  },exact InitPT, exact EndPT,
end

def Inv {a b : X} (f: Path a b) : Path b a :=
begin
  let Func := λ x, f.Func (1-x),
  split, rotate 3, use Func, continuity, exact f.Continuity,
  simp_rw Func,norm_num, exact f.EndPT, simp_rw Func, norm_num, exact f.InitPT,
end

notation f⁻¹ := Inv f

def Id {x: X}: Path x x :=
begin
  let Func := λ h, x,
  split, rotate 3, use Func, continuity, simp_rw Func, simp_rw Func,
end


theorem right_handed_inverse {a b : X} (f: Path a b) : Path_Homotopic (f ∘ f⁻¹) Id :=
begin
  split,split, rotate 2,
  {
    split, rotate 3, 
    let Func := λ x:ℝ × ℝ, if  1/2 * (1-x.1) ≤ x.2 ∧ x.2 ≤ 1 - 1/2 * (1-x.1) then (f ∘ f⁻¹).Func (1/2* (1-x.1))
    else (f ∘ f⁻¹).Func (x.2),
    use Func, simp only, apply continuous.if, continuity, 
    have h : a_1.2 = 1 / 2 * (1-a_1.1) ∨ a_1.2 = 1 - 1 / 2 * (1 - a_1.1),
    {
      left,
      apply frontier_le_subset_eq, continuity, sorry,
      /- Should be trivial-/
    }, cases h, rw h, rw h, simp only [one_div],
    have h1 : ∀x, (f ∘ f⁻¹).Func x = (f ∘ f⁻¹).Func (1-x),
    {
      intro x, unfold Path_Composition, simp only, split_ifs,
      have s1 : x = 1/2,
      {
        norm_num at h_1, norm_num at h_2,
        nlinarith,
      }, rw s1, ring_nf, unfold Inv,simp only,ring_nf,
      unfold Inv, simp only, ring_nf,
      have s2 : x = 1/2,
      {
         norm_num at h_1, norm_num at h_2,
        nlinarith,
      }, rw s2, ring_nf,
    },rw h1, exact (f∘f⁻¹).Continuity,exact (f∘f⁻¹).Continuity,
    simp only, split_ifs, simp only [one_div, mul_one, sub_zero] at h,
    have s1 : x = 1/2,
    {
      norm_num at h, nlinarith,
    }, rw s1, ring_nf, refl, simp only, split_ifs,
    unfold Id, ring, simp only [mul_zero, sub_self], exact (f∘f⁻¹).InitPT, simp at h,apply false.elim,
    have s2: 0≤x := sorry,
    have s3: x≤1 := sorry,
    have s4: 1<x,
    {
      apply h, exact s2,
    },
    nlinarith,
  },
  intro x, simp only, split_ifs,simp at h,
  {
    sorry, /- 1-x can't be negative -/
  }, exact (f∘f⁻¹).InitPT,
  intro x, simp only, split_ifs, simp at h, 
  {
    sorry, /- Same reason -/
  }, exact (f∘f⁻¹).EndPT,
end

theorem left_handed_inverse {a b : X} (f: Path a b) : Path_Homotopic (f⁻¹ ∘ f) Id :=
begin
  sorry,
  /- Basically the same -/
end

theorem right_handed_id {a b : X} (f: Path a b) : Path_Homotopic (f ∘ Id) f :=
begin
  split,split, rotate 2,
  {
    split, rotate 3,
    let Func := λ x:ℝ × ℝ, if x.2 ≤ 1/2*(1 + x.1) then f.Func (2*x.2/(1+x.1)) else f.Func 1,
    use Func, simp only, apply continuous.if, continuity,
    have h: a_1.snd = 1/2 * (1 + a_1.fst),
    {
      apply frontier_le_subset_eq, continuity, 
    },rw h, simp only [one_div, mul_inv_cancel_left₀, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero],
    {
      sorry /- should have a.1 >0 -/
    }, exact f.Continuity,
    {
      sorry /- same -/
    },
    simp only, split_ifs, unfold Path_Composition, simp only, split_ifs, ring_nf, ring_nf,
    norm_num at h_1, simp at h, norm_num at h, apply false.elim, nlinarith,
    unfold Path_Composition,simp only, split_ifs,simp at h, apply false.elim, nlinarith, unfold Id, simp only, exact f.EndPT,
    simp only, split_ifs,ring_nf, simp at h, 
    {
      sorry /- same -/
    },

  },

  intro x,simp only, split_ifs,ring_nf, exact f.InitPT,simp at h,
  {
    sorry /- same -/
  },

  intro x, simp only, split_ifs, ring_nf, simp at h,
  {
    sorry /- same -/
  },
  exact f.EndPT,
end

theorem left_handed_id {a b : X} (f: Path a b) : Path_Homotopic (Id ∘ f) f :=
begin
  sorry,
end

theorem Path_Assoc {a b c d : X} (f: Path a b) (g: Path b c) (h: Path c d) 
: Path_Homotopic ((f ∘ g) ∘ h) (f ∘ (g ∘ h)) :=
begin
  split,split,rotate 2,
  let Func := λ x : ℝ × ℝ, if x.2 ≤ 1/4 * (1+x.1) then f.Func (4*x.2/(1+x.1)) else
  ( if x.2 ≤ 1/4 * (2+x.1) then g.Func (4*(x.2- (1/4 * (1+x.1)))) else h.Func ((x.2-1/4*(2+x.1))/(1-1/4*(2+x.1)))),
  {
    
    split, rotate 3, use Func, apply continuous.if, intros a_1 h1,
    have r1 : a_1.snd = 1/4*(1+a_1.fst),
    {
      apply frontier_le_subset_eq, continuity,
    },rw r1, split_ifs, simp only [one_div, mul_inv_cancel_left₀, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_zero, sub_self],
    {
      sorry, /- same issues -/
    },apply false.elim,
    {
      sorry, 
    },
    {
      sorry,
    },
    {
      apply continuous.if, intros a ha,
      have r2: a.snd = 1/4 * (2+a.fst),
      {
        apply frontier_le_subset_eq, continuity,
      }, rw r2,simp only [one_div, mul_zero, sub_self],norm_num,ring_nf, rw g.EndPT, rw h.InitPT,
      continuity,
      exact g.Continuity, exact h.Continuity,
      {
        sorry,
      },
    }, intro x,unfold Path_Composition,simp_rw Func,simp only [one_div, add_zero, mul_one, div_one],
    split_ifs,ring_nf,
    {
      apply false.elim,simp only [not_le] at h_3, norm_num at h_1 h_3, nlinarith,
    },
    {
      apply false.elim,simp only [not_le] at h_2, norm_num at h_1 h_2, nlinarith,
    },
    {
      apply false.elim,simp only [not_le] at h_1, norm_num at h_1 h_4, nlinarith,
    },
    norm_num,ring_nf,
    {
      apply false.elim,simp only [not_le] at h_3, norm_num at h_2 h_3, nlinarith,
    },
    {
      apply false.elim,simp only [not_le] at h_2, norm_num at h_2 h_3, nlinarith,
    },
    {
      apply false.elim,simp only [not_le] at h_2, norm_num at h_2 h_3, nlinarith,
    },
    norm_num, ring_nf, intro x, simp_rw Func, unfold Path_Composition, simp only [one_div],
    norm_num, ring_nf, split_ifs,refl,refl,
    {
      apply false.elim, simp only [not_le] at h_3, nlinarith,
    },
    {
      apply false.elim, simp only [not_le] at h_1 h_2, nlinarith,
    },refl,
  },
  intro x, simp only,ring_nf,split_ifs, exact f.InitPT,
  {
    apply false.elim, sorry,
  },
  {
    apply false.elim, sorry,
  },
  intro x, simp only, split_ifs,
  {
    apply false.elim, sorry,
  },
  {
    apply false.elim, sorry,
  },
  have h1: (1 - 1 / 4 * (2 + x)) / (1 - 1 / 4 * (2 + x)) = 1,
  {
    sorry,
  }, 
  rw h1, exact h.EndPT,
  

end

theorem Inverse_Homotopic {a b: X} (f g: a ⟶ b) : Path_Homotopic f g → Path_Homotopic f⁻¹ g⁻¹ :=
begin
  intro rHomfg,
  have Homfg : Path_Homotopy f g := Path_Homotopy_if_Homotopic rHomfg,
  split, split, rotate 2,
  {
    split, rotate 3,
    let Func := λ x:ℝ×ℝ, Homfg.Hom.Func (x.1,1-x.2),
    use Func,continuity, exact Homfg.Hom.Continuity, unfold Inv,simp only, rw Homfg.Hom.InitPT,
    unfold Inv, simp only,rw Homfg.Hom.EndPT,
  },simp only, norm_num, intro x, rw Homfg.FixEndPT,
  simp only, norm_num, intro x, rw Homfg.FixInitPT,
end


end Alg_Top

/-
theorem right_handed_inverse {a b : X} (f: Path a b) : Path_Homotopic (f ∘ f⁻¹) Id :=
begin
  split,split, rotate 2,
  {
    split, rotate 3, 
    let Func := λ x:ℝ × ℝ, if  x.2 ≤ 1/2 * (x.1) then f.Func (2 * (x.2)) 
    else (if x.2 ≤ 1 - 1/2*(x.1) then  f.Func (x.1) else f.Func (2*(1-x.2))),
    exact Func, 
    {
      simp only, apply continuous.if,continuity,
      have n1 : a_1.snd = 1/2 * a_1.fst,
      {
        apply frontier_le_subset_eq,continuity,
      }, split_ifs, rw n1,ring_nf,
      rw n1 at h, apply false.elim,
      have t : a_1.fst ≤ 1,
      {
        sorry,
      },linarith, exact f.Continuity,
      apply continuous.if,continuity, 
      have n2 : a_1.snd = 1 - 1 / 2 * a_1.fst,
      {
        apply frontier_le_subset_eq,continuity,
      },
      rw n2, ring_nf, exact f.Continuity,exact f.Continuity,
    },
    {
      intro x, simp only, unfold Path_Composition,split_ifs,refl,simp only at h, norm_num at h, norm_num at h_1,
      apply false.elim, linarith, simp only at h,norm_num at h,
    }
  }

end-/