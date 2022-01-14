import topology.basic
import data.real.basic
import topology.continuous_function.basic
import tactic
import topology.instances.real
import Homotopy
import Path

open topological_space

noncomputable theory

namespace Alg_Top

variables {X Y: Type} [topological_space X][topological_space Y]
variables {x₀ : X}

instance loop_setoid : setoid (Path x₀ x₀) :=
begin
    split, rotate 1,
    use Path_Homotopic, apply @Path_Hom_Equiv,
end

def π₁ (x₀:X):= quotient (@Alg_Top.loop_setoid X _ x₀)
def foo : Path x₀ x₀ := Id

@[simp] lemma equiv_def (x y : Path x₀ x₀) : x ≈ y ↔ Path_Homotopic x y:=
begin
  refl
end

#check ⟦foo⟧
#check foo
#check π₁



example (x y : x₀ ⟶ x₀) : x ≈ y → ⟦x⟧ = ⟦y⟧ :=
quotient.sound

example (x y : x₀ ⟶ x₀) : ⟦x⟧ = ⟦y⟧ → x ≈ y :=
quotient.exact

example (x y : x₀ ⟶ x₀) : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
quotient.eq

@[simp] def id : π₁ x₀ := ⟦Id⟧


def inverse : π₁ x₀ → π₁ x₀ :=
begin
  apply quotient.lift,
  rotate, intro x, use ⟦x⁻¹⟧,
  intros x y rxy,simp, apply Inverse_Homotopic, rw ← equiv_def, exact rxy,
end

@[simp] lemma inv_def (a : x₀ ⟶ x₀) :  inverse ⟦a⟧ = ⟦a⁻¹⟧  := 
begin
  refl,
end

def multiply : π₁ x₀ → π₁ x₀ → π₁ x₀ :=
begin
  apply quotient.lift₂,
  rotate,
  intros x y,
  exact ⟦x ∘ y⟧,
  intros x y a b rxa ryb, simp, 
  apply Path_Comp_Preserve_Path_Hom,
  exact rxa, exact ryb,
end

@[simp] lemma multiply_def (a b : x₀ ⟶ x₀) : multiply ⟦a⟧ ⟦b⟧ = ⟦a∘b⟧ :=
begin
  refl,
end

@[simp] lemma mul_inv (a : x₀ ⟶ x₀) : multiply (inverse ⟦a⟧) ⟦a⟧ = id :=
begin
  simp, exact left_handed_inverse a,
end
  /-{
    intros a b c, apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c, simp, exact Path_Assoc a b c,
  }, -/

def group_structure : group (π₁ x₀) :=
{ 
  mul := multiply,
  one := id,
  inv := inverse,
  mul_assoc := begin
    intros a b c, apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c, simp, exact Path_Assoc a b c,
  end,
  one_mul := begin
    intro a, apply quotient.induction_on a, clear a,
    intro a, simp, exact left_handed_id a,
  end,
  mul_one := begin
    intro a, apply quotient.induction_on a, clear a,
    intro a, simp, exact right_handed_id a,
  end,
  mul_left_inv := begin
    intro a,  apply quotient.induction_on a, clear a,
    intro a, exact mul_inv a,
  end,
}


 

#check Alg_Top.loop_setoid




end Alg_Top