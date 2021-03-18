import order.directed
import linear_algebra.basic

lemma antimono_of_antimono_nat {α : Type*} [preorder α] {f : ℕ → α} 
  (hf : ∀n, f (n + 1) ≤ f n) :
  ∀ ⦃x y⦄, x ≤ y → f y ≤ f x | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end

lemma directed_le_of_monotone {α ι : Type*} [preorder α] [linear_order ι] {f : ι → α} 
  (hf : monotone f) : directed (≤) f :=
λ i j, ⟨max i j, hf (le_max_left i j), hf (le_max_right i j)⟩

namespace linear_map

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

lemma pow_succ_apply (n : ℕ) (x : E) : (f^(n+1)) x = f ((f^n) x) :=
by rw [pow_succ]; refl

lemma pow_succ_apply' (n : ℕ) (x : E) : (f^(n+1)) x = (f^n) (f x) :=
by rw [pow_succ']; refl

lemma pow_add_apply (n m : ℕ) (x : E) : (f^(n+m)) x = (f^n) ((f^m) x) :=
by rw [pow_add]; refl

lemma pow_add_apply' (n m : ℕ) (x : E) : (f^(n+m)) x = (f^m) ((f^n) x) :=
by rw [add_comm]; exact f.pow_add_apply m n x

lemma comp_stable (g : E →ₗ[K] E) {U : submodule K E} (hfU : ∀ x ∈ U, f x ∈ U)
  (hgU : ∀ x ∈ U, g x ∈ U) : ∀ x ∈ U, (f.comp g) x ∈ U := 
λ x hx, hfU _ (hgU x hx)

lemma pow_stable {U : submodule K E} (hfU : ∀ x ∈ U, f x ∈ U) :
  ∀ (n : ℕ), ∀ x ∈ U, (f^n) x ∈ U
| 0 := λ x hx, hx
| (n+1) := λ x hx,
  begin
    rw pow_succ_apply,
    exact hfU _ (pow_stable n _ hx)
  end

lemma restrict_comp (g : E →ₗ[K] E) {U : submodule K E} (hfU : ∀ x ∈ U, f x ∈ U)
  (hgU : ∀ x ∈ U, g x ∈ U) (hfgU : ∀ x ∈ U, (f.comp g) x ∈ U) : 
  (f.comp g).restrict hfgU = (f.restrict hfU).comp (g.restrict hgU) :=
rfl

lemma pow_restrict_comm {U : submodule K E} (hfU : ∀ x ∈ U, f x ∈ U) :
  ∀ n, (f.restrict hfU)^n = (f^n).restrict (f.pow_stable hfU n)
| 0 := 
  begin
    ext ⟨x, hx⟩,
    refl
  end
| (n+1) :=
  begin
    ext ⟨x, hx⟩,
    simp only [pow_succ, mul_eq_comp, restrict_comp _ _ hfU (f.pow_stable hfU n) _],
    rw pow_restrict_comm n
  end

end linear_map