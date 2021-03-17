import linear_algebra
import utils

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

def ker_it (n : ℕ) := (f^n).ker

lemma mem_ker_it_succ_iff (n : ℕ) (x : E) : x ∈ f.ker_it (n+1) ↔ f x ∈ f.ker_it n :=
by rw [ker_it, mem_ker, ker_it, mem_ker, pow_succ']; refl

def range_it (n : ℕ) := (f^n).range

lemma range_it_succ_eq' (n : ℕ) : f.range_it (n+1) = (f.range_it n).map f :=
by rw [range_it, range_it, range, range, pow_succ, mul_eq_comp, submodule.map_comp]

lemma range_it_succ_eq (n : ℕ) : f.range_it (n+1) = f.range.map (f^n) :=
by rw [range_it, range, range, pow_succ', mul_eq_comp, submodule.map_comp]

lemma ker_it_mono : monotone f.ker_it :=
monotone_of_monotone_nat
begin
  intros n x hx,
  rw [ker_it, mem_ker] at ⊢ hx,
  simp [hx, pow_succ]
end

lemma range_it_antimono : ∀ ⦃x y⦄, x ≤ y → f.range_it y ≤ f.range_it x :=
antimono_of_antimono_nat (λ n x ⟨x', _, hx'⟩, ⟨f x', trivial, by simpa using hx'⟩)

lemma q1_1 {m : ℕ} (hm : f.range_it (m+1) = f.range_it m) : ∀ p, f.range_it (m+p) = f.range_it m
| 0 := rfl
| (p+1) := le_antisymm (f.range_it_antimono $ le_add_right $ le_refl m)
  begin
    intros x hx,
    rwa [← hm, range_it_succ_eq', ← q1_1 p, ← range_it_succ_eq'] at hx
  end

lemma q1_2 {m : ℕ} (hm : f.ker_it (m+1) = f.ker_it m) : ∀ p, f.ker_it (m+p) = f.ker_it m
| 0 := rfl
| (p+1) := le_antisymm
  begin
    intros x hx,
    rwa [← add_assoc, mem_ker_it_succ_iff, q1_2 p, ← mem_ker_it_succ_iff, hm] at hx,
  end
  (f.ker_it_mono $ le_add_right $ le_refl m)

lemma q1_1' {m n : ℕ} (hm : f.range_it (m+1) = f.range_it m) (hmn : m ≤ n) : 
  f.range_it n = f.range_it m :=
begin
  convert f.q1_1 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

lemma q1_2' {m n : ℕ} (hm : f.ker_it (m+1) = f.ker_it m) (hmn : m ≤ n) : 
  f.ker_it n = f.ker_it m :=
begin
  convert f.q1_2 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

end linear_map