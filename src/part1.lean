import linear_algebra
import utils

namespace linear_map

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

local notation `k` := f.ker_it
local notation `j` := f.range_it

def ker_it (n : ℕ) := (f^n).ker

lemma mem_ker_it_succ_iff (n : ℕ) (x : E) : x ∈ k (n+1) ↔ f x ∈ k n :=
by rw [ker_it, mem_ker, ker_it, mem_ker, pow_succ']; refl

def range_it (n : ℕ) := (f^n).range

lemma range_it_succ_eq' (n : ℕ) : j (n+1) = (j n).map f :=
by rw [range_it, range_it, range, range, pow_succ, mul_eq_comp, submodule.map_comp]

lemma range_it_succ_eq (n : ℕ) : j (n+1) = f.range.map (f^n) :=
by rw [range_it, range, range, pow_succ', mul_eq_comp, submodule.map_comp]

lemma ker_it_mono : monotone k :=
monotone_of_monotone_nat
begin
  intros n x hx,
  rw [ker_it, mem_ker] at ⊢ hx,
  simp [hx, pow_succ]
end

lemma range_it_antimono : ∀ ⦃x y⦄, x ≤ y → j y ≤ j x :=
antimono_of_antimono_nat (λ n x ⟨x', _, hx'⟩, ⟨f x', trivial, by simpa using hx'⟩)

lemma q1_1 {m : ℕ} (hm : j (m+1) = j m) : ∀ p, j (m+p) = j m
| 0 := rfl
| (p+1) := le_antisymm (f.range_it_antimono $ le_add_right $ le_refl m)
  begin
    intros x hx,
    rwa [← hm, range_it_succ_eq', ← q1_1 p, ← range_it_succ_eq'] at hx
  end

lemma q1_2 {m : ℕ} (hm : k (m+1) = k m) : ∀ p, k (m+p) = k m
| 0 := rfl
| (p+1) := le_antisymm
  begin
    intros x hx,
    rwa [← add_assoc, mem_ker_it_succ_iff, q1_2 p, ← mem_ker_it_succ_iff, hm] at hx,
  end
  (f.ker_it_mono $ le_add_right $ le_refl m)

lemma q1_1' {m n : ℕ} (hm : j (m+1) = j m) (hmn : m ≤ n) : 
  j n = j m :=
begin
  convert f.q1_1 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

lemma q1_2' {m n : ℕ} (hm : k (m+1) = k m) (hmn : m ≤ n) : 
  k n = k m :=
begin
  convert f.q1_2 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

end linear_map