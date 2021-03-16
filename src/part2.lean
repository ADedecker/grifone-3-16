import part1

namespace linear_map

open_locale classical

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

def range_it_top := ⨅ (n : ℕ), f.range_it n

def ker_it_top := ⨆ (n : ℕ), f.ker_it n

def has_finite_range_char := ∃ m, f.range_it (m+1) = f.range_it m

def has_finite_ker_char := ∃ m, f.ker_it (m+1) = f.ker_it m

noncomputable def range_char := if h : f.has_finite_range_char then nat.find h else 0

noncomputable def ker_char := if h : f.has_finite_ker_char then nat.find h else 0

lemma range_char_spec (hf : f.has_finite_range_char) : 
  f.range_it (f.range_char + 1) = f.range_it f.range_char :=
begin
  simp only [range_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_char_spec (hf : f.has_finite_ker_char) : 
  f.ker_it (f.ker_char + 1) = f.ker_it f.ker_char :=
begin
  simp only [ker_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_it_top_stable : ∀ x ∈ f.ker_it_top, f x ∈ f.ker_it_top :=
begin
  intro x,
  simp [ker_it_top, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)],
  intros i hi,
  use i,
  rw [ker_it, mem_ker] at ⊢ hi, 
  rw [← iterate_succ_apply, iterate_succ_apply', hi, f.map_zero]
end

lemma range_it_top_stable : ∀ x ∈ f.range_it_top, f x ∈ f.range_it_top :=
begin
  intro x,
  simp [range_it_top, submodule.mem_infi],
  intros hx i,
  rcases hx i with ⟨x', -, rfl⟩,
  rw [← iterate_succ_apply', iterate_succ_apply],
  exact mem_range_self _ _
end

section q2_1

variables (hr : has_finite_range_char f)

include hr

local notation `r` := f.range_char

lemma range_it_top_eq_range_it_range_char : f.range_it_top = f.range_it r :=
le_antisymm (infi_le _ _)
begin
  intros x hx,
  refine (submodule.mem_infi _).mpr (λ i, _),
  by_cases h : i ≤ r,
  { exact f.range_it_antimono h hx },
  { rwa f.q1_1' (f.range_char_spec hr) (le_of_not_le h) }
end

lemma q2_1_a : f.range_it_top.map f ≤ f.range_it_top :=
begin
  rw [f.range_it_top_eq_range_it_range_char hr, ← range_it_succ_eq', f.range_char_spec hr],
  exact le_refl _
end

lemma q2_1_b : f.range_it_top ⊔ f.ker_it r = ⊤ :=
begin
  rw eq_top_iff,
  rintro x -,
  rw submodule.mem_sup,
  obtain ⟨x', -, hx'⟩ : f.iterate r x ∈ f.range_it (r + r),
  { convert (f.iterate r).mem_range_self x using 1,
    exact f.q1_1 (f.range_char_spec hr) _ },
  rw f.iterate_add_apply at hx',
  refine ⟨f.iterate r x', _, x - f.iterate r x', _, by abel⟩,
  { rw f.range_it_top_eq_range_it_range_char hr,
    exact (f.iterate r).mem_range_self x' },
  { simp [ker_it, hx'] }
end

end q2_1

section q2_2

variables (hs : has_finite_ker_char f)

include hs

local notation `s` := f.ker_char

lemma ker_it_top_eq_ker_it_ker_char : f.ker_it_top = f.ker_it s :=
le_antisymm
begin
  intros x hx,
  rw [ker_it_top, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)] at hx,
  rcases hx with ⟨i, hx⟩,
  by_cases h : i ≤ s,
  { exact f.ker_it_mono h hx },
  { rwa ← f.q1_2' (f.ker_char_spec hs) (le_of_not_le h) }
end
(le_supr _ _)

lemma q2_2_a : (f.restrict f.ker_it_top_stable).iterate s = 0 :=
begin
  ext ⟨x, hx⟩,
  rw iterate_restrict_comm,
  rw f.ker_it_top_eq_ker_it_ker_char hs at hx,
  exact hx
end

lemma q2_2_b : function.injective (f.restrict f.range_it_top_stable) :=
begin
  rw [← ker_eq_bot, eq_bot_iff],
  rintros ⟨x, hx⟩ hxf,
  rw [range_it_top, submodule.mem_infi] at hx,
  rw [ker_restrict] at hxf,
  have : f x = 0 := hxf,
  rcases hx s with ⟨x', -, rfl⟩,
  rw [← iterate_succ_apply'] at this,
  have : x' ∈ f.ker_it (s+1) := this,
  rw f.ker_char_spec hs at this,
  simpa
end 

lemma q2_2_c : f.range_it s ⊓ f.ker_it_top = ⊥ :=
begin
  rw [eq_bot_iff, f.ker_it_top_eq_ker_it_ker_char hs],
  rintros x ⟨⟨x', -, rfl⟩, hx⟩,
  have : x' ∈ f.ker_it (s+s),
  { simpa [ker_it, iterate_add_apply'] },
  rw f.q1_2 (f.ker_char_spec hs) s at this,
  simpa
end

end q2_2

end linear_map