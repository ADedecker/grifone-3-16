import part1

open_locale classical

namespace linear_map

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

local notation `k` := f.ker_it
local notation `j` := f.range_it
local notation `𝓚` := f.ker_it_supr
local notation `𝓙` := f.range_it_infi
local notation `r` := f.range_char
local notation `s` := f.ker_char

def range_it_infi := ⨅ (n : ℕ), j n

def ker_it_supr := ⨆ (n : ℕ), k n

def has_finite_range_char := ∃ m, j (m+1) = j m

def has_finite_ker_char := ∃ m, k (m+1) = k m

noncomputable def range_char := if h : f.has_finite_range_char then nat.find h else 0

noncomputable def ker_char := if h : f.has_finite_ker_char then nat.find h else 0

lemma range_char_spec (hf : f.has_finite_range_char) : 
  j (r + 1) = j r :=
begin
  simp only [range_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_char_spec (hf : f.has_finite_ker_char) : 
  k (s + 1) = k s :=
begin
  simp only [ker_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_it_supr_stable : ∀ x ∈ 𝓚, f x ∈ 𝓚 :=
begin
  intro x,
  simp [ker_it_supr, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)],
  intros i hi,
  use i,
  rw [ker_it, mem_ker] at ⊢ hi, 
  rw [← pow_succ_apply', pow_succ_apply, hi, f.map_zero]
end

lemma range_it_infi_stable : ∀ x ∈ 𝓙, f x ∈ 𝓙 :=
begin
  intro x,
  simp [range_it_infi, submodule.mem_infi],
  intros hx i,
  rcases hx i with ⟨x', -, rfl⟩,
  rw [← pow_succ_apply, pow_succ_apply'],
  exact mem_range_self _ _
end

section q2_1

variables (hr : has_finite_range_char f)

include hr

lemma range_it_infi_eq_range_it_range_char : 𝓙 = j r :=
le_antisymm (infi_le _ _)
begin
  intros x hx,
  refine (submodule.mem_infi _).mpr (λ i, _),
  by_cases h : i ≤ r,
  { exact f.range_it_antimono h hx },
  { rwa f.q1_1' (f.range_char_spec hr) (le_of_not_le h) }
end

lemma q2_1_a : submodule.map f 𝓙 ≤ 𝓙 :=
begin
  rw [f.range_it_infi_eq_range_it_range_char hr, ← range_it_succ_eq', f.range_char_spec hr],
  exact le_refl _
end

lemma q2_1_b : 𝓙 ⊔ k r = ⊤ :=
begin
  rw eq_top_iff,
  rintro x -,
  rw submodule.mem_sup,
  obtain ⟨x', -, hx'⟩ : (f^r) x ∈ j (r + r),
  { convert (f^r).mem_range_self x using 1,
    exact f.q1_1 (f.range_char_spec hr) _ },
  rw f.pow_add_apply at hx',
  refine ⟨(f^r) x', _, x - (f^r) x', _, by abel⟩,
  { rw f.range_it_infi_eq_range_it_range_char hr,
    exact (f^r).mem_range_self x' },
  { rw [ker_it, mem_ker, map_sub, hx', sub_self] }
end

end q2_1

section q2_2

variables (hs : has_finite_ker_char f)

include hs

lemma ker_it_supr_eq_ker_it_ker_char : 𝓚 = k s :=
le_antisymm
begin
  intros x hx,
  rw [ker_it_supr, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)] at hx,
  rcases hx with ⟨i, hx⟩,
  by_cases h : i ≤ s,
  { exact f.ker_it_mono h hx },
  { rwa ← f.q1_2' (f.ker_char_spec hs) (le_of_not_le h) }
end
(le_supr _ _)

lemma q2_2_a : (f.restrict f.ker_it_supr_stable)^s = 0 :=
begin
  ext ⟨x, hx⟩,
  rw pow_restrict_comm,
  rw f.ker_it_supr_eq_ker_it_ker_char hs at hx,
  exact hx
end

lemma q2_2_b : function.injective (f.restrict f.range_it_infi_stable) :=
begin
  rw [← ker_eq_bot, eq_bot_iff],
  rintros ⟨x, hx⟩,-- hxf,
  rw [ker_restrict, submodule.mem_bot, submodule.mk_eq_zero],
  rintro (hxf : f x = 0),
  rw [range_it_infi, submodule.mem_infi] at hx,
  rcases hx s with ⟨x', -, rfl⟩,
  have : x' ∈ k (s+1) := by rwa [← pow_succ_apply] at hxf,
  rwa f.ker_char_spec hs at this
end 

--lemma q2_2_b : function.injective (f.restrict f.range_it_infi_stable) :=
--suffices h : (f.restrict f.range_it_infi_stable).ker ≤ ⊥,
--  by rwa [← ker_eq_bot, eq_bot_iff],
--assume ⟨x, (hx : x ∈ 𝓙)⟩,
--suffices h : f x = 0 → x = 0,
--  by rw [ker_restrict, submodule.mem_bot, submodule.mk_eq_zero]; exact h,
--assume (hfx : f x = 0),
--have hx₁ : ∀ i, x ∈ j i,
--  by rwa [← submodule.mem_infi],
--have hx₂ : x ∈ j s,
--  from hx₁ s,
--let ⟨x', _, (hx' : (f^s) x' = x)⟩ := hx₂ in
--have hx'₁ : (f^(s+1)) x' = 0,
--  by rwa [pow_succ_apply, hx'],
--have hx'₂ : x' ∈ k s,
--  by rwa ← f.ker_char_spec hs,
--show x = 0,
--  by rwa ← hx'

lemma q2_2_c : j s ⊓ 𝓚 = ⊥ :=
begin
  rw [eq_bot_iff, f.ker_it_supr_eq_ker_it_ker_char hs],
  rintros x ⟨⟨x', -, rfl⟩, hx⟩,
  have : x' ∈ k (s+s),
  { rw [ker_it, mem_ker, pow_add_apply],
    exact hx },
  rw f.q1_2 (f.ker_char_spec hs) s at this,
  rwa [submodule.mem_bot]
end

--lemma q2_2_c : j s ⊓ 𝓚 = ⊥ :=
--suffices h : j s ⊓ 𝓚 ≤ ⊥,
--  by rwa eq_bot_iff,
--assume x ⟨⟨x', _, (hx' : (f^s) x' = x)⟩ , (hx : x ∈ 𝓚)⟩,
--suffices h : x = 0,
--  by rwa submodule.mem_bot,
--have hx₁ : x ∈ k s,
--  by rwa ← f.ker_it_supr_eq_ker_it_ker_char hs,
--have hx'₁ : (f^s) x' ∈ k s,
--  by rwa hx',
--have hx'₂ : x' ∈ k (s+s),
--  by rw [ker_it, mem_ker, pow_add_apply]; exact hx'₁,
--have hx'₃ : x' ∈ k s,
--  by rwa ← f.q1_2 (f.ker_char_spec hs) s,
--have hx'₄ : (f^s) x' = 0,
--  from hx'₃,
--show x = 0, 
--  by rwa ← hx'

end q2_2

end linear_map