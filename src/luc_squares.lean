import divisibility2
import data.nat.sqrt
import number_theory.quadratic_reciprocity

lemma qr_mod4 (a : ℕ ): (a^2%4)=0 ∨ (a^2%4)=1:=
begin
    rw nat.pow_two, rw nat.mul_mod, 
    have h1:= nat.mod_lt a (show 4>0, by linarith), interval_cases a%4; rw h; tauto
end

lemma diff_of_squares_neq_2 (a b: ℕ ): a^2 +2 ≠ b^2:=
begin
    by_contra, push_neg at a_1, apply_fun (λ (u: ℕ ), u%4) at a_1, rw nat.add_mod at a_1,
    have h1:= qr_mod4 b, cases qr_mod4 a, 
    {rw h at a_1, simp [(show 2%4 =2, from rfl)] at a_1,rw ← a_1 at h1, cc},
    {rw h at a_1, simp [(show (1+2)%4 = 3, from rfl)] at a_1, rw ← a_1 at h1,cc}
end

lemma is_contra (P:  Prop) : P ↔ (¬ P → false):=
begin
    cc,
end 

lemma to_3_n_gt_n (n:ℕ ): n + 1 ≤ 3^n :=
begin
  induction n with d hd,
  {simp},
  {calc d.succ + 1 = (d + 1) + 1 : rfl
  ...             ≤ 3 ^ d + 1 : add_le_add_right' hd
  ...             ≤ 3 ^ d + 2 * 3 ^ d : add_le_add_left' _
  ... = 3 ^ d.succ : by rw [nat.pow_succ]; ring,
  show 0 < _,
  apply mul_pos, simp,
  apply nat.pow_pos, simp}
end

lemma max_pow_3 (n: ℕ ) (h0 : n>0): ∃ (r: ℕ ), 3^r ∣ n ∧ ¬ 3^(r+1)∣ n:=
begin
    rw is_contra ( ∃ (r : ℕ), 3 ^ r ∣ n ∧  ¬3 ^ (r + 1) ∣ n), rw  not_exists, intro p, push_neg at p,
    have h1: ∀ x: ℕ , 3 ^(x+1) ∣ n,
        {intro q, induction q with d hd,
        {cases p 0 with p1 p2, exfalso, simp at p1, assumption, assumption},
        {rw nat.succ_eq_add_one, cases p (d+1) with p1 p2,  contradiction, assumption}},
    have h3:= nat.le_of_dvd h0 (h1 n),
    have h4:= to_3_n_gt_n (n+1), linarith
end

lemma decomp_pow_3 (n: ℕ ) (h : n>0): ∃ (r k: ℕ ), n = 3^r *k ∧ ¬ 3 ∣ k:=
begin 
    cases max_pow_3 n h with s h1, cases h1 with h1 h2, cases h1 with m h1, use s, use m,
    split, 
    {assumption}, 
    {by_contra, cases a with b a, rw a at h1, rw ← mul_assoc at h1, 
    have h3: 3^(s+1) ∣ n, 
        {use b, rw nat.pow_add, simp [h1]},
    contradiction}
end

lemma non_res_3_mod_4 (d a: ℕ ) (h: d>0): (a^2: zmod d) = -1 → (d%4) ≠ 3:=
begin
    apply nat.strong_induction_on d, intros n h1 h2, cases classical.em (n.prime), 
    {have h3: fact n.prime, {assumption},
    rw ← @zmod.exists_pow_two_eq_neg_one_iff_mod_four_ne_three n h3, use a, exact h2},
    {cases classical.em (n<2), 
        {interval_cases n,  
        {rw [show 0%4=0, from rfl], linarith},  
        {rw [show 1%4=1, from rfl], linarith}},
    push_neg at h_2, cases nat.exists_dvd_of_not_prime2 h_2 h_1, 
    rcases h_3 with ⟨ h3, h4, h5⟩, cases h3 with v h3, rw nat.succ_le_iff at h4, 
    have h5': v>0,
        {by_contra, push_neg at a_1, interval_cases v, rotate, linarith}, 
    rw ←  lt_mul_iff_one_lt_left h5' at h4, rw ← h3 at h4, 
    have h6: ((a^2:ℤ ): zmod n) = ((-1: ℤ ) : zmod n), {simp, exact h2}, 
    rw zmod.int_coe_eq_int_coe_iff at h6, 
    have h7:= int.modeq.modeq_of_dvd_of_modeq (show (w: ℤ ) ∣ (n:ℤ  ), by simp[h3]) h6,
    have h8:= int.modeq.modeq_of_dvd_of_modeq (show (v:ℤ ) ∣ (n:ℤ ), by simp[h3]) h6,
    rw ← zmod.int_coe_eq_int_coe_iff at *,  simp at h7, simp at h8, 
    have h9:= h1 v h4 h8, 
    have h10:= h1 w h5 h7,
    rw h3, rw nat.mul_mod, 
    have h11:= nat.mod_lt w (show 4>0, by linarith),
    have h12:= nat.mod_lt v (show 4>0, by linarith),
    interval_cases w%4; rw h_3; simp, {linarith}, {assumption},
    interval_cases v%4; rw h_4; simp [(show 2*2 =4, from rfl), (show 2%4=2, from rfl)]; linarith}
end

lemma squares_inv (a b n x: ℕ ) (h: nat.coprime a n) (h0: nat.coprime b n) (h1: (b*x^2 :zmod n) = -(b*a^2)) (h2:fact (0<n)):  ∃ (r: ℕ ),(r^2 : zmod n ) = -1:=
begin
    use ((x* a⁻¹ :zmod n).val), rw zmod.cast_val ((x* a⁻¹: zmod n)),
    have h3:= zmod.coe_mul_inv_eq_one a h, 
    have h4:= zmod.coe_mul_inv_eq_one b h0,
    rw mul_comm at h1, nth_rewrite 1 mul_comm at h1, apply_fun (λ (a: zmod n), (a* b⁻¹ :zmod n) ) at h1, rw ← neg_one_mul at h1, repeat {rw mul_assoc at h1}, rw h4 at h1, rw mul_one at h1,
    rw [show (-1: zmod n)=-1*1, by simp],rw ← h3, rw mul_pow, rw h1, ring
end

lemma pow_3_odd (u :ℕ ): (3^u)%2=1:=
begin
    induction u with d hd,
    {ring},
    {rw nat.pow_succ, simp [nat.mul_mod, hd], ring}
end

lemma double_not_zero_mod3 (u: ℕ ) (h1: ¬ 3 ∣ u) : 2 ∣ 2*u ∧ (2*u)%3 ≠ 0:=
begin
    split, {simp},
    {by_contra, push_neg at a, rw ← nat.dvd_iff_mod_eq_zero at a, 
    have a2:= nat.coprime.dvd_of_dvd_mul_left (show nat.coprime 3 2, by tauto) a, contradiction}
end 

lemma fun_gen_add (a u n s q r x y: ℕ ) (f: ℕ → ℕ ) (h2: n =  x+4*a*s ) (h3: s =q+1 ) (h4: s=3^r*u ) (h5: ∀ (m: ℕ),y ∣ f(m+2*(2*a*u)) +f(m)): y ∣ f(n) + f(x):=
begin
    nth_rewrite 0 h2, rw ← one_mul (f x),
    have g8: 1  = (-1: ℤ )^(3^r *(0+1)-1), 
        {have g9: 2 ∣ 3^r-1, {nth_rewrite 2 ← pow_3_odd r, apply nat.dvd_sub_mod}, 
        rw zero_add, rw mul_one, rw neg_1_pow_even _ g9},
    rw ← int.coe_nat_dvd, push_cast, rw g8, rw h4, rw [show (4*a)* (3 ^ r * u) = 3^r * (2*a*(2*u)), by ring],
    apply mod_fun_gen y (2*a*(2*u)) 0 (3^r) (x) (f) (nat.one_le_pow' r 2), rw [show (-1:ℤ )^0 =1, by ring], norm_cast, intro m, rw one_mul, rw [show 2*a*(2*u) = 2*(2*a*u), by ring], exact h5 m,
end

lemma res_mod_4' (n: ℕ ): n%2=0 ∨ n%4=1 ∨ n%4=3:=
begin
    have g1:= nat.mod_lt n (show 4>0, by linarith),
    have g2:= nat.mod_mul_left_mod n 2 2, rw (show 2*2 =4, from rfl) at g2,
    interval_cases n%4; rw h at g2; simp [*, (show 2%2=0, from rfl), (show 0%2=0, from rfl)] at *
end 

theorem luc_square (n k: ℕ ) (h: luc n =k^2) :  n=1 ∨ n=3:=
begin
    cases res_mod_4' n with h0 h1', cases div_algo n 2 with  w h1, rw h0 at h1, rw add_zero at h1,
    {rw h1 at h, apply_fun (λ (a: ℕ ), (a + 2*(-1)^w : ℤ )) at h, rw fib_luc3 at h, cases even_or_odd w with v h3, cases h3 with h3 h4,
    {rw h3 at h, 
    have h5:= neg_1_pow_even (2*v) (show 2 ∣ 2*v, by simp), rw h5 at h, rw mul_one at h, norm_cast at h,
    have h6:= diff_of_squares_neq_2 k (luc(2*v)), rw h at h6, contradiction},
    {rw h4 at h, rw neg_1_pow_odd at h, apply_fun (λ (a: ℤ ), a+2) at h, 
    have h7:= diff_of_squares_neq_2 (luc(2*v+1)) k, ring at h, norm_cast at h}},

    {cases div_algo n 4 with s h2, cases nat_case_bash s 0 with g2 g3, swap,
    {cases g3 with q g3, rw add_zero q at g3, cases decomp_pow_3 s (show s>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩, rw add_comm at h2,
    have g6:=double_not_zero_mod3 u g5, 
    have g7:=fun_gen_add 1 u n s q r (n%4) (luc(2*u)) (luc) h2 g3 g4 (mod_luc (2*1*u) g6), repeat{rw mul_one at g7},
    rw h at g7, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g7, apply_fun (λ (a: zmod (luc(2*u))), (a- luc(n%4))) at g7,
    have H: (k^2 : zmod (luc(2*u))) = -luc(n%4), {simp at g7, exact g7}, cases h1' with h_1 h_2,
    {rw h_1 at H, rw [show luc 1 =1, from rfl] at H, simp at H, 
    have g10:= non_res_3_mod_4 _ _ (luc_pos (2*u)) H, rw luc_mod_4 (2*u) g6 at g10, contradiction},

    {rw h_2 at H, rw [show luc 3 =4, from rfl] at H,  
    rw [show 4=1*2*2, by ring] at H, rw pow_two at H, nth_rewrite 0 ← one_mul (k) at H, repeat{rw nat.cast_mul at H}, repeat{rw mul_assoc at H}, repeat{rw ← pow_two at H}, 
    have g11:= squares_inv 2 1 (luc(2*u)) k (show nat.coprime 2 (luc(2*u)), from luc_coprime_2 _ (g6.2)) (nat.coprime_one_left (luc(2*u))) H (luc_pos(2*u)), cases g11 with r g11,
    have g12:= non_res_3_mod_4 _ _ (luc_pos (2*u)) g11, rw luc_mod_4 (2*u) g6 at g12, contradiction}},
    rw le_zero_iff_eq at g2, rw g2 at h2, 
    have g3:= nat.mod_lt n (show 4>0, by linarith), interval_cases (n%4); rw h_1 at h2; simp[h2]; omega}
end