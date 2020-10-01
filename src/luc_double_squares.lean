import luc_squares
import data.nat.sqrt

lemma double_qr_mod8 (a:ℕ ): (2*a^2)%8 =0 ∨ (2*a^2)%8=2:=
begin
    rw nat.pow_two, rw nat.mul_mod, nth_rewrite 1 nat.mul_mod, nth_rewrite_rhs 1 nat.mul_mod,
    have h1:= nat.mod_lt a (show 8>0, by linarith), interval_cases a%8; rw h; tauto
end

lemma res_mod_12 (n: ℕ ) (h: n%2=1) (h1: n%3=0): n%12=3 ∨ n%12=9:=
begin
    have g1:= nat.mod_lt n (show 12>0, by linarith), 
    have g2:= nat.mod_mul_left_mod n 4 3, rw [show 4*3=12, from rfl] at g2, rw h1 at g2,
    rw ←nat.dvd_iff_mod_eq_zero at g2, cases g2 with x g2, rw g2 at g1,
    have g3: x<4, by linarith,
    have g4:= nat.mod_mul_left_mod n 6 2, rw (show 6*2 =12, from rfl) at g4, rw←  g4 at h,
    interval_cases x; simp * at *, right, refl
end

lemma res_mod_4 (n a: ℕ ) (h: n=2*a ): n%4 =0 ∨ n%4=2:=
begin
    have g1:= nat.mod_lt n (show 4>0, by linarith),
    apply_fun (λ (a: ℕ ), a%2) at h, rw nat.mul_mod at h, rw (show 2%2=0, from rfl) at h, rw zero_mul at h,
    have g2:= nat.mod_mul_left_mod n 2 2, rw [show 2*2=4, from rfl] at g2, rw h at g2, 
    interval_cases n%4; simp [g2, h_1, (show 3%2=1, from rfl), (show 0%2=0, from rfl), (show 1%2 =1, from rfl)] at *; exfalso; assumption
end

lemma res_mod_8 (n: ℕ) (h: n%4=2): n%8 = 6 ∨ n%8=2:=
begin
    have g1:= nat.mod_lt n (show 8>0, by linarith),
    have g2:= nat.mod_mul_left_mod n 2 4, rw [show 2*4=8, from rfl] at g2, rw h at g2, 
    interval_cases n%8; simp [* ,(show 1%4=1, from rfl), (show 3%4 =3, from rfl), (show 5%4 =1, from rfl), (show 7%4=3, from rfl)] at *; cc
end

lemma add_sub_add (a b c: ℕ) (h: b≤ a) (h2: b ≤ c): a-b+c = c-b+a:=
begin
    omega
end

theorem luc_double_square  (n k: ℕ ) (h: luc n =2*k^2) :  n=0 ∨ n=6 :=
begin
    cases even_or_odd n with w h1, cases h1 with h1 h1', swap,
    {apply_fun ( λ (a: ℕ ), a%2) at h1', simp [nat.add_mod, nat.mul_mod, (show 1%2=1, from rfl)] at h1',
    have h2:= congr_arg (λ (a: ℕ), a%2 ) h, simp at h2, rw luc_even at h2,
    have h3:= res_mod_12 n h1' h2,
    have h4:= luc_mod_8_gen n, rw h at h4,
    have h5:= double_qr_mod8 k, rw h4 at h5, cases h3 with h31 h32,
    {rw h31 at h5, rw [show luc 3%8 = 4, from rfl]at h5,cc},
    {rw h32 at h5, rw [show luc 9%8 = 4, from rfl] at h5,cc}},

    {cases res_mod_4 n w h1,
    {cases div_algo n 4 with s h2, cases nat_case_bash s 0 with g2 g3, swap,
    {cases g3 with q g3, rw add_zero q at g3, cases decomp_pow_3 s (show s>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩, rw add_comm at h2,
    have g6:=double_not_zero_mod3 u g5,
    have g7:= fun_gen_add 1 u n s q r (n%4) (luc(2*u)) (luc) h2 g3 g4 (mod_luc (2*1*u) g6), repeat {rw mul_one at g7},
    rw h at g7, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g7, apply_fun (λ (a: zmod (luc(2*u))), (a- luc(n%4))) at g7,
    have H: (↑ (2*k*k) : zmod (luc(2*u))) = -luc(n%4), {simp at g7, simp, rw ← g7, ring},
    rw h_1 at H, rw (show luc 0 =2*1*1, from rfl) at H,  repeat{rw nat.cast_mul at H}, repeat{rw mul_assoc at H}, repeat{rw ← pow_two at H}, 
    have g8:= squares_inv 1 2 (luc(2*u)) k (nat.coprime_one_left (luc(2*u))) (show nat.coprime 2 (luc(2*u)), from luc_coprime_2 _ (g6.2)) H (luc_pos(2*u)), cases g8 with l g8,
    have g9:= non_res_3_mod_4 _ _ (luc_pos(2*u)) g8, rw luc_mod_4 (2*u) g6 at g9, contradiction},
    {rw le_zero_iff_eq at g2, rw g2 at h2, rw h_1 at h2, simp [h2]}},

    {have h2:= res_mod_8 n h_1, cases h2 with h21 h22,
    {cases div_algo n 8 with s h2, cases nat_case_bash s 0 with g2 g3, swap,
    {cases g3 with q g3, rw add_zero q at g3, cases decomp_pow_3 s (show s>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩, rw add_comm at h2,
    have g6:=double_not_zero_mod3 u g5, cases g6 with g61 g62, 
    have g6': 2*u %3 ≠ 0 → ¬ 3 ∣ 2*u, contrapose!, exact nat.mod_eq_zero_of_dvd,
    have G6:=double_not_zero_mod3 (2*u) (g6' g62), rw ← mul_assoc at G6,
    have g7:= fun_gen_add 2 u n s q r (n%(4*2)) (luc(2*2*u)) (luc) h2 g3 g4 (mod_luc (2*2*u) G6),
    rw h at g7, rw mul_assoc at g7, rw mul_assoc at G6, rw [show 4*2 =8, from rfl] at g7, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g7, apply_fun (λ (a: zmod (luc(2*(2*u)))), (a- luc(n%(8)))) at g7,
    have H: (↑ (2*k*k) : zmod (luc(2*(2*u)))) = -luc(n%(8)), {simp at g7, simp, rw ← g7, ring},
    rw h21 at H, rw (show luc 6 =2*3*3, from rfl) at H, repeat{rw nat.cast_mul at H}, repeat{rw mul_assoc at H}, repeat{rw ← pow_two at H}, 
    have g8: (2*(2*u))%4 ≠ 2, {rw ← mul_assoc, rw (show 2*2=4, from rfl), rw nat.mul_mod, rw (show 4%4=0, from rfl), rw zero_mul, simp, linarith},
    have g9:= squares_inv 3 2 (luc(2*(2*u))) k (show nat.coprime 3 (luc(2*(2*u))), from luc_coprime_3 _ (g8)) (show nat.coprime 2 (luc(2*(2*u))), from luc_coprime_2 _ (G6.2)) H (luc_pos(2*(2*u))), cases g9 with l g9,
    have g10:= non_res_3_mod_4 _ _ (luc_pos(2*(2*u))) g9, rw luc_mod_4 (2*(2*u)) G6 at g10, contradiction},
    {rw le_zero_iff_eq at g2, rw g2 at h2, rw h21 at h2, simp at h2, right, exact h2}},

    {cases div_algo n 8 with q h2', rw h22 at h2',
    have h2: n = 8*(q+1)-6, {rw h2', rw mul_add, rw mul_one, rw nat.add_sub_assoc (show 6 ≤ 8, by linarith)},
    cases decomp_pow_3 (q+1) (show q+1>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩, rw add_comm at h2,
    have g6:=double_not_zero_mod3 u g5, cases g6 with g61 g62, 
    have g6': 2*u %3 ≠ 0 → ¬ 3 ∣ 2*u, {contrapose!, exact nat.mod_eq_zero_of_dvd},
    have G6:=double_not_zero_mod3 (2*u) (g6' g62), rw ← mul_assoc at G6, 
    have g7:= fun_gen_add 2 u (8*u-6 + 4*2*(q+1)) (q+1) q r (8*u-6) (luc(2*2*u)) (luc) (show 8*u-6+4*2*(q+1) = 8*u-6+4*2*(q+1), from rfl) (show q+1=q+1, from rfl) g4 (mod_luc (2*2*u) G6),
    have g8:= mod_luc (2*2*u) G6 (8*(q+1)-6),
    have i1: 6 ≤ 2*(2*2*u), 
        {have h2: 1 ≤ u, {by_contra, push_neg at a, interval_cases u, linarith},
        ring, apply le_trans (show 6 ≤ 8*1, by linarith), linarith},
    have g9:= mod_luc_sub (2*2*u) (6) (G6.1) (G6.2) (i1),
    rw (show (-1 :ℤ )^6 = 1, by ring) at g9, rw one_mul at g9, norm_cast at g9, rw (show 2*(2*2*u)=8*u, by ring) at *,
    have g10: 8*(q+1)-6+8*u = 8*u -6+4*2*(q+1), {rw (show 4*2 =8, from rfl), rw add_sub_add _ _ _ (i1) (show 6 ≤ 8*(q+1), by linarith)}, rw g10 at g8,
    have g11:= nat.dvd_add g8 g9, rw add_assoc at g11, nth_rewrite 1 ← add_assoc at g11, nth_rewrite 4 add_comm at g11, repeat {rw ← add_assoc at g11}, rw add_assoc at g11, rw nat.dvd_add_right g7 at g11,
    rw add_comm at h2, rw h2 at h, rw h at g11, rw mul_assoc at g11, rw mul_assoc at G6, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g11, apply_fun (λ (a: zmod (luc(2*(2*u)))), (a- luc(6))) at g11,
    have H: (↑ (2*k*k) : zmod (luc(2*(2*u)))) = -luc(6), {simp at g11, simp, rw ← g11, ring},
    rw (show luc 6 =2*3*3, from rfl) at H, repeat{rw nat.cast_mul at H}, repeat{rw mul_assoc at H}, repeat{rw ← pow_two at H}, 
    have g12: (2*(2*u))%4 ≠ 2, {rw ← mul_assoc, rw (show 2*2=4, from rfl), rw nat.mul_mod, rw (show 4%4=0, from rfl), rw zero_mul, simp, linarith},
    have g13:= squares_inv 3 2 (luc(2*(2*u))) k (show nat.coprime 3 (luc(2*(2*u))), from luc_coprime_3 _ (g12)) (show nat.coprime 2 (luc(2*(2*u))), from luc_coprime_2 _ (G6.2)) H (luc_pos(2*(2*u))), cases g13 with l g13,
    have g14:= non_res_3_mod_4 _ _ (luc_pos(2*(2*u))) g13, rw luc_mod_4 (2*(2*u)) G6 at g14, contradiction}}}
end