import gcd

lemma luc_even_pre (m: ℕ ): luc(3*m)%2=0 ∧ luc(3*m+1)%2=1 ∧ luc(3*m+2)%2=1:=
begin
    induction m with d hd,
    {simp, omega},
    {rcases hd with ⟨ h1,h2,h3 ⟩, 
    rw nat.succ_eq_add_one, rw mul_add, rw mul_one, 
    have h4: luc(3*d+3)%2=0,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h5: luc(3*d+4)%2=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h6: luc(3*d+5)%2=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    tauto}
end

lemma luc_even (m: ℕ ): luc(m)%2 =0  ↔ (m%3)=0:=
begin
    have h1:= nat.mod_lt m (show 3>0, by linarith),
    cases div_algo m 3,
    have h2:= luc_even_pre w, 
    interval_cases m%3; rw h_1; rw h;simp only [*, add_zero]; omega,
end

lemma luc_mod_3_pre (k: ℕ ): luc(8*k)%3 =2 ∧ luc(8*k+1) %3 =1 ∧ luc(8*k+2) %3 =0 ∧ luc(8*k+3) %3=1 ∧ luc(8*k+4) %3 = 1 ∧ luc(8*k+5) %3=2 ∧ luc(8*k+6) %3 =0 ∧ luc(8*k+7) %3 = 2 :=
begin
    induction k with d hd,
    {simp, omega},
    {rcases hd with ⟨ h1,h2,h3,h4,h5,h6,h7,h8 ⟩, 
    rw nat.succ_eq_add_one, rw mul_add, rw mul_one, 
    have h9: luc(8*d+8)%3=2,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h10: luc(8*d+9)%3=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h11: luc(8*d+10)%3=0,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h12: luc(8*d+11)%3=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h13: luc(8*d+12)%3=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h14: luc(8*d+13)%3=2,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h15: luc(8*d+14)%3=0,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h16: luc(8*d+15)%3=2,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    tauto}
end

lemma luc_mod_3 (m: ℕ) : luc(m) %3=0 ↔ m%4=2 :=
begin
    have h1:= div_algo m 8, cases h1 with q h1,
    have h2:= nat.mod_lt m (show 8>0, by linarith),
    have h3:= luc_mod_3_pre q,
    have h4: (8*q)%4=0,
        {rw [show 8*q = 4*(2*q), by ring], rw nat.mul_mod_right},
    interval_cases m%8; rw h1; rw h; simp only [*, add_zero, nat.add_mod, zero_add]; omega
end

lemma luc_mod_4_pre (k: ℕ ): luc(6*k)%4 =2 ∧ luc (6*k+1)%4=1 ∧ luc(6*k+2)%4=3 ∧ luc(6*k+3)%4=0 ∧ luc(6*k+4)%4=3 ∧ luc(6*k+5)%4=3:=
begin
    induction k with d hd,
        {simp, omega},
    {rcases hd with ⟨ h1,h2,h3,h4,h5,h6 ⟩, 
    rw nat.succ_eq_add_one, rw mul_add, rw mul_one, 
    have h7: luc(6*d+6)%4=2,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h8: luc(6*d+7)%4=1,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h9: luc(6*d+8)%4=3,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h10: luc(6*d+9)%4=0,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h11: luc(6*d+10)%4=3,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    have h12: luc(6*d+11)%4=3,
        {rw luc_add, rw nat.add_mod, simp only *, ring},
    tauto}
end 

lemma luc_mod_4 (m: ℕ): 2 ∣ m ∧ (m%3 ≠ 0) →  luc (m)%4 =3 :=
begin
    have h1:= div_algo m 6, cases h1 with q h1,
    have h2:= luc_mod_4_pre q,
    have h3:= nat.mod_lt m (show 6>0, by linarith),
    have h4: (m%6)%3 = m%3, apply nat.mod_mod_of_dvd, use 2, refl,
    have h5: (m%6)%2 = m%2, apply nat.mod_mod_of_dvd, use 3, refl,
    intro u, cases u with u1 u2, rw nat.dvd_iff_mod_eq_zero at u1, interval_cases m%6; simp only [*, add_zero] at *; tauto
end

lemma luc_coprime_2 (u: ℕ ) (h: u%3 ≠ 0): nat.gcd 2 (luc(u))=1:= 
begin
    rw nat.gcd_rec, have h2:= nat.mod_lt (luc(u)) (show 2>0, by linarith), interval_cases luc(u)%2,
    {rw  luc_even at h_1, rw h_1 at h, cc},
    {rw h_1, refl}
end

lemma luc_coprime_3 (u: ℕ)  (h:u%4 ≠ 2) : nat.gcd 3 (luc(u)) =1:=
begin
    rw nat.gcd_rec, have h2:= nat.mod_lt (luc(u)) (show 3>0, by linarith), interval_cases luc(u)%3,
    {rw  luc_mod_3 at h_1, rw h_1 at h, cc},
    {rw h_1, refl}, {rw h_1, refl}
end