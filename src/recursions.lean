import data.nat.basic
import tactic
import data.int.basic
import tactic.nth_rewrite.default


def fib : ℕ → ℕ
| 0     := 0
| 1     := 1
| (n+2) := fib (n+1) + fib n

def luc: ℕ → ℕ
| 0 := 2
| 1 := 1
| (n+2) := luc(n+1) +luc n

@[simp] lemma fib_add ( n :  ℕ) : fib (n+2) = fib (n+1) + fib (n):= by refl
@[simp] lemma luc_add (n: ℕ ): luc (n+2) = luc (n+1) + luc n:= by refl 
@[simp] lemma fib_zero : fib 0 =0:= by refl
@[simp] lemma fib_one : fib 1 = 1:= by refl
@[simp] lemma fib_two : fib 2= 1:= by refl
@[simp] lemma luc_zero : luc 0 =2:= by refl
@[simp] lemma luc_one : luc 1 = 1:= by refl

@[simp] lemma fib_luc_rec (n: ℕ ): luc(n+1) = fib(n+2) + fib (n):=
begin
    revert n,
    apply nat.two_step_induction,
    {simp}, 
    {simp},
    {intros, simp * at *, ring}
    end

lemma nat_case_bash (h n : ℕ ):  h ≤ n ∨ ∃ (k: ℕ ), h=k+n+1:=
begin
    have t1:= le_or_lt h n, cases t1 with t1 t2,
    {left, assumption},
    {right, use h-(n+1), omega }
end

lemma fib_luc1 (m n : ℕ ) : 2 * fib (m+n) = fib (m) * luc (n) + luc(m) * fib(n):=
begin
    revert n, apply nat.two_step_induction,
    {simp [mul_comm]},
    {cases nat_case_bash m 0, interval_cases m, 
        {cases h with k h, rw h, simp, ring},
        {simp}},
    {intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
    rw fib_add, rw mul_add, rw IH1, rw IH2, rw [show n+1+1 =n+2, from rfl], rw fib_add, rw luc_add, ring,}
end

lemma fib_luc2 (m n : ℕ ): 2* luc (m+n) = 5* fib (m) * fib (n) +luc(m) * luc(n) :=
begin
    revert n, apply nat.two_step_induction,
    {simp [mul_comm]},
    {cases nat_case_bash m 0, interval_cases m, 
        {cases h with k h, rw h, simp, ring},
        {simp}},
    {intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
    rw luc_add, rw mul_add, rw IH1, rw IH2, rw [show n+1+1 =n+2, from rfl], rw fib_add, rw luc_add, ring,}
end

lemma fib_luc_rec_2 (m n: ℕ): luc(m+n+1) = fib(m+1)*luc(n+1) + fib(m)*luc(n):=
begin
    revert n, apply nat.two_step_induction,
    {simp,ring},
    {cases nat_case_bash m 0, interval_cases m, 
        {cases h with k h, rw h, simp, ring},
        {simp}},
    {intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
    rw luc_add, rw IH1, rw IH2, ring,}
end

lemma fib_luc3_pre (d: ℕ ):  (↑(luc (d + 2)) * ↑(fib (d + 1)) + 2 * (-1) ^ (d + 1): ℤ) = (↑(luc (d + 1)) * ↑(fib (d + 2)): ℤ):=
begin 
    revert d, apply nat.two_step_induction, 
    {ring}, 
    {ring},  
    {intros p q r, repeat {rw nat.succ_eq_add_one at *}, clear r,
    rw [luc_add, fib_add], push_cast, rw [add_mul, mul_add],
    have t1: (-1: ℤ )^(p+1+1+1) = (-1: ℤ )^ (p+1), rw pow_add (-1: ℤ ) (p+1) (1+1),rw [show (-1: ℤ )^(1+1)=1, from rfl], rw mul_one,
    rw t1, rw mul_add, rw [show p+1+1=p+2, from rfl], repeat{rw add_assoc},
    rw q, 
    nth_rewrite_rhs 0 fib_add, push_cast, rw mul_add,
    nth_rewrite_rhs 0 fib_add, push_cast, rw mul_add,
    nth_rewrite_rhs 0 luc_add, push_cast, rw add_mul,
    ring}
end

lemma fib_luc3 (m: ℕ) : ((luc(2*m) + 2 * (-1: ℤ )^(m)) : ℤ )= ((luc(m))^2 : ℤ ):=
begin
    cases m with d hd,
    {simp, ring},
    {rw nat.succ_eq_add_one, rw [show 2*(d+1)= d+(d+1)+1, by ring], rw fib_luc_rec_2,
    rw fib_luc_rec d, rw pow_two, 
    suffices goal:  (↑(luc (d + 2)) * ↑(fib (d + 1)) + 2 * (-1) ^ (d + 1): ℤ) = (↑(luc (d + 1)) * ↑(fib (d + 2)): ℤ),
        {push_cast,
        rw [add_right_comm, mul_comm], rw (show d+1+1=d+2, from rfl), rw goal, 
        rw fib_luc_rec, push_cast, ring},      
    {apply fib_luc3_pre}}
end


lemma fib_luc1_sub (m n: ℕ ) : (2 * fib (m) :ℤ ) =  (-1: ℤ )^(n)*fib (m+n)  *luc (n) + (-1: ℤ )^(n+1)*luc(m+n) * fib(n):=
begin
    have t1: (-1: ℤ )^(n+1) = -(-1)^n, rw pow_add, ring, 
    revert m, apply nat.two_step_induction, 
    {rw t1,simp, ring},
    {rw t1, cases nat_case_bash n 0,  interval_cases n, 
        {cases h with k h,  rw [show k+0+1 = k+1, from rfl] at h, rw h,
        rw [show 1+(k+1) = k+2, by ring], rw [show ((-1) ^ (k + 1) * ↑(fib (k + 2)) * ↑(luc (k + 1)): ℤ )=  ↑(luc (k + 1))  * ↑(fib (k + 2))*(-1) ^ (k + 1) , by ring], rw ← fib_luc3_pre, 
        rw add_mul, rw fib_one, nth_rewrite_rhs 0 mul_comm, rw add_right_comm, nth_rewrite_rhs 1 mul_assoc, ring, rw int.sub_self, 
        rw mul_assoc, rw ← pow_add, rw[show k+1 +(k+1) = 2*(k+1), by ring], rw pow_mul, rw [show (-1 : ℤ )^2 =1, from rfl], simp},
        {swap, simp}},
    {intros k IH1 IH2, repeat {rw nat.succ_eq_add_one at *}, rw [show  (k+1+1) = k+2, by refl],  
    rw fib_add, push_cast, rw mul_add, rw IH1, rw IH2,  rw [show k+2+n = k+n+2, by ring], rw fib_add, rw luc_add, push_cast, rw mul_add,  rw mul_add, rw add_mul, rw [show k+1+n =k+n+1, by ring], ring}
end

lemma fib_luc_4 (n : ℕ ) : (-1: ℤ )^(n+1)*5*(fib n)^2 + (-1: ℤ )^n * (luc n)^2 =4:=
begin 
    suffices goal: (-1) ^ (n + 1) * 5 * ↑(fib n) ^ 2 + (-1) ^ n * ↑(luc n) ^ 2 + (-1:ℤ )^n * ↑(luc n)^2 = 4+ (-1:ℤ )^n * ↑(luc n)^2, simp * at *,
    repeat{nth_rewrite_lhs 0 ← fib_luc3}, rw add_assoc, rw ← mul_add ((-1: ℤ )^n) _ _, 
    rw [show ↑(luc (2 * n)) + 2 * (-1) ^ n + (↑(luc (2 * n)) + 2 * (-1: ℤ ) ^ n) = ↑ (2*luc (2 * n)) + 4 * (-1) ^ n, by ring], rw [show 2*n = n+n, by ring], rw fib_luc2, 
    have t1: (-1: ℤ )^(n+1) = -(-1)^n, rw pow_add, ring, rw t1,clear t1,
    rw mul_add, 
    have t3: (-1: ℤ )^n *(4 *(-1)^n) = 4, rw ← mul_assoc,rw mul_comm, rw ← mul_assoc, rw ← pow_add, rw [show n+n=2*n, by ring], rw pow_mul, simp,
    rw add_comm,repeat{rw add_assoc},  rw t3, push_cast, rw mul_add, ring,
end

lemma fib_luc2_sub (m n : ℕ ) :  (2 * luc (m) :ℤ ) =  (-1: ℤ )^(n+1)*5*fib (m+n)  *fib (n) + (-1: ℤ )^(n)*luc(m+n) * luc(n):=
begin
    have t1: (-1: ℤ )^(n+1) = -(-1)^n, rw pow_add, ring, rw t1, 
    have main: (2*(2 * ↑(luc m)):ℤ ) = 2*(-(-1) ^ n * 5 * ↑(fib (m + n)) * ↑(fib n) + (-1) ^ n * ↑(luc (m + n)) * ↑(luc n)),
    { rw mul_add, rw eq_comm, 
    have t2: (2 * (-(-1) ^ n * 5 * ↑(fib (m + n)) * ↑(fib n)) :ℤ ) = ↑ (2 *(fib (m + n)))* (-(-1) ^ n * 5 *  ↑(fib n)), push_cast, ring,
    rw t2, rw fib_luc1,
    have t3: (2 * ((-1) ^ n * ↑(luc (m + n)) * ↑(luc n)) : ℤ ) = ↑(2  * (luc (m + n))) *(-1) ^ n* ↑(luc n), push_cast, ring,
    rw t3, rw fib_luc2,
    suffices goal: (-1: ℤ ) ^ n * ↑(luc m) * ↑(luc n) ^ 2 - 5 * (-1: ℤ ) ^ n * ↑(fib n) ^ 2 * ↑(luc m) = 4 * ↑(luc m), 
    {push_cast, simp, ring, assumption},
    {have:= fib_luc_4 n, rw t1 at this, rw ← this, ring}
    },
    {rw ←  int.mul_div_cancel_left (2 * ↑(luc m)), rw main, rw int.mul_div_cancel_left, linarith, linarith}
end