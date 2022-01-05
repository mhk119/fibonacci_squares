# 144 is the largest square in the Fibonacci Sequence

A formalisation of Cohn's Proof. See [here](https://math.la.asu.edu/~checkman/SquareFibonacci.html).

If you've installed [lean](https://leanprover-community.github.io/get_started.html#regular-install) then type 
```
leanproject get mhk119/fibonacci_squares
```

### Contents of src (refer to [Cohn](https://math.la.asu.edu/~checkman/SquareFibonacci.html))
In addition to the contents below, there are other lemmas formalized in every file that are needed later on in the proofs.
| No. | File               | Contents             |
|-----|--------------------|----------------------|
| 1   | recursions         | preliminaries 1-3    |
| 2   | gcd                | preliminaries 4-5    |
| 3   | divisibility1      | preliminaries 6,7,10 |
| 4   | divisibility2      | preliminaries 11-13  |
| 5   | luc_squares        | theorem 1            |
| 6   | luc_double_squares | theorem 2            |
| 7   | fib_squares        | theorem 3            |
