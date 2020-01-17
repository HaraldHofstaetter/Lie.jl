/*
 * compile with 
 *     gcc -O3 -fopenmp -Wall  bch.c -o bch64
 * or
 *    gcc -O3 -fopenmp -Wall -DUSE_INT128_T bch.c -o bch128
 * for enabling 128 bit integer arithmetics
 *
 */

#include<stdlib.h>
#include<stdint.h>
#include<stdio.h>
#include<assert.h>
#include<time.h>
#include<string.h>
#include<omp.h>

#ifdef USE_INT128_T
typedef __int128_t INTEGER; 
#else
typedef __int64_t INTEGER;
#endif

static size_t K;        /* number of generators */
static size_t N;        /* maximum length of Lyndon words (=maximum order of Lie series expansion) */
static uint8_t **W;     /* W[i] ... nth Lyndon word, ordered primarily by length and secondarily
                           by lexicographical order */
static size_t *p1;      /* standard factorization of W[i] is W[p1[i]]*W[p2[i]] */
static size_t *p2;
static size_t *nn;      /* nn[i] = length of W[i] */
static size_t *ii;      /* W[ii[n-1]] = first Lyndon word of length n; 
                           W[ii[n]-1] = last Lyndon word of length n */
static size_t *LWI;     /* LWI[i] = word index of W[i] */
static size_t *MDI;     /* MDI[i] = multi degree index of W[i] */
static size_t n_lyndon; /* number of Lyndon words of length <=N, n_lyndon = ii[N] */

static INTEGER *FACTORIAL;

static size_t max_lookup_size;
static size_t LUT_LD;   
int *LUT;

int ipow(int base, unsigned int exp)
{
    /* METHOD: see https://stackoverflow.com/questions/101439/the-most-efficient-way-to-implement-an-integer-based-power-function-powint-int
     */
    int result = 1;
    for (;;)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        if (!exp)
            break;
        base *= base;
    }
    return result;
}

INTEGER gcd(INTEGER a, INTEGER b) {
    while (b!=0) {
       INTEGER t = b; 
       b = a%b; 
       a = t; 
    }
    return a>=0 ? a : -a;
}

void moebius_mu(size_t N, int mu[N]) {
    /* INPUT: N
     * OUTPUT: mu[n] = Moebius mu function of n+1, n=0,...,N-1
     * METHOD: see https://mathoverflow.net/questions/99473/calculating-m%C3%B6bius-function
     */
    for (int i=0; i<N; i++) {
        mu[i] = 0;
    }
    mu[0] = 1;
    for (int n=1; n<=N/2; n++) {
        int mu_n = mu[n-1];
        for(int i=2*n-1; i<N; i+=n) {
            mu[i] -= mu_n;
        }
    }
}

void number_of_lyndon_words(uint8_t K, size_t N, size_t nLW[N]) {
    /* INPUT: K ... number of letters
     *        N ... maximum lenght of lyndon words
     * OUTPUT: nLW[n] ... number of lyndon words with K letters of length n+1, n=0,...,N-1
     * METHOD: Witt's formula
     */
    /* unsigned int powK[N+1];
    powK[0] = 1;
    for (int i=1; i<=N; i++) {
        powK[i] = powK[i-1]*K;
    }*/
    
    int mu[N];
    moebius_mu(N, mu);

    for (int n=1; n<=N; n++) {
        int d = 1;
        int h = 0;
        while (d*d < n) {
            div_t d1r = div(n, d);
            if (d1r.rem==0) {
               int d1 = d1r.quot; 
               //h += mu[d-1]*powK[d1]+mu[d1-1]*powK[d];
               h += mu[d-1]*ipow(K, d1)+mu[d1-1]*ipow(K, d);
            }
            d++;
        }
        if (d*d == n) {
            //h += mu[d-1]*powK[d];
            h += mu[d-1]*ipow(K, d);
        }
        nLW[n-1] = h/n;
    }
}

void print_word(size_t n, uint8_t w[]) {        
    for (int j=0; j<n; j++) {
           printf("%i", w[j]);
    }
}

size_t word_index(uint8_t K, uint8_t w[], size_t l, size_t r) {
    size_t x = 0;
    size_t y = 1;
    for (int j=r; j>= (signed) l; j--) { /* CAUTION! comparison between signed and unsigned */
        x += w[j]*y;
        y *= K;
    }
    return x + (y-1)/(K-1) - 1;
}

size_t find_lyndon_word_index(size_t l, size_t r, size_t wi) {
    /* METHOD: binary search
     */
    while (l<=r) {
        size_t m = l + (r-l)/2;
        if (LWI[m]==wi) {
            return m;
        }
        if (LWI[m]<wi) {
            l = m+1;
        }
        else {
            r = m-1;
        }
    }
    fprintf(stderr, "ERROR: Lyndon word index not found: %li\n", wi);
    exit(EXIT_FAILURE);
}

unsigned int binomial(unsigned int n, unsigned int k) {
    /* METHOD: from Julia base library, see
     * https://github.com/JuliaLang/julia/blob/master/base/intfuncs.jl     
     */ 
    if (k < 0 || k > n ) {
        return 0;
    }
    if (k == 0 || k == n) {
        return 1;
    }
    if (k == 1) {
        return n;
    }
    if (k > (n>>1)) {
        k = (n - k);
    }
    uint64_t x = n - k +1;
    uint64_t nn = x;
    nn++;
    uint64_t rr = 2;
    while (rr <= k) {
        x = (x*nn) / rr;  /* TODO: detect possible overflow 
                             (cannot occur with reasonable parameters for BCH) */
        rr++;
        nn++;
    }
    return x;
}

size_t multi_degree_index(uint8_t K, uint8_t w[], size_t l, size_t r) {
    size_t h[K];
    for (int j=0; j<K; j++) {
        h[j] = 0;
    }
    for (int j=l; j<=r; j++) {
        h[w[j]]++;
    }
    size_t index = 0;
    size_t n = 0;
    for (int k=0; k<K; k++) {
        n += h[K-k-1];
        index += binomial(k+n, n-1);
    }
    return index;
    
}

/* The following two functions are for the generation of Lyndon words
 * and their standard factorizations.
 *
 * METHOD: see J. Sawada, F. Ruskey, Generating Lyndon brackets. 
 * An addendum to: Fast algorithms to generate necklaces, unlabeled necklaces 
 * and irreducible polynomials over GF(2), J. Algorithms 46 (2003) 21–26.a
 *
 * See also Algorithm 2.1 from
 * K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms 
 * to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2), 
 * J. Algorithms 37 (2) (2000) 267–282
 */

void genLW(uint8_t K, size_t n, size_t t, size_t p[], 
           uint8_t a[], size_t *wp, size_t split[]) {
    if (t>n) {
        if (p[0]==n) {
            for (int i=0; i<n; i++) {
                W[*wp][i] = a[i+1];
            }
            LWI[*wp] = word_index(K, a, 1, n);
            MDI[*wp] = multi_degree_index(K, a, 1, n);
            if (n>1) {
                size_t m = split[(n-1)*n]; /* split[1,n] */
                size_t wi1 = word_index(K, a, 1, m-1);
                size_t wi2 = word_index(K, a, m, n);
                p1[*wp] = find_lyndon_word_index(0, *wp-1, wi1);
                p2[*wp] = find_lyndon_word_index(0, *wp-1, wi2);
            }
            (*wp)++;
        }
    }
    else {
        size_t q[n];
        for (int i=0; i<n; i++) {
            q[i] = p[i];
        }
        for (int j=a[t-p[0]]; j<K; j++) {
            a[t] = j;
            for (int i=1; i<t; i++) {
                if (a[t]<a[t-p[i-1]]) {
                    p[i-1] = 0;
                }
                if (a[t]>a[t-p[i-1]]) {
                    p[i-1] = t-i+1;
                }
            }
            for (int i=t-1; i>0; i--) {
                if (p[i]==t-i) {
                    split[i+(t-1)*n-1] = i+1;  /* split[i,t] */
                }
                else {
                    split[i+(t-1)*n-1] = split[i+(t-1)*n]; /*split[i, t], split[i+1,t] */
                }
            }
            genLW(K, n, t+1, p, a, wp, split);
            for (int i=0; i<n; i++) {
                p[i] = q[i];
            }
        }
    }
}

void init_lyndon_words(void) {
    size_t nLW[N];
    number_of_lyndon_words(K, N, nLW);
    size_t mem_len = 0;
    n_lyndon = 0;
    for (int n=1; n<=N; n++) {
        n_lyndon += nLW[n-1];
        mem_len += n*nLW[n-1];
    }
    W = malloc(n_lyndon*sizeof(uint8_t *)); 
    p1 = malloc(n_lyndon*sizeof(size_t)); 
    p2 = malloc(n_lyndon*sizeof(size_t)); 
    nn = malloc(n_lyndon*sizeof(size_t)); 
    LWI = malloc(n_lyndon*sizeof(size_t));
    MDI = malloc(n_lyndon*sizeof(size_t));
    ii = malloc((N+1)*sizeof(size_t)); 
    W[0] = malloc(mem_len*sizeof(uint8_t)); 
    ii[0] = 0;
    int m=0;
    for (int n=1; n<=N; n++) {
        ii[n] = ii[n-1] + nLW[n-1];
        for (int k=0; k<nLW[n-1]; k++) {            
            W[m+1] = W[m]+n;
            nn[m] = n;
            m++;
        }
    }
    for (int i=0; i<K; i++) {
        p1[i]=i;
        p2[i]=0;
    }

    uint8_t a[N+1];
    size_t p[N];
    size_t split[N*N];
    size_t wp = 0;
    for (int n=1; n<=N; n++) {
        for (int i=0; i<=n; i++) {
            a[i] = 0;
        }
        for (int i=0; i<n; i++) {
            p[i] = 1;
        }
        for (int i=0; i<n*n; i++) {
            split[i] = 0;
        }
        genLW(K, n, 1, p, a, &wp, split);
    }
    assert(wp==n_lyndon);
}

void free_lyndon_words(void) {
    free(W[0]);
    free(W);
    free(p1);
    free(p2);
    free(nn);
    free(ii);
    free(LWI);
    free(MDI);
}

void init_factorial(void) {
    FACTORIAL = malloc((N+1)*sizeof(INTEGER)); 
    FACTORIAL[0] = 1;
    for (int n=1; n<=N; n++) {
        FACTORIAL[n] = n*FACTORIAL[n-1];
    }
}

void free_factorial(void) {
    free(FACTORIAL);
}

enum expr_type { UNDEFINED, IDENTITY, GENERATOR, SUM, DIFFERENCE, PRODUCT, 
                 COMMUTATOR, TERM, EXPONENTIAL, LOGARITHM };

typedef struct expr {
    enum expr_type type;
    struct expr *arg1;
    struct expr *arg2;
    int num;
    int den;
} expr;

expr* undefined_expr(void) {
    expr *ex = malloc(sizeof(expr));
    ex->type = UNDEFINED;
    ex->arg1 = NULL;
    ex->arg2 = NULL;
    ex->num = 0;
    ex->den = 0;
    return ex;
}

expr* generator(uint8_t n) {
    expr *ex = undefined_expr();
    ex->type = GENERATOR;
    ex->num = n;
    return ex;
}

expr* identity(void) {
    expr *ex = undefined_expr();
    ex->type = IDENTITY;
    return ex;
}

expr* sum(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = SUM;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* difference(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = DIFFERENCE;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* product(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = PRODUCT;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* commutator(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = COMMUTATOR;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* term(int num, int den, expr* arg) {
    expr *ex = undefined_expr();
    ex->type = TERM;
    ex->arg1 = arg;
    ex->num = num;
    ex->den = den;
    return ex;
}

expr* exponential(expr* arg) {
    expr *ex = undefined_expr();
    ex->type = EXPONENTIAL;
    ex->arg1 = arg;
    return ex;
}

expr* logarithm(expr* arg) {
    expr *ex = undefined_expr();
    ex->type = LOGARITHM;
    ex->arg1 = arg;
    return ex;
}

void free_expr(expr* ex) {
    if (ex) {
        free(ex->arg1);
        free(ex->arg2);
        free(ex);
    }
}    

void print_expr(expr* ex) {
    switch(ex->type) {
        case IDENTITY:
            printf("Id");
            break;
        case GENERATOR: 
            printf("%c", 'A'+ex->num);
            break;
        case SUM:
            printf("(");
            print_expr(ex->arg1);
            printf("+");
            print_expr(ex->arg2);
            printf(")");
            break;
        case DIFFERENCE:
            printf("(");
            print_expr(ex->arg1);
            printf("-");
            print_expr(ex->arg2);
            printf(")");
            break;
        case PRODUCT: 
            print_expr(ex->arg1);
            printf("*");
            print_expr(ex->arg2);
            break;
        case COMMUTATOR: 
            printf("[");
            print_expr(ex->arg1);
            printf(",");
            print_expr(ex->arg2);
            printf("]");
            break;
        case TERM: 
            break;
        case EXPONENTIAL:
            printf("exp(");
            print_expr(ex->arg1);
            printf(")");
            break;
        case LOGARITHM: 
            printf("log(");
            print_expr(ex->arg1);
            printf(")");
            break;
        default:
            fprintf(stderr, "ERROR: unknown expr type %i\n", ex->type);
            exit(EXIT_FAILURE);
    }
}

static inline int iszero(INTEGER v[], size_t n) {
    for (int j=0; j<n; j++) {
        if (v[j]!=0) {
            return 0;
        }
    }
    return 1;
}

static inline void check_for_divisibility_by_int(INTEGER p, int q, INTEGER d) {
    if (q*d!=p) {
        int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %i\n", q1);
        exit(EXIT_FAILURE);
    }
}

static inline void check_for_divisibility_by_long_int(INTEGER p, long int q, INTEGER d) {
    if (q*d!=p) {
        long int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %li\n", q1);
        exit(EXIT_FAILURE);
    }
}

static inline void check_for_divisibility_by_INTEGER(INTEGER p, INTEGER q, INTEGER d) {
    if (q*d!=p) {
        long int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %li\n", q1);
        exit(EXIT_FAILURE);
    }
}

void phi(INTEGER y[], size_t n, uint8_t w[], expr* ex, INTEGER v[]) {
    switch (ex->type) {
        case IDENTITY: 
            for (int j=0; j<=n; j++) {
                y[j] = v[j];
            }
            break;
        case GENERATOR: 
            for (int j=0; j<n; j++) {
                if (w[j]==ex->num) {
                    y[j] = v[j+1];
                }
                else {
                    y[j] = 0;
                }
            }
            y[n] = 0;
            break;
        case SUM: { 
            INTEGER y1[n+1];
            INTEGER y2[n+1];
            phi(y1, n, w, ex->arg1, v);
            phi(y2, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] = y1[j] + y2[j];
            }
            } 
            break;
        case DIFFERENCE: {
            INTEGER y1[n+1];
            INTEGER y2[n+1];
            phi(y1, n, w, ex->arg1, v);
            phi(y2, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] = y1[j]-y2[j];
            }
            } 
            break;
        case PRODUCT: 
            if (iszero(v, n+1)) {
                return;
            }
            phi(y, n, w, ex->arg2, v);
            if (iszero(y, n+1)) {
                return;
            }
            phi(y, n, w, ex->arg1, y);
            break;
        //case COMMUTATOR: 
        //    break;
        case TERM: 
            phi(y, n, w, ex->arg1, v);
            int p = ex->num;
            int q = ex->den;
            for (int j=1; j<=n; j++) {
                INTEGER h = y[j]*p;
                INTEGER d = h/q;
                check_for_divisibility_by_int(h, q, d);
                y[j] = d;
            }
            break; 
        case EXPONENTIAL: {
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            }
            for (int k=1; k<=n; k++) {
                phi(z, n, w, ex->arg1, z);
                if (iszero(z, n+1)) {
                   return;
                }
                if (k<=20) {
                    long int f = FACTORIAL[k]; /* fits into int => faster arithmetics */
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_long_int(z[j], f, d);
                        y[j] += d;
                    }
                }
                else {
                    INTEGER f = FACTORIAL[k];
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_INTEGER(z[j], f, d);
                        y[j] += d;
                    }
                }
            }
            }
            break;
        case LOGARITHM: {
            expr* lm1 = difference(ex->arg1, identity());
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            }
            for (int k=1; k<=n; k++) {
                phi(z, n, w, lm1, z);
                if (iszero(z, n+1)) {
                   return;
                }
                int f = (k%2 ? +1 : -1)*k; /* f = (-1)^(k+1)*k */ 
                for (int j=0; j<=n; j++) {
                    INTEGER d = z[j]/f;
                    check_for_divisibility_by_int(z[j], f, d);
                    y[j] += d;
                }
            }
            free(lm1->arg2);
            free(lm1);
            }
            break;
        default:
            fprintf(stderr, "ERROR: unknown expr type %i\n", ex->type);
            exit(EXIT_FAILURE);
    }
}

int coeff_word_in_basis_element(uint8_t w[], size_t l, size_t r, 
           size_t j, size_t H[], size_t W2I[]) { 
    if (l==r) {
        return w[l]==j ? 1 : 0;
    }

    if (r-l+1<=max_lookup_size) {  /* use lookup table */
        return LUT[j + W2I[l + r*N]*LUT_LD];
    }

    if ((H[l+r*N] != MDI[j]) || (W2I[l+r*N] < LWI[j])) {
        return 0;
    }
    if (W2I[l+r*N] == LWI[j]) {
        return 1;
    }

    size_t j1 = p1[j];
    size_t j2 = p2[j];
    size_t m1 = nn[j1];
    size_t m2 = nn[j2];

    int c2 = coeff_word_in_basis_element(w, l+m2, r, j1, H, W2I);
    if (c2!=0) {
        c2 *= coeff_word_in_basis_element(w, l, l+m2-1, j2, H, W2I);
    }

    int c1 = coeff_word_in_basis_element(w, l+m1, r, j2, H, W2I);
    if (c1!=0) {
        c1 *= coeff_word_in_basis_element(w, l, l+m1-1, j1, H, W2I);
    }

    return c1 - c2;
}

void gen_ith_word_of_length_n(size_t i, size_t n, uint8_t w[]) {
    /* METHOD: compute base K expansion of i */
    for (int j=0; j<n; j++) {
        w[j] = 0;
    }
    size_t k=n-1;
    while (i>0) {
        w[k] = i%K;
        i/=K;
        k--;
    }
}

void init_lookup_table(size_t M) {
    LUT_LD = ii[M];                           /* leading dimension */
    size_t LUT_D2 = (ipow(K, M+1)-1)/(K-1)-1; /* other dimension */
    LUT = malloc(LUT_LD*LUT_D2*sizeof(size_t));

    size_t H[N*N];
    size_t W2I[N*N];
    uint8_t w[N];

    for (int n=1; n<=M; n++) {
        size_t i1 = ii[n-1];
        size_t i2 = ii[n]-1;

        max_lookup_size = n-1;
        for (int i=0; i<ipow(K, n); i++) {
            gen_ith_word_of_length_n(i, n, w);

            for (int l=0; l<n; l++) {
                for (int r=l; r<n; r++) {
                    H[l + r*N] = multi_degree_index(K, w, l, r); 
                    W2I[l + r*N] = word_index(K, w, l, r); 
                }
            }

            size_t wi = W2I[0 +(n-1)*N];
            for (int j=i1; j<=i2; j++) {
                int c = coeff_word_in_basis_element(w, 0, n-1, j, H, W2I); 
                if (c!=0) {
                    LUT[j + wi*LUT_LD] = c;
                }
            }
        } 
    }
    max_lookup_size = M;
}

void free_lookup_table(void) {
    free(LUT);
}

static inline size_t get_right_factors(size_t i, size_t J[], size_t kmax) {
    size_t k = 0;
    J[0] = i;
    size_t l = i;
    while ((k<kmax) && (p1[l]==0)) {
        k++;
        l = p2[l];
        J[k] = l;
    }
    return k;
}

void coeffs(expr* ex, INTEGER c[], INTEGER denom, int bch_specific) {
    INTEGER e[N+1];

    /* c[0] needs special handling */
    INTEGER t1[2];
    e[0] = 0;
    e[1] = denom;
    phi(t1, 1, W[0], ex, e);
    c[0] = t1[0];

    /* now the other coeffs */
    for (int j=0; j<N; j++){
        e[j] = 0;
    }
    e[N] = denom;

    size_t i1 = ii[N-1];
    size_t i2 = ii[N]-1;

    size_t h1 = MDI[i1];
    size_t h2 = MDI[i2];

    #pragma omp parallel 
    {
    size_t H[N*N];
    size_t W2I[N*N];
    
    for(int l=0; l<=N*N; l++) {
        H[l] = 0;
        W2I[l] = 0;
    }

    size_t JW[N];
    size_t JB[N];
    INTEGER t[N+1];

    #pragma omp for
    for (int h=h1; h<=h2; h++) {
        size_t j1 = 0;
        for (int i=i1; i<=i2; i++) {
            if (MDI[i]==h) {
                if (bch_specific && !(N%2) && p1[i]!=0) {
                    c[i] = 0;
                    continue;
                }
                if (j1==0) {
                    j1 = i;
                }

                uint8_t *w = W[i];
                phi(t, N, w, ex, e);

                size_t kW = get_right_factors(i, JW, N);
                for (int k=0; k<=kW; k++) {
                    c[JW[k]] = t[k];
                }

                for (int l=0; l<N; l++) {
                    for (int r=l; r<N; r++) {
                        H[l + r*N] = multi_degree_index(K, w, l, r); 
                        W2I[l + r*N] = word_index(K, w, l, r); 
                    }
                }

                for (int j=j1; j<=i-1; j++) {
                    if (MDI[j]==h) {
                        size_t kB = get_right_factors(j, JB, kW);
                        int d = coeff_word_in_basis_element(w, kB, N-1, JB[kB], H, W2I); 
                        if (d!=0) {
                            for (int k=0; k<=kB; k++) {
                                c[JW[k]] -= d*c[JB[k]];
                            }
                        }
                    }
                }
            }
        }
    }
    }
}

void init_bch(uint8_t number_of_generators, size_t order, size_t max_lookup_size) {
    K = number_of_generators;
    N = order;
    init_factorial();
    init_lyndon_words();
    init_lookup_table(max_lookup_size);
}

void free_bch(void) {
    free_factorial();
    free_lyndon_words();
    free_lookup_table();
}

long long int get_arg(int argc, char*argv[], char* varname, 
                      long long int default_value, 
                      long long int min, 
                      long long int max)
{
    for (int k=1; k<argc; k++) {
        char* sep = strchr(argv[k], '=');
        if (sep) {
            *sep ='\0';
            if (strcmp(argv[k], varname)==0) {
                char *endptr;
                long long int value = strtoll(sep+1, &endptr, 10); 
                if ((*endptr != '\0')||(endptr == sep+1)) {
                    fprintf(stderr, "ERROR: expected %s=integer\n", argv[k]);
                    exit(EXIT_FAILURE);
                }
                if (value<min) {
                    fprintf(stderr, "ERROR: expected %s>=%lli, got %lli\n", argv[k], min, value);
                    exit(EXIT_FAILURE);
                }
                if (value>max) {
                    fprintf(stderr, "ERROR: expected %s<=%lli, got %lli\n", argv[k], max, value);
                    exit(EXIT_FAILURE);
                }
                *sep = '=';
                return value;
            }
            *sep = '=';
        }   
    }
    return default_value;
}

void print_basis_element(size_t i) {
    if (i<K) {
        printf("%c", (char) ('A'+i));
    }
    else {
        printf("[");
        print_basis_element(p1[i]);
        printf(",");
        print_basis_element(p2[i]);
        printf("]");
    }
}    

void print_lie_series(INTEGER c[], INTEGER denom) {
    for (int i=0; i<n_lyndon; i++) {
        if (c[i]!=0) {
            INTEGER d = gcd(c[i], denom);
            INTEGER p = c[i]/d;
            INTEGER q = denom/d;
            if (p>0) {
                printf("+");
            }
            printf("%li/%li*", (int64_t) p, (int64_t) q); // TODO: output of __int128_t
            print_basis_element(i);
        }
    }
}

void print_lists(INTEGER c[], INTEGER denom) {
    for (int i=0; i<n_lyndon; i++) {
        INTEGER d = gcd(c[i], denom);
        INTEGER p = c[i]/d;
        INTEGER q = denom/d;
        printf("%10i %3li %10li %10li %20li/%li\n",
                i+1, nn[i], p1[i]+1, p2[i]+1, (int64_t) p, (int64_t) q); 
                // TODO: output of __int128_t
                // NOTE: +1 because for compatibility with Julia version
    }
}

int main(int argc, char*argv[]) {
    /* expression: */
    expr *A = NULL;
    expr *B = NULL;
    expr *C = NULL;
    expr *ex = NULL;
    int bch_specific = 0;
    uint8_t K = 2;

    switch(get_arg(argc, argv, "expression", 0, 0, 3)) {
        case 0:
            K = 2;
            A = generator(0);
            B = generator(1);
            ex = logarithm(product(exponential(A), exponential(B)));
            bch_specific = 1;
            break;
        case 1:
            K = 2;
            A = generator(0);
            B = generator(1);
            ex = logarithm(product(product(exponential(A), exponential(B)), exponential(A)));
            break;
        case 2:
            K = 3;  // !!! SIC !!!
            A = generator(0);
            B = generator(1);
            ex = logarithm(product(exponential(A), exponential(B)));
            break;
            break;
        case 3:
            K = 3;
            A = generator(0);
            B = generator(1);
            C = generator(2);
            ex = logarithm(product(product(exponential(A), exponential(B)), exponential(C)));
            break;
    }

#ifdef USE_INT128_T
    size_t N = get_arg(argc, argv, "N", 5, 1, 32);
#else
    size_t N = get_arg(argc, argv, "N", 5, 1, 16);
#endif 
    size_t M = get_arg(argc, argv, "M", 0, 0, N>16 ? 16 : N);

    struct timespec t0, t1;
    double t;

    clock_gettime(CLOCK_MONOTONIC, &t0);	
    init_bch(K, N, M);
    clock_gettime(CLOCK_MONOTONIC, &t1);	
    t = (t1.tv_sec-t0.tv_sec) + ( (double) (t1.tv_nsec - t0.tv_nsec))*1e-9;
    printf("initialization: time=%g seconds\n", t );

    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));
#ifdef USE_INT128_T
    INTEGER denom = FACTORIAL[N]*4*3*5*7*11*13;
#else
    INTEGER denom = FACTORIAL[N]*4*3*5*7;
#endif 

    clock_gettime(CLOCK_MONOTONIC, &t0);	
    coeffs(ex, c, denom, bch_specific);
    clock_gettime(CLOCK_MONOTONIC, &t1);	
    t = (t1.tv_sec-t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec)*1e-9;
    printf("computation of Lie series: time=%g seconds\n", t);

    /* output result: */
    switch(get_arg(argc, argv, "lists_output", N<=10 ? 0 : 1, 0, 1)) {
        case 0:
            print_expr(ex);
            printf("=");
            print_lie_series(c, denom);
            printf("\n");
            break;
        case 1:
            print_lists(c, denom);
            break;
    }

    free(c);
    free_expr(A);
    free_expr(B);
    free_expr(C);
    free_expr(ex);
    free_bch();

    return EXIT_SUCCESS ;
}
